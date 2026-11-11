/*
 * This file is part of FFmpeg.
 *
 * FFmpeg is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * FFmpeg is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with FFmpeg; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
 */

/**
 * @file
 * Attach CEA-608/708 (A53) closed caption side data, read from a
 * file or FIFO, to the video frame with a given output index.
 *
 * Input records (one per line, '\n' terminated):
 *   MPCC1 <n> <base64 cc_data>
 * where n is the 0-based index of the frame at this filter's output and
 * cc_data is the payload of AV_FRAME_DATA_A53_CC (cc_data triplets).
 *
 * The filter never blocks: the source is polled non-blockingly once per
 * frame. Records for frames that already passed are dropped and counted.
 */

#include "config.h"

#include <errno.h>
#include <fcntl.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#if HAVE_UNISTD_H
#include <unistd.h>
#endif

#include "libavutil/base64.h"
#include "libavutil/file_open.h"
#include "libavutil/mem.h"
#include "libavutil/opt.h"

#include "avfilter.h"
#include "filters.h"
#include "video.h"

#define MAX_CC_BYTES   (31 * 3)  /* cc_count is 5 bits */
#define MAX_LINE       8192
#define READ_CHUNK     16384

typedef struct A53Rec {
    int64_t n;
    int     size;
    uint8_t data[MAX_CC_BYTES];
} A53Rec;

typedef struct A53InjectContext {
    const AVClass *class;
    char    *path;
    int      max_pending;

    int      fd;
    int      is_fifo;
    int      eof;
    int      seen_data;

    uint8_t  line[MAX_LINE];
    int      line_len;
    int      skipping;      /* discarding an over-long line */

    A53Rec  *pending;       /* sorted by n, at most max_pending */
    int      nb_pending;

    int64_t  frame_index;

    int64_t  nb_injected;
    int64_t  nb_late;
    int64_t  nb_overflow;
    int64_t  nb_invalid;
} A53InjectContext;

#define OFFSET(x) offsetof(A53InjectContext, x)
#define FLAGS (AV_OPT_FLAG_FILTERING_PARAM | AV_OPT_FLAG_VIDEO_PARAM)
static const AVOption a53inject_options[] = {
    { "path", "file or FIFO with MPCC1 records", OFFSET(path), AV_OPT_TYPE_STRING, { .str = NULL }, 0, 0, FLAGS },
    { "max_pending", "maximum number of buffered future records", OFFSET(max_pending), AV_OPT_TYPE_INT, { .i64 = 256 }, 1, 65536, FLAGS },
    { NULL }
};

AVFILTER_DEFINE_CLASS(a53inject);

static av_cold int init(AVFilterContext *ctx)
{
    A53InjectContext *s = ctx->priv;
    struct stat st;

    if (!s->path || !*s->path) {
        av_log(ctx, AV_LOG_ERROR, "The path option is required\n");
        return AVERROR(EINVAL);
    }
#ifndef O_NONBLOCK
    av_log(ctx, AV_LOG_ERROR, "Non-blocking reads are not supported on this platform\n");
    return AVERROR(ENOSYS);
#else
    s->fd = avpriv_open(s->path, O_RDONLY | O_NONBLOCK);
    if (s->fd < 0) {
        int err = AVERROR(errno);
        av_log(ctx, AV_LOG_ERROR, "Cannot open '%s': %s\n", s->path, av_err2str(err));
        return err;
    }
    if (fstat(s->fd, &st) == 0)
        s->is_fifo = S_ISFIFO(st.st_mode);
    s->pending = av_calloc(s->max_pending, sizeof(*s->pending));
    if (!s->pending)
        return AVERROR(ENOMEM);
    return 0;
#endif
}

static av_cold void uninit(AVFilterContext *ctx)
{
    A53InjectContext *s = ctx->priv;

    av_log(ctx, AV_LOG_VERBOSE,
           "a53inject: injected=%"PRId64" late_dropped=%"PRId64
           " overflow_dropped=%"PRId64" invalid=%"PRId64" unused_pending=%d\n",
           s->nb_injected, s->nb_late, s->nb_overflow, s->nb_invalid, s->nb_pending);
    if (s->fd >= 0)
        close(s->fd);
    av_freep(&s->pending);
}

/* Insert or merge a record, keeping pending sorted by n. */
static void store_record(AVFilterContext *ctx, int64_t n, const uint8_t *d, int size)
{
    A53InjectContext *s = ctx->priv;
    int i;

    if (n < s->frame_index) {
        s->nb_late++;
        av_log(ctx, AV_LOG_VERBOSE, "late cc record for frame %"PRId64" (at %"PRId64"), dropped\n",
               n, s->frame_index);
        return;
    }
    for (i = s->nb_pending; i > 0 && s->pending[i - 1].n > n; i--)
        ;
    if (i > 0 && s->pending[i - 1].n == n) {
        A53Rec *r = &s->pending[i - 1];
        if (r->size + size > MAX_CC_BYTES) {
            s->nb_invalid++;
            return;
        }
        memcpy(r->data + r->size, d, size);
        r->size += size;
        return;
    }
    if (s->nb_pending == s->max_pending) {
        /* bounded: drop the oldest pending record */
        memmove(s->pending, s->pending + 1, (s->nb_pending - 1) * sizeof(*s->pending));
        s->nb_pending--;
        s->nb_overflow++;
        if (i > 0)
            i--;
    }
    memmove(s->pending + i + 1, s->pending + i, (s->nb_pending - i) * sizeof(*s->pending));
    s->pending[i].n = n;
    s->pending[i].size = size;
    memcpy(s->pending[i].data, d, size);
    s->nb_pending++;
}

static void parse_line(AVFilterContext *ctx, char *line, int len)
{
    A53InjectContext *s = ctx->priv;
    uint8_t buf[MAX_CC_BYTES + 8];
    char *p, *end;
    long long n;
    int size;

    if (len > 0 && line[len - 1] == '\r')
        len--;
    line[len] = '\0';
    if (!len)
        return;
    if (strncmp(line, "MPCC1 ", 6)) {
        s->nb_invalid++;
        return;
    }
    p = line + 6;
    errno = 0;
    n = strtoll(p, &end, 10);
    if (end == p || *end != ' ' || errno || n < 0) {
        s->nb_invalid++;
        return;
    }
    p = end + 1;
    size = av_base64_decode(buf, p, sizeof(buf));
    if (size <= 0 || size > MAX_CC_BYTES || size % 3) {
        s->nb_invalid++;
        return;
    }
    store_record(ctx, n, buf, size);
}

/* One non-blocking read; never waits. */
static void poll_source(AVFilterContext *ctx)
{
    A53InjectContext *s = ctx->priv;
    uint8_t chunk[READ_CHUNK];
    ssize_t r;

    if (s->eof)
        return;
    r = read(s->fd, chunk, sizeof(chunk));
    if (r < 0) {
        if (errno != EAGAIN && errno != EINTR) {
            av_log(ctx, AV_LOG_VERBOSE, "read error, injection stopped\n");
            s->eof = 1;
        }
        return;
    }
    if (r == 0) {
        /* A FIFO without any writer yet also reads 0: only treat EOF as
         * final once data has been seen on a FIFO. */
        if (!s->is_fifo || s->seen_data) {
            av_log(ctx, AV_LOG_VERBOSE, "end of cc source, injection stopped\n");
            s->eof = 1;
        }
        return;
    }
    s->seen_data = 1;
    for (ssize_t i = 0; i < r; i++) {
        uint8_t c = chunk[i];
        if (c == '\n') {
            if (s->skipping)
                s->skipping = 0;
            else
                parse_line(ctx, s->line, s->line_len);
            s->line_len = 0;
        } else if (s->skipping) {
            continue;
        } else if (s->line_len >= MAX_LINE - 1) {
            s->nb_invalid++;
            s->skipping = 1;
            s->line_len = 0;
        } else {
            s->line[s->line_len++] = c;
        }
    }
}

static int filter_frame(AVFilterLink *inlink, AVFrame *frame)
{
    AVFilterContext *ctx = inlink->dst;
    A53InjectContext *s = ctx->priv;
    int i, ret;

    poll_source(ctx);

    /* discard records for frames already passed (cannot happen for
     * records stored after the fact, but earlier-stored ones age out) */
    for (i = 0; i < s->nb_pending && s->pending[i].n < s->frame_index; i++)
        s->nb_late++;
    if (i) {
        memmove(s->pending, s->pending + i, (s->nb_pending - i) * sizeof(*s->pending));
        s->nb_pending -= i;
    }

    if (s->nb_pending && s->pending[0].n == s->frame_index) {
        A53Rec *r = &s->pending[0];
        AVFrameSideData *sd;

        av_frame_remove_side_data(frame, AV_FRAME_DATA_A53_CC);
        sd = av_frame_new_side_data(frame, AV_FRAME_DATA_A53_CC, r->size);
        if (sd) {
            memcpy(sd->data, r->data, r->size);
            s->nb_injected++;
        } else {
            s->nb_invalid++;
        }
        memmove(s->pending, s->pending + 1, (s->nb_pending - 1) * sizeof(*s->pending));
        s->nb_pending--;
    }
    s->frame_index++;

    ret = ff_filter_frame(inlink->dst->outputs[0], frame);
    return ret;
}

static const AVFilterPad a53inject_inputs[] = {
    {
        .name         = "default",
        .type         = AVMEDIA_TYPE_VIDEO,
        .filter_frame = filter_frame,
    },
};

const AVFilter ff_vf_a53inject = {
    .name          = "a53inject",
    .description   = NULL_IF_CONFIG_SMALL("Attach A53 closed caption side data from a file or FIFO to frames by output index."),
    .priv_size     = sizeof(A53InjectContext),
    .priv_class    = &a53inject_class,
    .init          = init,
    .uninit        = uninit,
    FILTER_INPUTS(a53inject_inputs),
    FILTER_OUTPUTS(ff_video_default_filterpad),
    .flags         = AVFILTER_FLAG_METADATA_ONLY,
};
