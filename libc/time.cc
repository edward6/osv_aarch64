/*
 * Copyright (C) 2013 Cloudius Systems, Ltd.
 *
 * This work is open source software, licensed under the terms of the
 * BSD license as described in the LICENSE file in the top-level directory.
 */

#include <api/utime.h>
#include <sys/time.h>
#include <time.h>
#include <unistd.h>
#include <osv/stubbing.hh>
#include "libc.hh"
#include <osv/clock.hh>
#include <osv/sched.hh>

static u64 convert(const timespec& ts)
{
    return ts.tv_sec * 1000000000 + ts.tv_nsec;
}

extern "C"
int gettimeofday(struct timeval* tv, struct timezone* tz)
{
    if (!tv) {
        return 0;
    }
    using namespace std::chrono;
    auto d = osv::clock::wall::now().time_since_epoch();
    tv->tv_sec = duration_cast<seconds>(d).count();
    tv->tv_usec = duration_cast<microseconds>(d).count() % 1000000;
    return 0;
}

int nanosleep(const struct timespec* req, struct timespec* rem)
{
    if (!req || req->tv_nsec < 0 || req->tv_nsec >= 1000000000L || req->tv_sec < 0)
        return libc_error(EINVAL);

    sched::thread::sleep(std::chrono::nanoseconds(convert(*req)));
    return 0;
}

int usleep(useconds_t usec)
{
    sched::thread::sleep(std::chrono::microseconds(usec));
    return 0;
}

// Convenient inline function for converting std::chrono::duration,
// of a clock with any period, into the classic Posix "struct timespec":
template <class Rep, class Period>
static inline void fill_ts(std::chrono::duration<Rep, Period> d, timespec *ts)
{
    using namespace std::chrono;
    ts->tv_sec = duration_cast<seconds>(d).count();
    ts->tv_nsec = duration_cast<nanoseconds>(d).count() % 1000000000;
}

int clock_gettime(clockid_t clk_id, struct timespec* ts)
{
    if (!ts)
        return libc_error(EINVAL);

    switch (clk_id) {
    case CLOCK_MONOTONIC:
        fill_ts(osv::clock::uptime::now().time_since_epoch(), ts);
        break;
    case CLOCK_REALTIME:
    case CLOCK_REALTIME_COARSE:
        fill_ts(osv::clock::wall::now().time_since_epoch(), ts);
        break;
    case CLOCK_PROCESS_CPUTIME_ID:
        fill_ts(sched::process_cputime(), ts);
        break;
    case CLOCK_THREAD_CPUTIME_ID:
        fill_ts(sched::thread::current()->thread_clock(), ts);
        break;

    default:
        if (clk_id < _OSV_CLOCK_SLOTS) {
            return libc_error(EINVAL);
        } else {
            auto thread = sched::thread::find_by_id(clk_id - _OSV_CLOCK_SLOTS);
            fill_ts(thread->thread_clock(), ts);
        }
    }

    return 0;
}

extern "C"
int __clock_gettime(clockid_t clk_id, struct timespec* ts) __attribute__((alias("clock_gettime")));

int clock_getres(clockid_t clk_id, struct timespec* ts)
{
    switch (clk_id) {
    case CLOCK_REALTIME:
    case CLOCK_REALTIME_COARSE:
    case CLOCK_PROCESS_CPUTIME_ID:
    case CLOCK_THREAD_CPUTIME_ID:
    case CLOCK_MONOTONIC:
        break;
    default:
        if (clk_id < _OSV_CLOCK_SLOTS) {
            return libc_error(EINVAL);
        }
    }

    if (ts) {
        ts->tv_sec = 0;
        ts->tv_nsec = 1;
    }
    return 0;
}

int clock_getcpuclockid(pid_t pid, clockid_t* clock_id)
{
    return CLOCK_PROCESS_CPUTIME_ID;
}

clock_t clock(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &ts);
    return ts.tv_sec * 1000000000L + ts.tv_nsec;
}

int clock_nanosleep(clockid_t clock_id, int flags,
                    const struct timespec *request,
                    struct timespec *remain)
{
    /* XXX we are implementing really only CLOCK_MONOTONIC, */
    /* and we don't support remain, due to signals. */
    WARN_STUBBED();
    if (!request) {
        return libc_error(EINVAL);
    }
    if (remain) {
        assert(0); /* XXX not supported yet */
    }
    if (clock_id != CLOCK_MONOTONIC) {
        assert(0); /* XXX not supported yet */
    }

    switch (flags) {
    case 0:
        return nanosleep(request, NULL);
    case TIMER_ABSTIME: {
        struct timespec ts;
        if (clock_gettime(clock_id, &ts) != 0) {
            return -1;
        }
        if (timespeccmp(request, &ts, <=)) {
            return 0;
        }
        sched::thread::sleep(osv::clock::uptime::time_point(
                                 osv::clock::uptime::duration(convert(*request))));
        return 0;
    }
    default:
        return libc_error(EINVAL);
    }
}
