// Newlib platform services for the isolated guest. Memory is disjoint from
// Rust allocations. C file reads/process operations refuse with errno.
// stdout/stderr are local diagnostic streams; only Rust commits the journal.
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <stddef.h>
#include <stdint.h>
#include <limits.h>
#include <errno.h>

extern void *l4zk_heap_allocate(size_t);
extern void l4zk_private_write(int, const void *, size_t);
extern void l4zk_fail(void) __attribute__((noreturn));

void *_sbrk(ptrdiff_t increment) {
    static unsigned char *start;
    static size_t used;
    const size_t cap = 128u * 1024u * 1024u;
    if (!start) {
        start = l4zk_heap_allocate(cap);
        if (!start) { errno = ENOMEM; return (void *)-1; }
    }
    if (increment < 0) {
        size_t decrease = (size_t)(-(increment + 1)) + 1;
        if (decrease > used) { errno = ENOMEM; return (void *)-1; }
        void *old = start + used;
        used -= decrease;
        return old;
    }
    if ((size_t)increment > cap - used) { errno = ENOMEM; return (void *)-1; }
    void *old = start + used;
    used += (size_t)increment;
    return old;
}

int _write(int fd, const void *p, size_t n) {
    if (fd != 1 && fd != 2) { errno = EBADF; return -1; }
    if (n > INT_MAX) { errno = EOVERFLOW; return -1; }
    l4zk_private_write(fd, p, n);
    return (int)n;
}
int _read(int fd, void *p, size_t n) {
    (void)fd; (void)p; (void)n; errno = ENOSYS; return -1;
}
int _close(int fd) { (void)fd; errno = ENOSYS; return -1; }
off_t _lseek(int fd, off_t off, int whence) {
    (void)fd; (void)off; (void)whence; errno = ESPIPE; return -1;
}
int _isatty(int fd) { (void)fd; errno = ENOTTY; return 0; }
int _fstat(int fd, struct stat *s) {
    if (fd < 0 || fd > 2) { errno = EBADF; return -1; }
    *s = (struct stat){0};
    s->st_mode = S_IFCHR;
    return 0;
}
int _getpid(void) { errno = ENOSYS; return -1; }
int _kill(int pid, int sig) { (void)pid; (void)sig; errno = ENOSYS; return -1; }
int _gettimeofday(struct timeval *tv, void *tz) {
    (void)tv; (void)tz; errno = ENOSYS; return -1;
}
void _exit(int code) { (void)code; l4zk_fail(); }

/* RV32IM has no hardware atomics. The zkVM has one non-preemptive hart;
 * these ABI operations therefore have their ordinary sequential meaning.
 * They are real read/modify/write operations, not success-returning stubs.
 * Lean's negative reference counts and thunk slots still use these symbols
 * even with LEAN_MULTI_THREAD disabled. */
static uint32_t load_word(volatile void *p) {
    uint32_t value;
    unsigned char *bytes = (unsigned char *)&value;
    volatile unsigned char *source = (volatile unsigned char *)p;
    for (size_t i = 0; i < sizeof(value); ++i) bytes[i] = source[i];
    return value;
}
static void store_word(volatile void *p, uint32_t value) {
    const unsigned char *bytes = (const unsigned char *)&value;
    volatile unsigned char *dest = (volatile unsigned char *)p;
    for (size_t i = 0; i < sizeof(value); ++i) dest[i] = bytes[i];
}
uint32_t __atomic_fetch_add_4(volatile void *p, uint32_t value, int order) {
    (void)order;
    uint32_t old = load_word(p);
    store_word(p, old + value);
    return old;
}
uint32_t __atomic_fetch_sub_4(volatile void *p, uint32_t value, int order) {
    (void)order;
    uint32_t old = load_word(p);
    store_word(p, old - value);
    return old;
}
uint32_t __atomic_exchange_4(volatile void *p, uint32_t value, int order) {
    (void)order;
    uint32_t old = load_word(p);
    store_word(p, value);
    return old;
}
