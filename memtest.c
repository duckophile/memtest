/*
 *
 * A user-space memory test.
 *
 * Compile with -lrt
 *
 * Written by Mark Mason.
 *
 * See the command-line help for an explanation of what it does and why.
 *
 */

/*
 * TODO:  I need to reap my children to get rid of the zombies!
 */

#define _GNU_SOURCE
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <ctype.h>
#include <sched.h>
#include <sys/mman.h>
#include <time.h>
#include <signal.h>
#include <sys/types.h>
#include <sys/wait.h>

#define HEX__(n) 0x##n##LU
#define B8__(x)								\
          ((x & 0x0000000FLU) ? 1   : 0)				\
        + ((x & 0x000000F0LU) ? 2   : 0)				\
        + ((x & 0x00000F00LU) ? 4   : 0)				\
        + ((x & 0x0000F000LU) ? 8   : 0)				\
        + ((x & 0x000F0000LU) ? 16  : 0)				\
        + ((x & 0x00F00000LU) ? 32  : 0)				\
        + ((x & 0x0F000000LU) ? 64  : 0)				\
        + ((x & 0xF0000000LU) ? 128 : 0)
#define B8(d) ((unsigned char)B8__(HEX__(d)))
#define B16(dmsb,dlsb) (((uint32_t)B8(dmsb) << 8) + (uint32_t)B8(dlsb))
#define B32(dmsb,db2,db3,dlsb)                                   \
          (((uint32_t)B8(dmsb) << 24)                       \
         + ((uint32_t)B8(db2)  << 16)                       \
         + ((uint32_t)B8(db3)  << 8)                        \
         + ((uint32_t)B8(dlsb) << 0))

#define NUM_MEM_CHUNKS	8
#define MEM_CHUNK_SIZE (1024 * 1024 * sizeof(uint32_t))

#define PATTERN_FILL	0
#define PATTERN_VERIFY	1

#define FILL_LINEAR	0
#define FILL_RANDOM	1

#define MAX_SKIP 32
/* Increase this for longer and more comprehensive tests. */
int skip_iterations = MAX_SKIP;

#define MAX_ERRORS 10
/* Show at most this many errors in any test. */
int max_errors = MAX_ERRORS;

int verbose_flag = 0;	/* Give verbose output. */
int do_fork = 0;	/* Do fork test. */
int do_random = 0;	/* Do pseudo-random filling. */

int run_fork_test = 0;
int run_linear_pattern_test = 0;
int run_pseudo_random_pattern_test = 0;

#define TIME_FORMAT_STRING "%2dm %2d.%03ds"

static void
sigchld_handler(int pid)
{
    int x;

    (void)pid;
    wait(&x);
}

/*
 * Allocate some memory.  It allocates a multiple of a page size, and
 * the memory is always page aligned.  It exits on failure.
 */
static void *
my_malloc(int size)
{
        void *ptr;
        static int pagesize = 0;
        static int pagemask;

        if (pagesize == 0) {
                pagesize = getpagesize();
                pagemask = pagesize - 1;
        }

        /* Round up to page boundary. */
        size = (size + pagemask) & ~pagemask;

        ptr = mmap(NULL, size, PROT_READ | PROT_WRITE,
                   MAP_ANONYMOUS | MAP_PRIVATE | MAP_POPULATE, -1, 0);

        if (ptr == MAP_FAILED) {
                perror("Couldn't allocate memory");
                ptr = NULL;
                exit(-1);
        }

        return ptr;
}

void
my_free(void *ptr, int size)
{
        static int pagesize = 0;
        static int pagemask;

        if (pagesize == 0) {
                pagesize = getpagesize();
                pagemask = pagesize - 1;
        }

        /* Round up to page boundary. */
        size = (size + pagemask) & ~pagemask;

        if (munmap(ptr, size) == -1) {
                perror("munmap");
                exit(-1);
        }
}

/*
 * Convert an uint32_t to a binary string.
 */
static char *
binstring(uint32_t l)
{
        int x;
        static char s[34];

        for (x = 31;x >= 0;x--)
        {
                if (l & (1 << x))
                        s[31 - x] = '1';
                else
                        s[31 - x] = '0';
        }
        s[32] = 0;

        return s;
}

static struct timespec *
timestamp(clockid_t clock, struct timespec *t)
{
        clock_gettime(clock, t);

        return t;
}

static struct timespec *
time_since(struct timespec *start, clockid_t clock, uint32_t *minutes,
           uint32_t *seconds, uint32_t *msec)
{
        static struct timespec elapsed_time;

        clock_gettime(clock, &elapsed_time);

        elapsed_time.tv_sec -= start->tv_sec;

        elapsed_time.tv_nsec += 1000000000L;	/* Add a second of nsecs. */
        elapsed_time.tv_nsec -= start->tv_nsec;
        if (elapsed_time.tv_nsec < 1000000000)
                elapsed_time.tv_sec--;
        else
                elapsed_time.tv_nsec -= 1000000000;

        if (minutes)
                *minutes = elapsed_time.tv_sec / 60;
        if (seconds)
                *seconds = elapsed_time.tv_sec % 60;
        if (msec) {
                *msec = (elapsed_time.tv_nsec / 1000000);
                if (elapsed_time.tv_nsec > ((*msec * 1000000) + 500000))
                        (*msec)++;
        }

        return &elapsed_time;
}

/****************************************************************
 *
 * Pattern tests.
 *
 * This fills a chunk of memory with a variety of 32 bit patterns,
 * copies the buffer to another buffer some number of times, then
 * verifies the result at the end.
 *
 * The patterns are written to memory, alternating with the inverted
 * pattern.  The same pattern is run N (256) times.  For each run, the
 * pattern is only inverted every N words.
 *
 * The variably inverting patterns are intended to generate a wide
 * variety of bit patterns on the data lines, hoping to induce as much
 * cross talk and ground bounce as possible.
 *
 ****************************************************************/
static uint32_t patterns[] = {
        B32(10101010,10101010,10101010,10101010),
        B32(11001100,11001100,11001100,11001100),
        B32(11100011,10001110,00111000,11100011),
        B32(11110000,11110000,11110000,11110000),
        B32(11111000,00111110,00001111,10000011),
        B32(11111100,00001111,11000000,11111100),
        B32(11111110,00000011,11111000,00001111),
        B32(11111111,00000000,11111111,00000000)
};
#define N_PATTERNS 8

static int
pattern_fill_verify_lfsr(uint32_t *ptr, uint32_t len, int skip,
                         int pattern, int verify)
{
        uint x;
        uint32_t idx = 1;
        uint patval = patterns[pattern];
        uint pattern_read;
        int skipped = 0;
        int error_count = 0;
        uint32_t * volatile l = ptr;
        int bit;

        if (verbose_flag)
                printf("Pattern %s %s  pattern #%d, skip %3d\n",
                       do_random ? "pseudo-random" : "linear",
                       verify ? "verify" : "fill  ", pattern, skip);

        if (do_random) {
                idx = 1;	/* LFSR can't handle 0. */
                len--;
        } else {
                idx = 0;
        }

        for (x = 0;x < len;x++) {
                /* every 'skip' words we invert the pattern. */
                if (skipped == skip) {
                        patval = ~patval;
                        skipped = 0;
                } else
                        skipped++;
                if (verify == PATTERN_VERIFY) {
                        pattern_read = l[idx];
                        if (pattern_read != patval) {
                                if (error_count < max_errors)
                                        printf("ERROR: Pattern %d, skip %3d, word %7u, virtual "
                                               "address %p - wanted 0x%08X, got 0x%08X",
                                               pattern, skip, x, (void *)&l[idx], patval, pattern_read);
                                error_count++;
                                pattern_read = l[idx];
                                if (error_count < max_errors) {
                                        if (pattern_read == patval)
                                                printf(" (but a second read worked)");
                                        printf("\n");
                                }
                        }
                } else {
                        l[idx] = patval;
                }
                if (do_random) {
                        bit = idx & 1;
                        idx >>= 1;
                        if (bit)
                                idx ^= 0x90000;	/* Only works for 20 bits (1M). */
                } else {
                        idx++;
                }
        }

        if (error_count)
                printf("Got %d errors\n", error_count);

        return error_count;
}

static uint32_t *mem_chunks[NUM_MEM_CHUNKS];

static void
allocate_chunks(void)
{
        int x;

        for (x = 0;x < NUM_MEM_CHUNKS;x++) {
                if (mem_chunks[x] == NULL) {
                        mem_chunks[x] = my_malloc(MEM_CHUNK_SIZE);
                }
        }
}

static void
free_chunks(void)
{
        int x;

        for (x = 0;x < NUM_MEM_CHUNKS;x++) {
                if (mem_chunks[x] != NULL) {
                        my_free(mem_chunks[x], MEM_CHUNK_SIZE);
                        mem_chunks[x] = NULL;
                }
        }
}

/*
 * Run a pattern test.
 *
 * This covers linear & pseudo-random fill, as well as the fork test.
 */
static int
pattern_test(void)
{
        struct timespec realtime, cputime;
        uint32_t cpu_min, cpu_sec, cpu_msec;
        uint real_min, real_sec, real_msec;
        int pattern;
        int use_pattern;
        int skip = 0;
        int y;
        int pid = -1;

        printf("%d skip iterations:\n", skip_iterations);

        timestamp(CLOCK_MONOTONIC, &realtime);
        timestamp(CLOCK_PROCESS_CPUTIME_ID, &cputime);

        /*
         * For fork test, allocate the buffers up front, so the child
         * has to fault in the copy-on-write pages.
         */
        if (do_fork) {
                allocate_chunks();
        }

        for (skip = 0; skip < skip_iterations;skip++) {
                if (!verbose_flag) {
                        printf("%d ", skip);
                        fflush(stdout);
                }

                for (pattern = 0;pattern < N_PATTERNS;pattern++) {
                        if (do_fork) {
                                pid = fork();
                        }
                        if (pid == 0) {
                                /*
                                 * If I forked then I'm the child.
                                 * The parent and the child process do
                                 * not run the same pattern at the
                                 * same time, so the child gets a
                                 * different pattern.
                                 */
                                use_pattern = N_PATTERNS - pattern;
                        } else {
                                /*
                                 * I'm the parent, or I didn't fork.
                                 */
                                use_pattern = pattern;
                        }

                        /* Allocate the first chunk. */
                        if (mem_chunks[0] == NULL) {
                                mem_chunks[0] = my_malloc(MEM_CHUNK_SIZE);
                                if (mem_chunks[0] == NULL) {
                                        perror("malloc");
                                        exit(-1);
                                }
                        }

                        /* Fill the first chunk. */
                        pattern_fill_verify_lfsr(mem_chunks[0], MEM_CHUNK_SIZE / 4,
                                            skip, use_pattern, PATTERN_FILL);

                        /*
                         * Allocate new chunks, copy into them, and
                         * free the previous chunk.
                         */
                        for (y = 1;y < NUM_MEM_CHUNKS;y++) {
                                if (mem_chunks[y] == NULL) {
                                        mem_chunks[y] = my_malloc(MEM_CHUNK_SIZE);
                                        if (mem_chunks[y] == NULL) {
                                                perror("malloc");
                                                exit(-1);
                                        }
                                }
                                memcpy(mem_chunks[y], mem_chunks[y - 1], MEM_CHUNK_SIZE);
                                /*
                                 * Randomly free, trying to scramble
                                 * the memory pool.
                                 */
                                if (!do_fork && rand() % 2) {
                                        my_free(mem_chunks[y - 1], MEM_CHUNK_SIZE);
                                        mem_chunks[y - 1] = NULL;
                                }
                        }

                        /* Verify the last pattern. */
                        pattern_fill_verify_lfsr(mem_chunks[y - 1],
                                            MEM_CHUNK_SIZE / 4, skip,
                                            use_pattern, PATTERN_VERIFY);

                        /* And free any memory that's left. */
                        if (!do_fork) {
                                for (y = 0;y < NUM_MEM_CHUNKS;y++) {
                                        if (mem_chunks[y]) {
                                                my_free(mem_chunks[y], MEM_CHUNK_SIZE);
                                                mem_chunks[y] = NULL;
                                        }
                                }
                        }

                        if (do_fork) {
                                if (pid == 0) {
                                        /*
                                         * We're the child, so exit
                                         * and let the exit free the
                                         * memory.
                                         */
                                        exit(0);
                                }
                        }
                }
        }

        if (!verbose_flag)
                printf("\n");

        /*
         * Free the chunks, if there are any left.
         */
        free_chunks();

        time_since(&realtime, CLOCK_MONOTONIC,
                   &real_min, &real_sec, &real_msec);
        time_since(&cputime, CLOCK_PROCESS_CPUTIME_ID,
                   &cpu_min, &cpu_sec, &cpu_msec);

        printf("Time for this test: Elapsed: " TIME_FORMAT_STRING "  ",
               real_min, real_sec, real_msec);
        printf("CPU: " TIME_FORMAT_STRING "\n",
               cpu_min, cpu_sec, cpu_msec);

        return 0;
}

static void
usage(void)
{
        int x;

        printf("Usage:  memtest [-v] [<number>] [-h]\n"
               "        -L        Run linear fill pattern test.\n"
               "        -R        Run random fill pattern test.\n"
               "        -F        Run fork test.\n"
               "        -e <n>    Show at most <n> errors for any test (default is  %d).\n"
               "        -r <n>    Repeat all tests <n> time (0 for infinite).\n"
               "        -s <n>    Set skip iterations (default is %d).\n"
               "        -v        Verbose output.\n"
               "        <number>  Set CPU affinity to specified CPU.\n"
               "        -h        This help.\n"
               "Use \"-h -v\" for an explanation of tests.\n", MAX_ERRORS, MAX_SKIP);
        printf("\n");

        if (!verbose_flag)
                exit(0);

        printf("This is a memory test suite that attempts to stress the memory timings,\n"
               "crosstalk and ground bounce on the circuit board, as well as the\n"
               "Linux virtual memory system.\n");
        printf("\n");

        printf("The first test, a varying pattern test, fills a chunk of memory with a\n"
               "variety of 32 bit patterns, copies the buffer to another buffer some\n"
               "number of times, then verifies the result at the end.\n");
        printf("\n");

        printf("The patterns are written to memory, alternating with the logical\n"
               "inversion of that pattern. The test is run N times, where N is the skip\n"
               "iterations.  For each run, the pattern is only inverted every N words.\n"
               "IE, to use a one bit example, the pattern written to consecutive words of\n"
               "memory for the first run would be 1,0,1,0,1,0 etc.  The second time it\n"
               "would be 1,1,0,0,1,1,0,0, the third time it would be 1,1,1,0,0,0,1,1,\n"
               "and so on.\n");
        printf("\n");

        printf("The variably inverting patterns are intended to generate a wide\n"
               "variety of bit patterns on the data lines, hoping to induce as much\n"
               "cross talk and ground bounce as possible.\n");
        printf("\n");

        printf("The second test, the pseudo-random test, is identical to the first,\n"
               "except the words are written to memory in a pseudo-random order.  The\n"
               "pseudo random order is generated by a 20 bit linear feedback shift\n"
               "register, which guarantees that all 1M word addresses (except 0) are\n"
               "written exactly once.  This test should take longer than the first,\n"
               "since it makes poor use of the caches.");
        printf("\n");

        printf("The third test, the fork test, is identical to the first, except that\n"
               "each test is forked into two processes, both of which run the same\n"
               "test with a different pattern.  The parent process allocates the test\n"
               "buffers, which are inherited by the child as copy-on-write pages, so\n"
               "they're faulted and mapped in as their touched.  This is intended to\n"
               "exercise the OS virtual memory system.\n");
        printf("\n");

        printf("There are %d patterns:\n", N_PATTERNS);
        for (x = 0;x < N_PATTERNS;x++)
                printf("        %s  0x%08X\n", binstring(patterns[x]), patterns[x]);
        printf("\n");
        printf("The chunks of memory are %d (0x%08X) bytes, and are copied %d times.\n",
               (int)MEM_CHUNK_SIZE, (int)MEM_CHUNK_SIZE, NUM_MEM_CHUNKS);
        printf("\n");

        printf("Unfortunately it is not possible to give the physical address when a\n"
               "a failure occurs without using memory allocation more complex than\n"
               "malloc.  But, the physical address has the same page alignment as\n"
               "given virtual address, so the bottom 12 bits will be the same.\n");
        printf("\n");

        exit(0);
}

int
cpu_set_affinity(int cpu)
{
        cpu_set_t new_mask;
        cpu_set_t cur_mask;
        unsigned int len = sizeof(new_mask);

        CPU_ZERO(&new_mask);
        CPU_SET(cpu, &new_mask);

        if (sched_getaffinity(0, len, &cur_mask) < 0) {
                perror("sched_getaffinity");
                return -1;
        }

#ifdef CPU_EQUAL
        if (!CPU_EQUAL(&cur_mask, &new_mask)){
#endif
                printf("Setting affinity to CPU %d\n", cpu);
                if (sched_setaffinity(0, len, &new_mask) < 0) {
                        perror("sched_setaffinity");
                        return -1;
                }
#ifdef CPU_EQUAL
        } else {
                printf("Affinity already set to CPU %d\n", cpu);
        }
#endif
        return 0;
}

void
run_all_tests(void)
{
        struct timespec realtime, cputime;
        uint32_t cpu_min, cpu_sec, cpu_msec;
        uint32_t real_min, real_sec, real_msec;

        /*
         * I'd like to use CLOCK_MONOTONIC_RAW, but it's not supported
         * in our tool chain.
         */
        timestamp(CLOCK_MONOTONIC, &realtime);
        timestamp(CLOCK_PROCESS_CPUTIME_ID, &cputime);

        if (run_linear_pattern_test) {
                printf("\n-----> Running pattern test, linear fill...\n\n");
                do_random = 0;
                do_fork = 0;
                pattern_test();
        }

        if (run_pseudo_random_pattern_test) {
                printf("\n-----> Running pattern test, pseudo-random fill...\n\n");
                do_random = 1;
                do_fork = 0;
                pattern_test();
        }

        if (run_fork_test) {
                printf("\n-----> Running fork test...\n\n");
                do_random = 0;
                do_fork = 1;
                pattern_test();
        }

        time_since(&realtime, CLOCK_MONOTONIC,
                   &real_min, &real_sec, &real_msec);
        time_since(&cputime, CLOCK_PROCESS_CPUTIME_ID,
                   &cpu_min, &cpu_sec, &cpu_msec);

        printf("\n");
        printf("Total time for all tests: Elapsed: " TIME_FORMAT_STRING "  ",
               real_min, real_sec, real_msec);
        printf("CPU: " TIME_FORMAT_STRING "\n",
               cpu_min, cpu_sec, cpu_msec);
        printf("\n");

        return;
}

int
main(int argc, char *argv[])
{
        int cpu;
        int x;
        int do_help = 0;
        int repeat_count = 1;


        for (x = 1; argv[x] != NULL;x++) {
                if (!strcmp(argv[x], "-h")) {
                        do_help = 1;
                } else if (!strcmp(argv[x], "-c")) {
                        if (argv[x + 1] == NULL) {
                                printf("Please specify a CPU number.\n");
                                exit(0);
                        } else {
                                cpu = atoi(argv[x + 1]);
                                if (cpu_set_affinity(cpu))
                                    exit(0);
                                x++;
                        }
                } else if (!strcmp(argv[x], "-e")) {
                        if (argv[x + 1] == NULL) {
                                printf("Please specify how many errors you want to see.\n");
                                exit(0);
                        } else {
                                max_errors = atoi(argv[x + 1]);
                                x++;
                        }
                } else if (!strcmp(argv[x], "-r")) {
                        if (argv[x + 1] == NULL) {
                                printf("Please specify how many times you want to repeat the tests\n");
                                exit(0);
                        } else {
                                repeat_count = atoi(argv[x + 1]);
                                x++;
                        }
                } else if (!strcmp(argv[x], "-v")) {
                        verbose_flag++;
                } else if (!strcmp(argv[x], "-s")) {
                        if (argv[x + 1] == NULL) {
                                printf("Please specify how many skip iterations you'd like.\n");
                                exit(0);
                        } else {
                                skip_iterations = atoi(argv[x + 1]);
                                x++;
                        }
                } else if (!strcmp(argv[x], "-F")) {
                        run_fork_test = 1;
                } else if (!strcmp(argv[x], "-L")) {
                        run_linear_pattern_test = 1;
                } else if (!strcmp(argv[x], "-R")) {
                        run_pseudo_random_pattern_test = 1;
                } else {
                        printf("Uknown option \"%s\"\n", argv[x]);
                        do_help = 1;
                }

        }

        if (do_help)
                usage();

         signal(SIGCHLD, sigchld_handler);

        /*
         * If no tests were selected then run all of them.
         */
        if (!run_fork_test &&
            !run_linear_pattern_test &&
            !run_pseudo_random_pattern_test) {
                run_fork_test = 1;
                run_linear_pattern_test = 1;
                run_pseudo_random_pattern_test = 1;
        }

        srand(314);

        x = 1;
        do {
                printf("----------------------------------------------------------------\n");
                run_all_tests();
                printf("----------------------------------------------------------------\n");
        } while (x++ != repeat_count);

        return 0;
}
