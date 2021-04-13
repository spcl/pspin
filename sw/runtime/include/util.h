#pragma once

#include <stdio.h>

// #define LOG

#define MIN(a, b) (((a)<(b)) ? (a) : (b))
#define MAX(a, b) (((a)>(b)) ? (a) : (b))

//#define FAST_MIN(x, y) (y ^ ((x ^ y) & -(x < y)))
//#define FAST_MAX(x, y) (x ^ ((x ^ y) & -(x < y)))

#define STRINGIFY(x) #x
#define read_csr(reg, val) asm volatile ("csrr %0, " STRINGIFY(reg) : "=r"(val));
#define write_csr(reg, val) asm volatile ("csrw " STRINGIFY(reg) ", %0" : : "rK" (val) : "memory");
#define clear_csr(reg, mask) asm volatile ("csrc " STRINGIFY(reg) ", %0" : : "rK" (mask) : "memory");
#define read_register(reg, val) asm volatile ("addi %0, " STRINGIFY(reg) ", 0" : "=r"(val));
#define write_register(reg, val) asm volatile ("addi " STRINGIFY(reg) ", %0, 0" : : "r"(val) : "memory");

#define DIV_CEIL(a, b) (((a) + (b) - 1)/(b))

//only for powers of 2!
#define FAST_DIV(a, log2_b) ((a) >> log2_b)
#define FAST_MOD(a, b) ((a) & ((b) - 1))

#define AND(a, b) ((a) & ((b)))

#define TERMINATE {*(volatile unsigned int*) 0x1B200000 = 1;}

/*
#define FAST_MOD2(a, b, c)                          \
{                                                   \
    uint32_t tmp = b-1;                             \
    __asm__ volatile (                              \
        "and %0, %1, %2;"                           \
        : "=r" (c)                                  \
        : "ri" (a)                                  \
        , "ri" (tmp)                                \
    );                                              \
}                
*/

#define LABEL(name) __asm__ __volatile__ (#name ":;" ::: "memory")


#ifdef CHECK_ASSERTS
#define ASSERT(condition)\
if (!(condition)) {\
while (true) {\
    printf("Assertion fail: " #condition " at " __FILE__ ":" "%d\n", __LINE__); \
    *(volatile unsigned int*) 0x1B200000 = 1; \
}}
#else
#define ASSERT(condition)
#endif

#define SPIN_PRINTF(format, ...) printf("%s:%s:%d: " format, __FILE__, __FUNCTION__, __LINE__, ##__VA_ARGS__)

#ifdef LOG
#define DEBUG_PRINT(format, ...) SPIN_PRINTF(format, ##__VA_ARGS__)
#else
#define DEBUG_PRINT(...)
#endif

#ifdef ENABLE_TRACING
#define TRACING_DUMMY_INSTR() __asm__ __volatile__ ("nop")
#else
#define TRACING_DUMMY_INSTR() 
#endif
