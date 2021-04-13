/*
 * Copyright (C) 2018 ETH Zurich and University of Bologna
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/*
 * Authors: Germain Haugou, ETH (germain.haugou@iis.ee.ethz.ch)
 */

#include "tinyprintf.h"
#include <stdarg.h>
#include "hal/pulp.h"
#include <stdint.h>

static int errno;
int *__errno() { return &errno; } 

int strcmp(const char *s1, const char *s2)
{
  while (*s1 != '\0' && *s1 == *s2)
    {
      s1++;
      s2++;
    }

  return (*(unsigned char *) s1) - (*(unsigned char *) s2);
}

int strncmp(const char *s1, const char *s2, size_t n)
{
  if (n == 0)
    return 0;

  while (n-- != 0 && *s1 == *s2)
    {
      if (n == 0 || *s1 == '\0')
        break;
      s1++;
      s2++;
    }

  return (*(unsigned char *) s1) - (*(unsigned char *) s2);
}

size_t strlen(const char *str)
{ 
  const char *start = str;

  while (*str)
    str++;
  return str - start;
}

int memcmp(const void *m1, const void *m2, size_t n)
{
  unsigned char *s1 = (unsigned char *) m1;
  unsigned char *s2 = (unsigned char *) m2;

  while (n--)
    {
      if (*s1 != *s2)
        {
          return *s1 - *s2;
        }
      s1++;
      s2++;
    }
  return 0;
}

void *memset(void *m, int c, size_t n)
{
  char *s = (char *)m;
  while (n--)
    *s++ = (char) c;

  return m;
}

void *memcpy(void *dst0, const void *src0, size_t len0)
{
  char *dst = (char *) dst0;
  char *src = (char *) src0;

  void *save = dst0;

  while (len0--)
    {
      *dst++ = *src++;
    }

  return save;
}

static void __rt_putc_stdout(char c)
{
  //*(uint32_t*)(long)(0x1A104000 + (hal_core_id() << 3) + (hal_cluster_id() << 7)) = c;
  *(uint32_t*)(long)(0x1A104000) = c;
  // Poll while microblaze debug module's FIFo is full
  //while (pulp_read8(ARCHI_STDOUT_ADDR + 0x8) & 0x8);
  //*(uint32_t *)(long)(ARCHI_STDOUT_ADDR + STDOUT_PUTC_OFFSET + 0x4) = c;
}

static void tfp_putc(void *data, char c) {
    __rt_putc_stdout(c);
}

int printf(const char *fmt, ...) {

  va_list va;
  va_start(va, fmt);
  tfp_format(NULL, tfp_putc, fmt, va);
  va_end(va);

  return 0;
}

int puts(const char *s) {

  char c;
  do {
    c = *s;
    if (c == 0) {
      tfp_putc(NULL, '\n');
      break;
    }
    tfp_putc(NULL, c);
    s++;
  } while(1);

  return 0;
}

int putchar(int c) {

  tfp_putc(NULL, c);

  return c;
}

