/*
#include <stdio.h>
#include <stdint.h>

extern uintptr_t program(void);

static inline long long unbox_i63(uintptr_t v) { return (long long)(v >> 1); }

int main(void) {
    uintptr_t v = program();
    printf("program ====> %lld\n", unbox_i63(v));
    return 0;
} */

#include <stdio.h>
#include <stdlib.h>
#include "gc_stack.h"

extern value body(struct thread_info *);
extern void print_Coq_Init_Datatypes_nat(value);

int main(int argc, char **argv) {
  struct thread_info *tinfo = make_tinfo();
  value v = body(tinfo);
  print_Coq_Init_Datatypes_nat(v);
  printf("\n");
  return 0;
}
