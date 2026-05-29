#ifndef CERTICOQ_BENCHMARKS_FIBONACCI_FIB_PROGRAM_C
#define CERTICOQ_BENCHMARKS_FIBONACCI_FIB_PROGRAM_C
#include <gc_stack.h>
#include <prim_string.h>
#include <prim_floats.h>
#include <prim_int63.h>
#include <coq_c_ffi.h>
#include "CertiCoq.Benchmarks.Fibonacci.fib.program.h"
extern struct thread_info *make_tinfo(void);
extern value f_case_known_123(struct thread_info *, value, value);
extern value succ_known_122(struct thread_info *, value);
extern value of_succ_nat_known_121(struct thread_info *, value);
extern value f_case_known_120(struct thread_info *, value);
extern value fib_loop_nat_uncurried_uncurried_known_119(struct thread_info *, value, value, value);
extern value iter_uncurried_known_118(struct thread_info *, value, value);
extern value f_case_known_117(struct thread_info *, value);
extern value f_case_known_116(struct thread_info *, value);
extern value to_Z_rec_uncurried_known_115(struct thread_info *, value, value);
extern value CoqdZArithdBinIntDefdZdsucc_double_wrapper_114(struct thread_info *, value, value);
extern value pred_double_known_113(struct thread_info *, value);
extern value CoqdZArithdBinIntDefdZdsucc_double_known_112(struct thread_info *, value);
extern value CoqdZArithdBinIntDefdZddouble_wrapper_111(struct thread_info *, value, value);
extern value CoqdZArithdBinIntDefdZddouble_known_110(struct thread_info *, value);
extern value add_uncurried_known_109(struct thread_info *, value, value);
extern value of_pos_rec_uncurried_known_108(struct thread_info *, value, value);
extern value body(struct thread_info *);
value f_case_known_123(struct thread_info *, value, value);
value succ_known_122(struct thread_info *, value);
value of_succ_nat_known_121(struct thread_info *, value);
value f_case_known_120(struct thread_info *, value);
value fib_loop_nat_uncurried_uncurried_known_119(struct thread_info *, value, value, value);
value iter_uncurried_known_118(struct thread_info *, value, value);
value f_case_known_117(struct thread_info *, value);
value f_case_known_116(struct thread_info *, value);
value to_Z_rec_uncurried_known_115(struct thread_info *, value, value);
value CoqdZArithdBinIntDefdZdsucc_double_wrapper_114(struct thread_info *, value, value);
value pred_double_known_113(struct thread_info *, value);
value CoqdZArithdBinIntDefdZdsucc_double_known_112(struct thread_info *, value);
value CoqdZArithdBinIntDefdZddouble_wrapper_111(struct thread_info *, value, value);
value CoqdZArithdBinIntDefdZddouble_known_110(struct thread_info *, value);
value add_uncurried_known_109(struct thread_info *, value, value);
value of_pos_rec_uncurried_known_108(struct thread_info *, value, value);
value body(struct thread_info *);
unsigned long long const body_info_356[2] = { 126LL, 0LL, };

unsigned long long const of_pos_rec_uncurried_known_info_355[4] = { 0LL, 2LL,
  0LL, 1LL, };

unsigned long long const add_uncurried_known_info_354[4] = { 0LL, 2LL, 0LL,
  1LL, };

unsigned long long const CoqdZArithdBinIntDefdZddouble_known_info_353[3] = {
  4LL, 1LL, 0LL, };

unsigned long long const CoqdZArithdBinIntDefdZddouble_wrapper_info_352[4] = {
  0LL, 2LL, 0LL, 1LL, };

unsigned long long const CoqdZArithdBinIntDefdZdsucc_double_known_info_351[3] = {
  4LL, 1LL, 0LL, };

unsigned long long const pred_double_known_info_350[3] = { 4LL, 1LL, 0LL, };

unsigned long long const CoqdZArithdBinIntDefdZdsucc_double_wrapper_info_349[4] = {
  0LL, 2LL, 0LL, 1LL, };

unsigned long long const to_Z_rec_uncurried_known_info_348[4] = { 0LL, 2LL,
  0LL, 1LL, };

unsigned long long const f_case_known_info_347[3] = { 3LL, 1LL, 0LL, };

unsigned long long const f_case_known_info_346[3] = { 2LL, 1LL, 0LL, };

unsigned long long const iter_uncurried_known_info_345[4] = { 0LL, 2LL, 0LL,
  1LL, };

unsigned long long const fib_loop_nat_uncurried_uncurried_known_info_344[5] = {
  0LL, 3LL, 0LL, 1LL, 2LL, };

unsigned long long const f_case_known_info_343[3] = { 0LL, 1LL, 0LL, };

unsigned long long const of_succ_nat_known_info_342[3] = { 0LL, 1LL, 0LL, };

unsigned long long const succ_known_info_341[3] = { 2LL, 1LL, 0LL, };

unsigned long long const f_case_known_info_340[4] = { 0LL, 2LL, 0LL, 1LL, };

value f_case_known_123(struct thread_info *$tinfo, value $s_252, value $CoqdNumbersdCyclicdInt63dUint63dsize_253)
{
  struct stack_frame frame;
  value root[2];
  register value $y_254;
  register value $p_255;
  register value $p_257;
  register value $y_259;
  register value $y_260;
  register value $prim_261;
  register value *$alloc;
  register value *$limit;
  register value *$args;
  register _Bool $arg;
  register value $result;
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $args = (*$tinfo).args;
  frame.next = root;
  frame.root = root;
  frame.prev = (*$tinfo).fp;
  if (($s_252 & 1) == 0) {
    switch (*((value *) $s_252 + -1LL) & 255LL) {
      case 0:
        $p_255 = *((value *) $s_252 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value, value)) of_pos_rec_uncurried_known_108)
          ($tinfo, $p_255, $CoqdNumbersdCyclicdInt63dUint63dsize_253);
        return $result;
        break;
      default:
        $p_257 = *((value *) $s_252 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_259 =
          ((value (*)(struct thread_info *, value, value)) of_pos_rec_uncurried_known_108)
          ($tinfo, $p_257, $CoqdNumbersdCyclicdInt63dUint63dsize_253);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        /*skip*/;
        $y_260 = 1LLU;
        $prim_261 =
          ((value (*)(value, value)) prim_int63_sub)
          ($y_260, $y_259);
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $prim_261;
        break;
      
    }
  } else {
    switch ($s_252 >> 1LL) {
      default:
        $y_254 = 1LLU;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_254;
        break;
      
    }
  }
}

value succ_known_122(struct thread_info *$tinfo, value $x_243)
{
  struct stack_frame frame;
  value root[1];
  register value $p_244;
  register value $y_245;
  register value $y_246;
  register value $p_247;
  register value $y_248;
  register value $y_249;
  register value $y_250;
  register value *$alloc;
  register value *$limit;
  register value *$args;
  register _Bool $arg;
  register value $result;
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $args = (*$tinfo).args;
  frame.next = root;
  frame.root = root;
  frame.prev = (*$tinfo).fp;
  if (!(2LL <= $limit - $alloc)) {
    *(root + 0LL) = $x_243;
    frame.next = root + 1LL;
    (*$tinfo).fp = &frame;
    (*$tinfo).nalloc = 2LL;
    garbage_collect($tinfo);
    $x_243 = *(root + 0LL);
    (*$tinfo).fp = frame.prev;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  if (($x_243 & 1) == 0) {
    switch (*((value *) $x_243 + -1LL) & 255LL) {
      case 0:
        $p_244 = *((value *) $x_243 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_245 =
          ((value (*)(struct thread_info *, value)) succ_known_122)
          ($tinfo, $p_244);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_245;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_245 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_246 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_246 + -1LL) = 1025LL;
        *((value *) $y_246 + 0LL) = $y_245;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_246;
        break;
      default:
        $p_247 = *((value *) $x_243 + 0LL);
        $y_248 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_248 + -1LL) = 1024LL;
        *((value *) $y_248 + 0LL) = $p_247;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_248;
        break;
      
    }
  } else {
    switch ($x_243 >> 1LL) {
      default:
        $y_249 = 1LL;
        $y_250 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_250 + -1LL) = 1025LL;
        *((value *) $y_250 + 0LL) = $y_249;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_250;
        break;
      
    }
  }
}

value of_succ_nat_known_121(struct thread_info *$tinfo, value $n_237)
{
  struct stack_frame frame;
  value root[1];
  register value $y_238;
  register value $x_239;
  register value $y_240;
  register value *$alloc;
  register value *$limit;
  register value *$args;
  register _Bool $arg;
  register value $result;
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $args = (*$tinfo).args;
  frame.next = root;
  frame.root = root;
  frame.prev = (*$tinfo).fp;
  if (($n_237 & 1) == 0) {
    switch (*((value *) $n_237 + -1LL) & 255LL) {
      default:
        $x_239 = *((value *) $n_237 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_240 =
          ((value (*)(struct thread_info *, value)) of_succ_nat_known_121)
          ($tinfo, $x_239);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        /*skip*/;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value)) succ_known_122)
          ($tinfo, $y_240);
        return $result;
        break;
      
    }
  } else {
    switch ($n_237 >> 1LL) {
      default:
        $y_238 = 1LL;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_238;
        break;
      
    }
  }
}

value f_case_known_120(struct thread_info *$tinfo, value $s_230)
{
  struct stack_frame frame;
  value root[1];
  register value $y_231;
  register value $n_232;
  register value $y_234;
  register value $y_235;
  register value *$alloc;
  register value *$limit;
  register value *$args;
  register _Bool $arg;
  register value $result;
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $args = (*$tinfo).args;
  frame.next = root;
  frame.root = root;
  frame.prev = (*$tinfo).fp;
  if (($s_230 & 1) == 0) {
    switch (*((value *) $s_230 + -1LL) & 255LL) {
      default:
        $n_232 = *((value *) $s_230 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_234 =
          ((value (*)(struct thread_info *, value)) of_succ_nat_known_121)
          ($tinfo, $n_232);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_234;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_234 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_235 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_235 + -1LL) = 1024LL;
        *((value *) $y_235 + 0LL) = $y_234;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_235;
        break;
      
    }
  } else {
    switch ($s_230 >> 1LL) {
      default:
        $y_231 = 1LL;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_231;
        break;
      
    }
  }
}

value fib_loop_nat_uncurried_uncurried_known_119(struct thread_info *$tinfo, value $b_223, value $a_224, value $i_225)
{
  struct stack_frame frame;
  value root[3];
  register value $ip_226;
  register value $y_228;
  register value *$alloc;
  register value *$limit;
  register value *$args;
  register _Bool $arg;
  register value $result;
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $args = (*$tinfo).args;
  frame.next = root;
  frame.root = root;
  frame.prev = (*$tinfo).fp;
  if (($i_225 & 1) == 0) {
    switch (*((value *) $i_225 + -1LL) & 255LL) {
      default:
        $ip_226 = *((value *) $i_225 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 1LL) = $ip_226;
        *(root + 0LL) = $a_224;
        frame.next = root + 2LL;
        (*$tinfo).fp = &frame;
        $y_228 =
          ((value (*)(struct thread_info *, value, value)) add_uncurried_known_109)
          ($tinfo, $b_223, $a_224);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $ip_226 = *(root + 1LL);
        $a_224 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value, value, value)) fib_loop_nat_uncurried_uncurried_known_119)
          ($tinfo, $a_224, $y_228, $ip_226);
        return $result;
        break;
      
    }
  } else {
    switch ($i_225 >> 1LL) {
      default:
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $b_223;
        break;
      
    }
  }
}

value iter_uncurried_known_118(struct thread_info *$tinfo, value $a_212, value $p_213)
{
  struct stack_frame frame;
  value root[2];
  register value $p_214;
  register value $y_216;
  register value $y_217;
  register value $p_219;
  register value $y_221;
  register value *$alloc;
  register value *$limit;
  register value *$args;
  register _Bool $arg;
  register value $result;
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $args = (*$tinfo).args;
  frame.next = root;
  frame.root = root;
  frame.prev = (*$tinfo).fp;
  if (($p_213 & 1) == 0) {
    switch (*((value *) $p_213 + -1LL) & 255LL) {
      case 0:
        $p_214 = *((value *) $p_213 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 1LL) = $p_214;
        *(root + 0LL) = $a_212;
        frame.next = root + 2LL;
        (*$tinfo).fp = &frame;
        $y_216 =
          ((value (*)(struct thread_info *, value, value)) add_uncurried_known_109)
          ($tinfo, $a_212, $a_212);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $p_214 = *(root + 1LL);
        $a_212 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $a_212;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_217 =
          ((value (*)(struct thread_info *, value, value)) iter_uncurried_known_118)
          ($tinfo, $y_216, $p_214);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $a_212 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value, value)) add_uncurried_known_109)
          ($tinfo, $y_217, $a_212);
        return $result;
        break;
      default:
        $p_219 = *((value *) $p_213 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $p_219;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_221 =
          ((value (*)(struct thread_info *, value, value)) add_uncurried_known_109)
          ($tinfo, $a_212, $a_212);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $p_219 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value, value)) iter_uncurried_known_118)
          ($tinfo, $y_221, $p_219);
        return $result;
        break;
      
    }
  } else {
    switch ($p_213 >> 1LL) {
      default:
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $a_212;
        break;
      
    }
  }
}

value f_case_known_117(struct thread_info *$tinfo, value $s_204)
{
  struct stack_frame frame;
  value root[1];
  register value $y_205;
  register value $p_206;
  register value $y_208;
  register value $y_209;
  register value $y_210;
  register value *$alloc;
  register value *$limit;
  register value *$args;
  register _Bool $arg;
  register value $result;
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $args = (*$tinfo).args;
  frame.next = root;
  frame.root = root;
  frame.prev = (*$tinfo).fp;
  if (!(2LL <= $limit - $alloc)) {
    *(root + 0LL) = $s_204;
    frame.next = root + 1LL;
    (*$tinfo).fp = &frame;
    (*$tinfo).nalloc = 2LL;
    garbage_collect($tinfo);
    $s_204 = *(root + 0LL);
    (*$tinfo).fp = frame.prev;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  if (($s_204 & 1) == 0) {
    switch (*((value *) $s_204 + -1LL) & 255LL) {
      case 0:
        $p_206 = *((value *) $s_204 + 0LL);
        $y_208 = 1LL;
        $y_209 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_209 + -1LL) = 1024LL;
        *((value *) $y_209 + 0LL) = $y_208;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value, value)) iter_uncurried_known_118)
          ($tinfo, $y_209, $p_206);
        return $result;
        break;
      default:
        $y_210 = 1LL;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_210;
        break;
      
    }
  } else {
    switch ($s_204 >> 1LL) {
      default:
        $y_205 = 1LL;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_205;
        break;
      
    }
  }
}

value f_case_known_116(struct thread_info *$tinfo, value $s_198)
{
  struct stack_frame frame;
  value root[1];
  register value $CoqdZArithdBinIntDefdZdsucc_double_wrapperbogus_env_199;
  register value $CoqdZArithdBinIntDefdZdsucc_double_wrapper_clo_200;
  register value $CoqdZArithdBinIntDefdZddouble_wrapperbogus_env_201;
  register value $CoqdZArithdBinIntDefdZddouble_wrapper_clo_202;
  register value *$alloc;
  register value *$limit;
  register value *$args;
  register _Bool $arg;
  register value $result;
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $args = (*$tinfo).args;
  frame.next = root;
  frame.root = root;
  frame.prev = (*$tinfo).fp;
  if (!(3LL <= $limit - $alloc)) {
    *(root + 0LL) = $s_198;
    frame.next = root + 1LL;
    (*$tinfo).fp = &frame;
    (*$tinfo).nalloc = 3LL;
    garbage_collect($tinfo);
    $s_198 = *(root + 0LL);
    (*$tinfo).fp = frame.prev;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  if (($s_198 & 1) == 0) {
    switch (*((value *) $s_198 + -1LL) & 255LL) {
      
    }
  } else {
    switch ($s_198 >> 1LL) {
      case 0:
        $CoqdZArithdBinIntDefdZdsucc_double_wrapperbogus_env_199 = 1LL;
        $CoqdZArithdBinIntDefdZdsucc_double_wrapper_clo_200 =
          (value) ($alloc + 1LL);
        $alloc = $alloc + 3LL;
        *((value *) $CoqdZArithdBinIntDefdZdsucc_double_wrapper_clo_200
           + -1LL) =
          2048LL;
        *((value *) $CoqdZArithdBinIntDefdZdsucc_double_wrapper_clo_200
           + 0LL) =
          CoqdZArithdBinIntDefdZdsucc_double_wrapper_114;
        *((value *) $CoqdZArithdBinIntDefdZdsucc_double_wrapper_clo_200
           + 1LL) =
          $CoqdZArithdBinIntDefdZdsucc_double_wrapperbogus_env_199;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $CoqdZArithdBinIntDefdZdsucc_double_wrapper_clo_200;
        break;
      default:
        $CoqdZArithdBinIntDefdZddouble_wrapperbogus_env_201 = 1LL;
        $CoqdZArithdBinIntDefdZddouble_wrapper_clo_202 =
          (value) ($alloc + 1LL);
        $alloc = $alloc + 3LL;
        *((value *) $CoqdZArithdBinIntDefdZddouble_wrapper_clo_202 + -1LL) =
          2048LL;
        *((value *) $CoqdZArithdBinIntDefdZddouble_wrapper_clo_202 + 0LL) =
          CoqdZArithdBinIntDefdZddouble_wrapper_111;
        *((value *) $CoqdZArithdBinIntDefdZddouble_wrapper_clo_202 + 1LL) =
          $CoqdZArithdBinIntDefdZddouble_wrapperbogus_env_201;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $CoqdZArithdBinIntDefdZddouble_wrapper_clo_202;
        break;
      
    }
  }
}

value to_Z_rec_uncurried_known_115(struct thread_info *$tinfo, value $i_182, value $n_183)
{
  struct stack_frame frame;
  value root[2];
  register value $y_184;
  register value $n_185;
  register value $y_187;
  register value $prim_188;
  register value $y_189;
  register value $prim_190;
  register value $y_191;
  register value $y_192;
  register value $prim_193;
  register value $y_194;
  register value $y_code_195;
  register value $y_env_196;
  register value *$alloc;
  register value *$limit;
  register value *$args;
  register _Bool $arg;
  register value $result;
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $args = (*$tinfo).args;
  frame.next = root;
  frame.root = root;
  frame.prev = (*$tinfo).fp;
  if (($n_183 & 1) == 0) {
    switch (*((value *) $n_183 + -1LL) & 255LL) {
      default:
        $n_185 = *((value *) $n_183 + 0LL);
        $y_187 = 3LLU;
        $prim_188 =
          ((value (*)(value, value)) prim_int63_land)
          ($i_182, $y_187);
        $y_189 = 1LLU;
        $prim_190 =
          ((value (*)(value, value)) prim_int63_eqb)
          ($prim_188, $y_189);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 1LL) = $n_185;
        *(root + 0LL) = $i_182;
        frame.next = root + 2LL;
        (*$tinfo).fp = &frame;
        $y_191 =
          ((value (*)(struct thread_info *, value)) f_case_known_116)
          ($tinfo, $prim_190);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $n_185 = *(root + 1LL);
        $i_182 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $y_192 = 3LLU;
        $prim_193 =
          ((value (*)(value, value)) prim_int63_lsr)
          ($i_182, $y_192);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $y_191;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_194 =
          ((value (*)(struct thread_info *, value, value)) to_Z_rec_uncurried_known_115)
          ($tinfo, $prim_193, $n_185);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $y_191 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $y_code_195 = *((value *) $y_191 + 0LL);
        $y_env_196 = *((value *) $y_191 + 1LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value, value)) $y_code_195)
          ($tinfo, $y_env_196, $y_194);
        return $result;
        break;
      
    }
  } else {
    switch ($n_183 >> 1LL) {
      default:
        $y_184 = 1LL;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_184;
        break;
      
    }
  }
}

value CoqdZArithdBinIntDefdZdsucc_double_wrapper_114(struct thread_info *$tinfo, value $env_178, value $x_179)
{
  struct stack_frame frame;
  value root[1];
  register value *$alloc;
  register value *$limit;
  register value *$args;
  register _Bool $arg;
  register value $result;
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $args = (*$tinfo).args;
  frame.next = root;
  frame.root = root;
  frame.prev = (*$tinfo).fp;
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  $result =
    ((value (*)(struct thread_info *, value)) CoqdZArithdBinIntDefdZdsucc_double_known_112)
    ($tinfo, $x_179);
  return $result;
}

value pred_double_known_113(struct thread_info *$tinfo, value $x_170)
{
  struct stack_frame frame;
  value root[1];
  register value $p_171;
  register value $y_172;
  register value $y_173;
  register value $p_174;
  register value $y_175;
  register value $y_176;
  register value $y_177;
  register value *$alloc;
  register value *$limit;
  register value *$args;
  register _Bool $arg;
  register value $result;
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $args = (*$tinfo).args;
  frame.next = root;
  frame.root = root;
  frame.prev = (*$tinfo).fp;
  if (!(4LL <= $limit - $alloc)) {
    *(root + 0LL) = $x_170;
    frame.next = root + 1LL;
    (*$tinfo).fp = &frame;
    (*$tinfo).nalloc = 4LL;
    garbage_collect($tinfo);
    $x_170 = *(root + 0LL);
    (*$tinfo).fp = frame.prev;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  if (($x_170 & 1) == 0) {
    switch (*((value *) $x_170 + -1LL) & 255LL) {
      case 0:
        $p_171 = *((value *) $x_170 + 0LL);
        $y_172 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_172 + -1LL) = 1025LL;
        *((value *) $y_172 + 0LL) = $p_171;
        $y_173 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_173 + -1LL) = 1024LL;
        *((value *) $y_173 + 0LL) = $y_172;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_173;
        break;
      default:
        $p_174 = *((value *) $x_170 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_175 =
          ((value (*)(struct thread_info *, value)) pred_double_known_113)
          ($tinfo, $p_174);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_175;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_175 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_176 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_176 + -1LL) = 1024LL;
        *((value *) $y_176 + 0LL) = $y_175;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_176;
        break;
      
    }
  } else {
    switch ($x_170 >> 1LL) {
      default:
        $y_177 = 1LL;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_177;
        break;
      
    }
  }
}

value CoqdZArithdBinIntDefdZdsucc_double_known_112(struct thread_info *$tinfo, value $x_159)
{
  struct stack_frame frame;
  value root[1];
  register value $y_160;
  register value $y_161;
  register value $p_162;
  register value $y_163;
  register value $y_164;
  register value $p_165;
  register value $y_167;
  register value $y_168;
  register value *$alloc;
  register value *$limit;
  register value *$args;
  register _Bool $arg;
  register value $result;
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $args = (*$tinfo).args;
  frame.next = root;
  frame.root = root;
  frame.prev = (*$tinfo).fp;
  if (!(4LL <= $limit - $alloc)) {
    *(root + 0LL) = $x_159;
    frame.next = root + 1LL;
    (*$tinfo).fp = &frame;
    (*$tinfo).nalloc = 4LL;
    garbage_collect($tinfo);
    $x_159 = *(root + 0LL);
    (*$tinfo).fp = frame.prev;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  if (($x_159 & 1) == 0) {
    switch (*((value *) $x_159 + -1LL) & 255LL) {
      case 0:
        $p_162 = *((value *) $x_159 + 0LL);
        $y_163 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_163 + -1LL) = 1024LL;
        *((value *) $y_163 + 0LL) = $p_162;
        $y_164 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_164 + -1LL) = 1024LL;
        *((value *) $y_164 + 0LL) = $y_163;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_164;
        break;
      default:
        $p_165 = *((value *) $x_159 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_167 =
          ((value (*)(struct thread_info *, value)) pred_double_known_113)
          ($tinfo, $p_165);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_167;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_167 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_168 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_168 + -1LL) = 1025LL;
        *((value *) $y_168 + 0LL) = $y_167;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_168;
        break;
      
    }
  } else {
    switch ($x_159 >> 1LL) {
      default:
        $y_160 = 1LL;
        $y_161 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_161 + -1LL) = 1024LL;
        *((value *) $y_161 + 0LL) = $y_160;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_161;
        break;
      
    }
  }
}

value CoqdZArithdBinIntDefdZddouble_wrapper_111(struct thread_info *$tinfo, value $env_155, value $x_156)
{
  struct stack_frame frame;
  value root[1];
  register value *$alloc;
  register value *$limit;
  register value *$args;
  register _Bool $arg;
  register value $result;
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $args = (*$tinfo).args;
  frame.next = root;
  frame.root = root;
  frame.prev = (*$tinfo).fp;
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  $result =
    ((value (*)(struct thread_info *, value)) CoqdZArithdBinIntDefdZddouble_known_110)
    ($tinfo, $x_156);
  return $result;
}

value CoqdZArithdBinIntDefdZddouble_known_110(struct thread_info *$tinfo, value $x_147)
{
  struct stack_frame frame;
  value root[1];
  register value $y_148;
  register value $p_149;
  register value $y_150;
  register value $y_151;
  register value $p_152;
  register value $y_153;
  register value $y_154;
  register value *$alloc;
  register value *$limit;
  register value *$args;
  register _Bool $arg;
  register value $result;
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $args = (*$tinfo).args;
  frame.next = root;
  frame.root = root;
  frame.prev = (*$tinfo).fp;
  if (!(4LL <= $limit - $alloc)) {
    *(root + 0LL) = $x_147;
    frame.next = root + 1LL;
    (*$tinfo).fp = &frame;
    (*$tinfo).nalloc = 4LL;
    garbage_collect($tinfo);
    $x_147 = *(root + 0LL);
    (*$tinfo).fp = frame.prev;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  if (($x_147 & 1) == 0) {
    switch (*((value *) $x_147 + -1LL) & 255LL) {
      case 0:
        $p_149 = *((value *) $x_147 + 0LL);
        $y_150 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_150 + -1LL) = 1025LL;
        *((value *) $y_150 + 0LL) = $p_149;
        $y_151 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_151 + -1LL) = 1024LL;
        *((value *) $y_151 + 0LL) = $y_150;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_151;
        break;
      default:
        $p_152 = *((value *) $x_147 + 0LL);
        $y_153 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_153 + -1LL) = 1025LL;
        *((value *) $y_153 + 0LL) = $p_152;
        $y_154 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_154 + -1LL) = 1025LL;
        *((value *) $y_154 + 0LL) = $y_153;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_154;
        break;
      
    }
  } else {
    switch ($x_147 >> 1LL) {
      default:
        $y_148 = 1LL;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_148;
        break;
      
    }
  }
}

value add_uncurried_known_109(struct thread_info *$tinfo, value $m_141, value $n_142)
{
  struct stack_frame frame;
  value root[2];
  register value $p_143;
  register value $y_144;
  register value $y_145;
  register value *$alloc;
  register value *$limit;
  register value *$args;
  register _Bool $arg;
  register value $result;
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $args = (*$tinfo).args;
  frame.next = root;
  frame.root = root;
  frame.prev = (*$tinfo).fp;
  if (($n_142 & 1) == 0) {
    switch (*((value *) $n_142 + -1LL) & 255LL) {
      default:
        $p_143 = *((value *) $n_142 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_144 =
          ((value (*)(struct thread_info *, value, value)) add_uncurried_known_109)
          ($tinfo, $m_141, $p_143);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_144;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_144 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_145 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_145 + -1LL) = 1024LL;
        *((value *) $y_145 + 0LL) = $y_144;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_145;
        break;
      
    }
  } else {
    switch ($n_142 >> 1LL) {
      default:
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $m_141;
        break;
      
    }
  }
}

value of_pos_rec_uncurried_known_108(struct thread_info *$tinfo, value $p_125, value $n_126)
{
  struct stack_frame frame;
  value root[2];
  register value $y_127;
  register value $n_128;
  register value $p_129;
  register value $y_130;
  register value $y_131;
  register value $prim_132;
  register value $y_133;
  register value $prim_134;
  register value $p_135;
  register value $y_136;
  register value $y_137;
  register value $prim_138;
  register value $y_139;
  register value *$alloc;
  register value *$limit;
  register value *$args;
  register _Bool $arg;
  register value $result;
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $args = (*$tinfo).args;
  frame.next = root;
  frame.root = root;
  frame.prev = (*$tinfo).fp;
  if (($n_126 & 1) == 0) {
    switch (*((value *) $n_126 + -1LL) & 255LL) {
      default:
        $n_128 = *((value *) $n_126 + 0LL);
        if (($p_125 & 1) == 0) {
          switch (*((value *) $p_125 + -1LL) & 255LL) {
            case 0:
              $p_129 = *((value *) $p_125 + 0LL);
              $args = (*$tinfo).args;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              /*skip*/;
              $y_130 =
                ((value (*)(struct thread_info *, value, value)) of_pos_rec_uncurried_known_108)
                ($tinfo, $p_129, $n_128);
              $alloc = (*$tinfo).alloc;
              $limit = (*$tinfo).limit;
              /*skip*/;
              $y_131 = 3LLU;
              $prim_132 =
                ((value (*)(value, value)) prim_int63_lsl)
                ($y_130, $y_131);
              $y_133 = 3LLU;
              $prim_134 =
                ((value (*)(value, value)) prim_int63_lor)
                ($prim_132, $y_133);
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $prim_134;
              break;
            default:
              $p_135 = *((value *) $p_125 + 0LL);
              $args = (*$tinfo).args;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              /*skip*/;
              $y_136 =
                ((value (*)(struct thread_info *, value, value)) of_pos_rec_uncurried_known_108)
                ($tinfo, $p_135, $n_128);
              $alloc = (*$tinfo).alloc;
              $limit = (*$tinfo).limit;
              /*skip*/;
              $y_137 = 3LLU;
              $prim_138 =
                ((value (*)(value, value)) prim_int63_lsl)
                ($y_136, $y_137);
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $prim_138;
              break;
            
          }
        } else {
          switch ($p_125 >> 1LL) {
            default:
              $y_139 = 3LLU;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $y_139;
              break;
            
          }
        }
        break;
      
    }
  } else {
    switch ($n_126 >> 1LL) {
      default:
        $y_127 = 1LLU;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_127;
        break;
      
    }
  }
}

value body(struct thread_info *$tinfo)
{
  struct stack_frame frame;
  value root[2];
  register value $y_262;
  register value $y_263;
  register value $y_264;
  register value $y_265;
  register value $y_266;
  register value $y_267;
  register value $y_268;
  register value $y_269;
  register value $y_270;
  register value $y_271;
  register value $y_272;
  register value $y_273;
  register value $y_274;
  register value $y_275;
  register value $y_276;
  register value $y_277;
  register value $y_278;
  register value $y_279;
  register value $y_280;
  register value $y_281;
  register value $y_282;
  register value $y_283;
  register value $y_284;
  register value $y_285;
  register value $y_286;
  register value $y_287;
  register value $y_288;
  register value $y_289;
  register value $y_290;
  register value $y_291;
  register value $y_292;
  register value $y_293;
  register value $y_294;
  register value $y_295;
  register value $y_296;
  register value $y_297;
  register value $y_298;
  register value $y_299;
  register value $y_300;
  register value $y_301;
  register value $y_302;
  register value $y_303;
  register value $y_304;
  register value $y_305;
  register value $y_306;
  register value $y_307;
  register value $y_308;
  register value $y_309;
  register value $y_310;
  register value $y_311;
  register value $y_312;
  register value $y_313;
  register value $y_314;
  register value $y_315;
  register value $y_316;
  register value $y_317;
  register value $y_318;
  register value $y_319;
  register value $y_320;
  register value $y_321;
  register value $y_322;
  register value $y_323;
  register value $y_324;
  register value $CoqdNumbersdCyclicdInt63dUint63dsize_325;
  register value $y_327;
  register value $y_328;
  register value $y_330;
  register value $y_332;
  register value $y_333;
  register value $y_334;
  register value $y_335;
  register value $y_337;
  register value $CertiCoqdBenchmarksdFibonaccidfibdprogram_339;
  register value *$alloc;
  register value *$limit;
  register value *$args;
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $args = (*$tinfo).args;
  frame.next = root;
  frame.root = root;
  frame.prev = (*$tinfo).fp;
  if (!(126LL <= $limit - $alloc)) {
    /*skip*/;
    (*$tinfo).nalloc = 126LL;
    garbage_collect($tinfo);
    /*skip*/;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  $y_262 = 1LL;
  $y_263 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_263 + -1LL) = 1024LL;
  *((value *) $y_263 + 0LL) = $y_262;
  $y_264 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_264 + -1LL) = 1024LL;
  *((value *) $y_264 + 0LL) = $y_263;
  $y_265 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_265 + -1LL) = 1024LL;
  *((value *) $y_265 + 0LL) = $y_264;
  $y_266 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_266 + -1LL) = 1024LL;
  *((value *) $y_266 + 0LL) = $y_265;
  $y_267 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_267 + -1LL) = 1024LL;
  *((value *) $y_267 + 0LL) = $y_266;
  $y_268 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_268 + -1LL) = 1024LL;
  *((value *) $y_268 + 0LL) = $y_267;
  $y_269 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_269 + -1LL) = 1024LL;
  *((value *) $y_269 + 0LL) = $y_268;
  $y_270 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_270 + -1LL) = 1024LL;
  *((value *) $y_270 + 0LL) = $y_269;
  $y_271 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_271 + -1LL) = 1024LL;
  *((value *) $y_271 + 0LL) = $y_270;
  $y_272 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_272 + -1LL) = 1024LL;
  *((value *) $y_272 + 0LL) = $y_271;
  $y_273 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_273 + -1LL) = 1024LL;
  *((value *) $y_273 + 0LL) = $y_272;
  $y_274 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_274 + -1LL) = 1024LL;
  *((value *) $y_274 + 0LL) = $y_273;
  $y_275 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_275 + -1LL) = 1024LL;
  *((value *) $y_275 + 0LL) = $y_274;
  $y_276 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_276 + -1LL) = 1024LL;
  *((value *) $y_276 + 0LL) = $y_275;
  $y_277 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_277 + -1LL) = 1024LL;
  *((value *) $y_277 + 0LL) = $y_276;
  $y_278 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_278 + -1LL) = 1024LL;
  *((value *) $y_278 + 0LL) = $y_277;
  $y_279 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_279 + -1LL) = 1024LL;
  *((value *) $y_279 + 0LL) = $y_278;
  $y_280 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_280 + -1LL) = 1024LL;
  *((value *) $y_280 + 0LL) = $y_279;
  $y_281 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_281 + -1LL) = 1024LL;
  *((value *) $y_281 + 0LL) = $y_280;
  $y_282 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_282 + -1LL) = 1024LL;
  *((value *) $y_282 + 0LL) = $y_281;
  $y_283 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_283 + -1LL) = 1024LL;
  *((value *) $y_283 + 0LL) = $y_282;
  $y_284 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_284 + -1LL) = 1024LL;
  *((value *) $y_284 + 0LL) = $y_283;
  $y_285 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_285 + -1LL) = 1024LL;
  *((value *) $y_285 + 0LL) = $y_284;
  $y_286 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_286 + -1LL) = 1024LL;
  *((value *) $y_286 + 0LL) = $y_285;
  $y_287 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_287 + -1LL) = 1024LL;
  *((value *) $y_287 + 0LL) = $y_286;
  $y_288 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_288 + -1LL) = 1024LL;
  *((value *) $y_288 + 0LL) = $y_287;
  $y_289 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_289 + -1LL) = 1024LL;
  *((value *) $y_289 + 0LL) = $y_288;
  $y_290 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_290 + -1LL) = 1024LL;
  *((value *) $y_290 + 0LL) = $y_289;
  $y_291 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_291 + -1LL) = 1024LL;
  *((value *) $y_291 + 0LL) = $y_290;
  $y_292 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_292 + -1LL) = 1024LL;
  *((value *) $y_292 + 0LL) = $y_291;
  $y_293 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_293 + -1LL) = 1024LL;
  *((value *) $y_293 + 0LL) = $y_292;
  $y_294 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_294 + -1LL) = 1024LL;
  *((value *) $y_294 + 0LL) = $y_293;
  $y_295 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_295 + -1LL) = 1024LL;
  *((value *) $y_295 + 0LL) = $y_294;
  $y_296 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_296 + -1LL) = 1024LL;
  *((value *) $y_296 + 0LL) = $y_295;
  $y_297 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_297 + -1LL) = 1024LL;
  *((value *) $y_297 + 0LL) = $y_296;
  $y_298 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_298 + -1LL) = 1024LL;
  *((value *) $y_298 + 0LL) = $y_297;
  $y_299 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_299 + -1LL) = 1024LL;
  *((value *) $y_299 + 0LL) = $y_298;
  $y_300 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_300 + -1LL) = 1024LL;
  *((value *) $y_300 + 0LL) = $y_299;
  $y_301 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_301 + -1LL) = 1024LL;
  *((value *) $y_301 + 0LL) = $y_300;
  $y_302 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_302 + -1LL) = 1024LL;
  *((value *) $y_302 + 0LL) = $y_301;
  $y_303 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_303 + -1LL) = 1024LL;
  *((value *) $y_303 + 0LL) = $y_302;
  $y_304 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_304 + -1LL) = 1024LL;
  *((value *) $y_304 + 0LL) = $y_303;
  $y_305 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_305 + -1LL) = 1024LL;
  *((value *) $y_305 + 0LL) = $y_304;
  $y_306 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_306 + -1LL) = 1024LL;
  *((value *) $y_306 + 0LL) = $y_305;
  $y_307 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_307 + -1LL) = 1024LL;
  *((value *) $y_307 + 0LL) = $y_306;
  $y_308 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_308 + -1LL) = 1024LL;
  *((value *) $y_308 + 0LL) = $y_307;
  $y_309 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_309 + -1LL) = 1024LL;
  *((value *) $y_309 + 0LL) = $y_308;
  $y_310 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_310 + -1LL) = 1024LL;
  *((value *) $y_310 + 0LL) = $y_309;
  $y_311 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_311 + -1LL) = 1024LL;
  *((value *) $y_311 + 0LL) = $y_310;
  $y_312 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_312 + -1LL) = 1024LL;
  *((value *) $y_312 + 0LL) = $y_311;
  $y_313 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_313 + -1LL) = 1024LL;
  *((value *) $y_313 + 0LL) = $y_312;
  $y_314 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_314 + -1LL) = 1024LL;
  *((value *) $y_314 + 0LL) = $y_313;
  $y_315 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_315 + -1LL) = 1024LL;
  *((value *) $y_315 + 0LL) = $y_314;
  $y_316 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_316 + -1LL) = 1024LL;
  *((value *) $y_316 + 0LL) = $y_315;
  $y_317 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_317 + -1LL) = 1024LL;
  *((value *) $y_317 + 0LL) = $y_316;
  $y_318 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_318 + -1LL) = 1024LL;
  *((value *) $y_318 + 0LL) = $y_317;
  $y_319 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_319 + -1LL) = 1024LL;
  *((value *) $y_319 + 0LL) = $y_318;
  $y_320 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_320 + -1LL) = 1024LL;
  *((value *) $y_320 + 0LL) = $y_319;
  $y_321 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_321 + -1LL) = 1024LL;
  *((value *) $y_321 + 0LL) = $y_320;
  $y_322 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_322 + -1LL) = 1024LL;
  *((value *) $y_322 + 0LL) = $y_321;
  $y_323 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_323 + -1LL) = 1024LL;
  *((value *) $y_323 + 0LL) = $y_322;
  $y_324 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_324 + -1LL) = 1024LL;
  *((value *) $y_324 + 0LL) = $y_323;
  $CoqdNumbersdCyclicdInt63dUint63dsize_325 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $CoqdNumbersdCyclicdInt63dUint63dsize_325 + -1LL) = 1024LL;
  *((value *) $CoqdNumbersdCyclicdInt63dUint63dsize_325 + 0LL) = $y_324;
  $y_327 = 91LLU;
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  *(root + 0LL) = $CoqdNumbersdCyclicdInt63dUint63dsize_325;
  frame.next = root + 1LL;
  (*$tinfo).fp = &frame;
  $y_328 =
    ((value (*)(struct thread_info *, value, value)) to_Z_rec_uncurried_known_115)
    ($tinfo, $y_327, $CoqdNumbersdCyclicdInt63dUint63dsize_325);
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $CoqdNumbersdCyclicdInt63dUint63dsize_325 = *(root + 0LL);
  (*$tinfo).fp = frame.prev;
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  *(root + 0LL) = $CoqdNumbersdCyclicdInt63dUint63dsize_325;
  frame.next = root + 1LL;
  (*$tinfo).fp = &frame;
  $y_330 =
    ((value (*)(struct thread_info *, value)) f_case_known_117)
    ($tinfo, $y_328);
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  if (!(2LL <= $limit - $alloc)) {
    *(root + 1LL) = $y_330;
    frame.next = root + 2LL;
    (*$tinfo).nalloc = 2LL;
    garbage_collect($tinfo);
    $y_330 = *(root + 1LL);
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  $CoqdNumbersdCyclicdInt63dUint63dsize_325 = *(root + 0LL);
  (*$tinfo).fp = frame.prev;
  $y_332 = 1LL;
  $y_333 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_333 + -1LL) = 1024LL;
  *((value *) $y_333 + 0LL) = $y_332;
  $y_334 = 1LL;
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  *(root + 0LL) = $CoqdNumbersdCyclicdInt63dUint63dsize_325;
  frame.next = root + 1LL;
  (*$tinfo).fp = &frame;
  $y_335 =
    ((value (*)(struct thread_info *, value, value, value)) fib_loop_nat_uncurried_uncurried_known_119)
    ($tinfo, $y_334, $y_333, $y_330);
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $CoqdNumbersdCyclicdInt63dUint63dsize_325 = *(root + 0LL);
  (*$tinfo).fp = frame.prev;
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  *(root + 0LL) = $CoqdNumbersdCyclicdInt63dUint63dsize_325;
  frame.next = root + 1LL;
  (*$tinfo).fp = &frame;
  $y_337 =
    ((value (*)(struct thread_info *, value)) f_case_known_120)
    ($tinfo, $y_335);
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $CoqdNumbersdCyclicdInt63dUint63dsize_325 = *(root + 0LL);
  (*$tinfo).fp = frame.prev;
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  /*skip*/;
  $CertiCoqdBenchmarksdFibonaccidfibdprogram_339 =
    ((value (*)(struct thread_info *, value, value)) f_case_known_123)
    ($tinfo, $y_337, $CoqdNumbersdCyclicdInt63dUint63dsize_325);
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  /*skip*/;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  return $CertiCoqdBenchmarksdFibonaccidfibdprogram_339;
}


#endif /* CERTICOQ_BENCHMARKS_FIBONACCI_FIB_PROGRAM_C */
