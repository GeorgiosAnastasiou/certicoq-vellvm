COQC      ?= coqc
CLANG     ?= clang
COQLIB     := $(shell coqc -where)
PLUGIN_RT  := $(COQLIB)/user-contrib/CertiCoq/Plugin/runtime

COQFLAGS  ?= -Q . CertiCoq.Benchmarks.Fibonacci \
             -Q $(COQLIB)/user-contrib/CertiCoq CertiCoq

EXTRACT_DIR := extraction
EXTRACTED_C := $(EXTRACT_DIR)/CertiCoq.Benchmarks.Fibonacci.fib.program.c

# pick up glue files in either place
GLUE_CS    := $(wildcard $(EXTRACT_DIR)/glue*.c) $(wildcard glue*.c)

# only link get_ordinal.c if there is NO glue file (glue defines the same helpers)
ORDINAL_SRC := $(if $(strip $(GLUE_CS)),,$(PLUGIN_RT)/get_ordinal.c)

TARGET      := fib_app

all: $(TARGET)

$(EXTRACT_DIR):
	mkdir -p $@

$(EXTRACT_DIR)/stamp: fib.v | $(EXTRACT_DIR)
	$(COQC) $(COQFLAGS) fib.v
	touch $@

$(EXTRACTED_C): $(EXTRACT_DIR)/stamp ;

$(TARGET): $(EXTRACTED_C) fib_main.c $(GLUE_CS)
	$(CLANG) -O2 -Wno-everything -fomit-frame-pointer -std=c99 \
	  -I"$(PLUGIN_RT)" -I"$(EXTRACT_DIR)" -I. \
	  fib_main.c \
	  "$(EXTRACTED_C)" \
	  $(GLUE_CS) \
	  "$(PLUGIN_RT)/gc_stack.c" \
	  $(ORDINAL_SRC) \
	  "$(PLUGIN_RT)/prim_floats.c" \
	  "$(PLUGIN_RT)/prim_int63.c" \
	  -o "$(TARGET)" -lm

clean:
	rm -rf $(EXTRACT_DIR) *.vo *.vok *.vos *.glob *.aux $(TARGET)

.PHONY: all clean
