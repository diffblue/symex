SRC = path_search.cpp \
      symex_cover.cpp \
      symex_main.cpp \
      symex_parse_options.cpp \
      # Empty last line

OBJ += ../../$(CPROVER_DIR)/src/ansi-c/ansi-c$(LIBEXT) \
       ../../$(CPROVER_DIR)/src/cpp/cpp$(LIBEXT) \
       ../../$(CPROVER_DIR)/jbmc/src/java_bytecode/java_bytecode$(LIBEXT) \
       ../../$(CPROVER_DIR)/src/linking/linking$(LIBEXT) \
       ../../$(CPROVER_DIR)/src/big-int/big-int$(LIBEXT) \
       ../../$(CPROVER_DIR)/src/goto-programs/goto-programs$(LIBEXT) \
       ../../$(CPROVER_DIR)/src/analyses/analyses$(LIBEXT) \
       ../../$(CPROVER_DIR)/src/langapi/langapi$(LIBEXT) \
       ../../$(CPROVER_DIR)/src/xmllang/xmllang$(LIBEXT) \
       ../../$(CPROVER_DIR)/src/assembler/assembler$(LIBEXT) \
       ../../$(CPROVER_DIR)/src/solvers/solvers$(LIBEXT) \
       ../../$(CPROVER_DIR)/src/util/util$(LIBEXT) \
       ../../$(CPROVER_DIR)/src/goto-symex/adjust_float_expressions$(OBJEXT) \
       ../../$(CPROVER_DIR)/src/goto-symex/rewrite_union$(OBJEXT) \
       ../../$(CPROVER_DIR)/src/pointer-analysis/dereference$(OBJEXT) \
       ../../$(CPROVER_DIR)/src/goto-instrument/cover$(OBJEXT) \
       ../../$(CPROVER_DIR)/src/goto-instrument/cover_filter$(OBJEXT) \
       ../../$(CPROVER_DIR)/src/goto-instrument/cover_basic_blocks$(OBJEXT) \
       ../../$(CPROVER_DIR)/src/goto-instrument/cover_instrument_branch$(OBJEXT) \
       ../../$(CPROVER_DIR)/src/goto-instrument/cover_instrument_condition$(OBJEXT) \
       ../../$(CPROVER_DIR)/src/goto-instrument/cover_instrument_decision$(OBJEXT) \
       ../../$(CPROVER_DIR)/src/goto-instrument/cover_instrument_location$(OBJEXT) \
       ../../$(CPROVER_DIR)/src/goto-instrument/cover_instrument_mcdc$(OBJEXT) \
       ../../$(CPROVER_DIR)/src/goto-instrument/cover_instrument_other$(OBJEXT) \
       ../../$(CPROVER_DIR)/src/goto-instrument/cover_util$(OBJEXT) \
       ../../$(CPROVER_DIR)/src/miniz/miniz$(OBJEXT) \
       ../../$(CPROVER_DIR)/src/json/json$(LIBEXT) \
       ../goto-locs/goto-locs$(LIBEXT) \
       ../path-symex/path-symex$(LIBEXT)

INCLUDES= -I .. -I ../../$(CPROVER_DIR)/src -I ../../$(CPROVER_DIR)/jbmc/src

LIBS =

include ../config.inc
include ../../$(CPROVER_DIR)/src/config.inc
include ../../$(CPROVER_DIR)/src/common

CLEANFILES = symex$(EXEEXT)

all: symex$(EXEEXT)

ifneq ($(wildcard ../specc/Makefile),)
  OBJ += ../specc/specc$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_SPECC
endif

ifneq ($(wildcard ../php/Makefile),)
  OBJ += ../php/php$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_PHP
endif

###############################################################################

symex$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: symex-mac-signed

symex-mac-signed: cbmc$(EXEEXT)
	strip symex$(EXEEXT) ; codesign -v -s $(OSX_IDENTITY) symex$(EXEEXT)
