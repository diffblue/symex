SRC = path_search.cpp \
      symex_cover.cpp \
      symex_main.cpp \
      symex_parse_options.cpp \
      # Empty last line

OBJ += ../../$(CPROVER_DIR)/ansi-c/ansi-c$(LIBEXT) \
       ../../$(CPROVER_DIR)/cpp/cpp$(LIBEXT) \
       ../../$(CPROVER_DIR)/java_bytecode/java_bytecode$(LIBEXT) \
       ../../$(CPROVER_DIR)/linking/linking$(LIBEXT) \
       ../../$(CPROVER_DIR)/big-int/big-int$(LIBEXT) \
       ../../$(CPROVER_DIR)/goto-programs/goto-programs$(LIBEXT) \
       ../../$(CPROVER_DIR)/analyses/analyses$(LIBEXT) \
       ../../$(CPROVER_DIR)/langapi/langapi$(LIBEXT) \
       ../../$(CPROVER_DIR)/xmllang/xmllang$(LIBEXT) \
       ../../$(CPROVER_DIR)/assembler/assembler$(LIBEXT) \
       ../../$(CPROVER_DIR)/solvers/solvers$(LIBEXT) \
       ../../$(CPROVER_DIR)/util/util$(LIBEXT) \
       ../../$(CPROVER_DIR)/goto-symex/adjust_float_expressions$(OBJEXT) \
       ../../$(CPROVER_DIR)/goto-symex/rewrite_union$(OBJEXT) \
       ../../$(CPROVER_DIR)/pointer-analysis/dereference$(OBJEXT) \
       ../../$(CPROVER_DIR)/goto-instrument/cover$(OBJEXT) \
       ../../$(CPROVER_DIR)/path-symex/path-symex$(LIBEXT) \
       ../../$(CPROVER_DIR)/miniz/miniz$(OBJEXT) \
       ../../$(CPROVER_DIR)/json/json$(LIBEXT)

INCLUDES= -I .. -I ../../$(CPROVER_DIR)

LIBS =

include ../../$(CPROVER_DIR)/config.inc
include ../../$(CPROVER_DIR)/common

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
