SRC = build_goto_trace.cpp \
      locs.cpp \
      path_replay.cpp \
      path_symex.cpp \
      path_symex_allocate.cpp \
      path_symex_history.cpp \
      path_symex_state.cpp \
      path_symex_state_read.cpp \
      var_map.cpp \
      # Empty last line

INCLUDES= -I .. -I ../../$(CPROVER_DIR)/src

include ../config.inc
include ../../$(CPROVER_DIR)/src/config.inc
include ../../$(CPROVER_DIR)/src/common

CLEANFILES = path-symex$(LIBEXT)

all: path-symex$(LIBEXT)

###############################################################################

path-symex$(LIBEXT): $(OBJ)
	$(LINKLIB)
