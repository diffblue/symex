SRC = locs.cpp loop_heads.cpp
      # Empty last line

INCLUDES= -I .. -I ../../$(CPROVER_DIR)/src

include ../config.inc
include ../../$(CPROVER_DIR)/src/config.inc
include ../../$(CPROVER_DIR)/src/common

CLEANFILES = path-symex$(LIBEXT)

all: goto-locs$(LIBEXT)

###############################################################################

goto-locs$(LIBEXT): $(OBJ)
	$(LINKLIB)
