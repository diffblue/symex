/*******************************************************************\

Module: Build Goto Trace from Path Symex History

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Build Goto Trace from Path Symex History

// NOLINT(build/header_guard) as this file is also symlinked
#ifndef CPROVER_PATH_SYMEX_BUILD_GOTO_TRACE_H
#define CPROVER_PATH_SYMEX_BUILD_GOTO_TRACE_H

#include <util/decision_procedure.h>
#include <goto-programs/goto_trace.h>

#include "path_symex_state.h"

goto_tracet build_goto_trace(
  const path_symex_statet &,
  const decision_proceduret &);

#endif // CPROVER_PATH_SYMEX_BUILD_GOTO_TRACE_H
