/*******************************************************************\

Module: Loop heads for locs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// CFG made of Program Locations, built from goto_functionst

#ifndef CPROVER_GOTO_LOCS_LOOP_HEADS_H
#define CPROVER_GOTO_LOCS_LOOP_HEADS_H

#include <vector>

#include "locs.h"

#include <util/invariant.h>

struct loop_headst
{
public:
  explicit loop_headst(const locst &locs);

  bool operator[](const loc_reft loc_ref) const
  {
    PRECONDITION(!loc_ref.is_nil());
    DATA_INVARIANT(loc_ref.loc_number<map.size(), "loc_ref ok");
    return map[loc_ref.loc_number];
  }

protected:
  typedef std::vector<bool> mapt;
  mapt map;
};

#endif // CPROVER_PATH_SYMEX_LOCS_H
