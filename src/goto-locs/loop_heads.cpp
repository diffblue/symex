/*******************************************************************\

Module: Loop heads for locs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "loop_heads.h"

loop_headst::loop_headst(const locst &locs)
{
  map.resize(locs.size(), false);

  for(auto &l : locs.loc_vector)
    if(l.target->is_backwards_goto())
      map[l.branch_target.loc_number]=true;
}
