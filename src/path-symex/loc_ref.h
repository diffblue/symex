/*******************************************************************\

Module: Program Locations

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Program Locations

#ifndef CPROVER_PATH_SYMEX_LOC_REF_H
#define CPROVER_PATH_SYMEX_LOC_REF_H

#include <goto-programs/goto_program.h>

class loc_reft
{
public:
  irep_idt function_identifier;
  goto_programt::const_targett target;

  loc_reft(irep_idt _function_identifier,
           goto_programt::const_targett _target):
    function_identifier(_function_identifier),
    target(_target)
  {
  }

  loc_reft() = default;

  bool is_nil() const
  {
    return function_identifier.empty();
  }

  bool is_not_nil() const
  {
    return !is_nil();
  }

  void increase()
  {
    ++target;
  }

  loc_reft next_loc() const
  {
    loc_reft tmp = *this;
    tmp.increase();
    return tmp;
  }

  loc_reft get_target() const
  {
    return loc_reft(function_identifier, target->get_target());
  }
};

inline std::ostream &operator<<(std::ostream &out, const loc_reft l)
{
  if(l.is_nil())
    return out << "nil";
  else
    return out << l.target->location_number << "@" << l.function_identifier;
}

inline bool operator< (const loc_reft &a, const loc_reft &b)
{
  if(a.function_identifier==b.function_identifier)
  {
    if(a.is_nil())
      return false; // both are nil
    else
      return a.target->location_number < b.target->location_number;
  }
  else
    return a.function_identifier<b.function_identifier;  
}

#endif // CPROVER_PATH_SYMEX_LOC_REF_H
