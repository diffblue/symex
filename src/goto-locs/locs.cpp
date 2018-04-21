/*******************************************************************\

Module: Program Locations

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Program Locations

#include <langapi/language_util.h>

#include "locs.h"

locst::locst(
  const namespacet &_ns):
  ns(_ns)
{
}

void locst::build(const goto_functionst &goto_functions)
{
  // build locations

  typedef std::map<goto_programt::const_targett,
                   loc_reft> target_mapt;

  target_mapt target_map;

  forall_goto_functions(f_it, goto_functions)
  {
    const goto_functionst::goto_functiont &goto_function = f_it->second;

    function_entryt &function_entry=function_map[f_it->first];
    function_entry.type=goto_function.type;
    function_entry.hidden=goto_function.is_hidden();

    if(goto_function.body_available())
    {
      const loc_reft entry_loc=end();
      function_entry.first_loc=entry_loc;

      forall_goto_program_instructions(i_it, goto_function.body)
      {
        target_map[i_it]=end();
        loc_vector.push_back(loct(i_it));
      }
    }
    else
      function_entry.first_loc=loc_reft::nil();
  }

  if(function_map.find(goto_functionst::entry_point())==
     function_map.end())
    throw "no entry point";

  entry_loc=function_map[goto_functionst::entry_point()].first_loc;

  // build branch targets
  for(unsigned l=0; l<loc_vector.size(); l++)
  {
    const goto_programt::instructiont &i=*loc_vector[l].target;

    if(i.targets.empty())
    {
    }
    else if(i.targets.size()==1)
    {
      const target_mapt::const_iterator m_it=target_map.find(i.get_target());

      if(m_it==target_map.end())
        throw "locst::build: jump target not found";

      const loc_reft target=m_it->second;

      if(target.loc_number>=loc_vector.size())
        throw "locst::build: illegal jump target";

      loc_vector[l].branch_target=target;
    }
    else
      throw "locst does not support more than one branch target";
  }
}

void locst::output(std::ostream &out) const
{
  // first build a map of function entry locs
  std::map<loc_reft, irep_idt> entry_locs;

  for(const auto &f : function_map)
    if(f.second.first_loc.is_not_nil())
      entry_locs[f.second.first_loc]=f.first;

  irep_idt function;

  for(unsigned l=0; l<loc_vector.size(); l++)
  {
    auto f_it=entry_locs.find(loc_reft(l));
    if(f_it!=entry_locs.end())
    {
      function=f_it->second;
      out << "*** " << function << "\n";
    }

    const loct &loc=loc_vector[l];

    out << "  L" << l << ": ";
    //        << loc.target->type << " "
    //        << loc.target->location

    if(loc.target->is_goto())
    {
      if(loc.target->guard.is_true())
        out << "GOTO " << loc.branch_target;
      else
        out << "IF " << from_expr(ns, function, loc.target->guard)
            << " THEN GOTO " << loc.branch_target;
    }
    else
    {
      out << as_string(ns, *loc.target);
    }

    out << '\n';
  }

  out << "\n";
  out << "The entry location is L" << entry_loc << ".\n";
}
