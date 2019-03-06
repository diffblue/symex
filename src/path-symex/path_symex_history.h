/*******************************************************************\

Module: History for path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// History for path-based symbolic simulator

#ifndef CPROVER_PATH_SYMEX_PATH_SYMEX_HISTORY_H
#define CPROVER_PATH_SYMEX_PATH_SYMEX_HISTORY_H

#include <limits>

#include <util/base_exceptions.h>
#include <util/std_expr.h>
#include <util/variant.h>

#include "goto-locs/loc_ref.h"

class path_symex_stept;

// This is a reference to a path_symex_stept,
// and is really cheap to copy. These references are stable,
// even though the underlying vector is not.
class path_symex_step_reft
{
public:
  explicit path_symex_step_reft(
    class path_symex_historyt &_history):
    index(std::numeric_limits<std::size_t>::max()),
    history(&_history)
  {
  }

  path_symex_step_reft():
    index(std::numeric_limits<std::size_t>::max()), history(nullptr)
  {
  }

  bool is_nil() const
  {
    return index==std::numeric_limits<std::size_t>::max();
  }

  path_symex_historyt &get_history() const
  {
    INVARIANT_STRUCTURED(
      history!=nullptr, nullptr_exceptiont, "history is null");
    return *history;
  }

  // pre-decrement
  path_symex_step_reft &operator--();

  path_symex_stept &operator*() const { return get(); }
  path_symex_stept *operator->() const { return &get(); }

  template<typename T>
  void generate_successor(T variant);

  // build a forward-traversable version of the history
  void build_history(std::vector<path_symex_step_reft> &dest) const;

protected:
  // we use a vector to store all steps
  std::size_t index;
  class path_symex_historyt *history;

  path_symex_stept &get() const;
};

class decision_proceduret;

// the actual history node
class path_symex_stept
{
public:
  struct othert
  {
  };

  struct assumet
  {
    exprt ssa_cond;
  };

  struct brancht
  {
    bool taken;
    exprt ssa_cond;
  };

  struct callt
  {
    irep_idt called_function;
    struct function_argumentt { symbol_exprt ssa_lhs; exprt ssa_rhs; };
    std::vector<function_argumentt> function_arguments;
  };

  struct assignt
  {
    // pre SSA, but dereferenced
    exprt lhs;

    // in SSA
    exprt ssa_guard;
    symbol_exprt ssa_lhs;
    exprt ssa_rhs;
  };

  bool is_branch() const
  {
    return holds_alternative<brancht>(variant);
  }

  bool is_assume() const
  {
    return holds_alternative<assumet>(variant);
  }

  bool is_assign() const
  {
    return holds_alternative<assignt>(variant);
  }

  bool is_call() const
  {
    return holds_alternative<callt>(variant);
  }

  variant<assignt, assumet, brancht, callt, othert> variant;

  const assignt &assign() const
  {
    return get<assignt>(variant);
  }

  assignt &assign()
  {
    return get<assignt>(variant);
  }

  const assumet &assume() const
  {
    return get<assumet>(variant);
  }

  assumet &assume()
  {
    return get<assumet>(variant);
  }

  const callt &call() const
  {
    return get<callt>(variant);
  }

  callt &call()
  {
    return get<callt>(variant);
  }

  const brancht &branch() const
  {
    return get<brancht>(variant);
  }

  brancht &branch()
  {
    return get<brancht>(variant);
  }

  path_symex_step_reft predecessor;

  // the thread that did the step
  unsigned thread_nr = 0;

  // the instruction that was executed
  loc_reft pc;
  irep_idt f_identifier;

  bool hidden = false;

  template<typename T>
  explicit path_symex_stept(T _variant):variant(std::move(_variant))
  {
  }

  // interface to solvers; this converts a single step
  void convert(decision_proceduret &dest) const;

  void output(std::ostream &) const;
};

// converts the full history
inline decision_proceduret &operator<<(
  decision_proceduret &dest,
  path_symex_step_reft src)
{
  while(!src.is_nil())
  {
    src->convert(dest);
    --src;
  }

  return dest;
}

// this stores the forest of histories
class path_symex_historyt
{
public:
  typedef std::vector<path_symex_stept> step_containert;
  step_containert step_container;

  // TODO: consider typedefing path_symex_historyt
  void clear()
  {
    step_container.clear();
  }
};

template<typename T>
inline void path_symex_step_reft::generate_successor(T variant)
{
  INVARIANT_STRUCTURED(
    history!=nullptr, nullptr_exceptiont, "history is null");
  path_symex_step_reft old=*this;
  index=history->step_container.size();
  history->step_container.push_back(path_symex_stept(std::move(variant)));
  history->step_container.back().predecessor=old;
}

inline path_symex_step_reft &path_symex_step_reft::operator--()
{
  *this=get().predecessor;
  return *this;
}

inline path_symex_stept &path_symex_step_reft::get() const
{
  INVARIANT_STRUCTURED(
    history!=nullptr, nullptr_exceptiont, "history is null");
  PRECONDITION(!is_nil());
  return history->step_container[index];
}

#endif // CPROVER_PATH_SYMEX_PATH_SYMEX_HISTORY_H
