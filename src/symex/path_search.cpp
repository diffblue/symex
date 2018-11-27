/*******************************************************************\

Module: Path-based Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Path-based Symbolic Execution

#include "path_search.h"

#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>

#include "../path-symex/path_symex.h"
#include "../path-symex/build_goto_trace.h"

path_searcht::resultt path_searcht::operator()(
  const goto_functionst &goto_functions)
{
  path_symex_configt config(ns);
  config.set_message_handler(get_message_handler());
  config.locs.build(goto_functions);

  status() << "Starting symbolic simulation" << eom;

  // this is the container for the history-forest
  path_symex_historyt history;

  queue.push_back(config.initial_state());

  // set up the statistics
  number_of_dropped_states=0;
  number_of_paths=0;
  number_of_VCCs=0;
  number_of_steps=0;
  number_of_feasible_paths=0;
  number_of_infeasible_paths=0;
  number_of_VCCs_after_simplification=0;
  number_of_failed_properties=0;
  number_of_locs=config.locs.size();

  // stop the time
  start_time=std::chrono::steady_clock::now();
  auto last_reported_time=start_time;

  initialize_property_map(goto_functions);

  while(!queue.empty())
  {
    number_of_steps++;

    // Pick a state from the queue,
    // according to some heuristic.
    // The state moves to the head of the queue.
    pick_state();

    // move into temporary queue
    queuet tmp_queue;
    tmp_queue.splice(
      tmp_queue.begin(), queue, queue.begin(), ++queue.begin());

    try
    {
      statet &state=tmp_queue.front();

      // record we have seen it
      loc_data[state.pc().loc_number].visited=true;

      debug() << "Loc: #" << state.pc().loc_number
              << ", queue: " << queue.size()
              << ", depth: " << state.get_depth();
      for(const auto &s : queue)
        debug() << ' ' << s.get_depth();

      debug() << eom;

      // dead already?
      if(!state.is_executable())
      {
        goto_programt::const_targett pc=state.get_instruction();
        debug() << "path is dead at "
                << pc->source_location
                << " thread " << state.get_current_thread()
                << eom;
        number_of_paths++;
        continue;
      }

      // drop deliberately?
      if(drop_state(state))
      {
        number_of_dropped_states++;
        number_of_paths++;
        continue;
      }

      // check feasibility
      if(eager_infeasibility &&
         state.last_was_branch() &&
         !is_feasible(state))
      {
        number_of_infeasible_paths++;
        number_of_paths++;
        continue;
      }

      if(number_of_steps%10==0)
      {
        auto now=std::chrono::steady_clock::now();
        if(now>=last_reported_time+std::chrono::seconds(1))
        {
          last_reported_time=now;
          auto running_time=now-start_time;
          status() << "Queue " << queue.size()
                   << " thread " << state.get_current_thread()+1
                   << '/' << state.threads.size()
                   << " PC " << state.pc()
                   << " depth " << state.get_depth()
                   << " [" << number_of_steps << " steps, "
                   << std::chrono::duration<double>(running_time).count()
                   << "s]" << messaget::eom;
        }
      }

      // an error, possibly?
      if(state.get_instruction()->is_assert())
      {
        if(show_vcc)
          do_show_vcc(state);
        else
        {
          check_assertion(state);

          // all assertions failed?
          if(number_of_failed_properties==property_map.size())
            break;

          // do we stop on failure?
          if(number_of_failed_properties>=1 && stop_on_fail)
            break;
        }
      }

      // execute
      path_symex(state, tmp_queue);

      // put at head of main queue
      queue.splice(queue.begin(), tmp_queue);
    }
    catch(const std::string &e)
    {
      error() << e << eom;
      number_of_dropped_states++;
    }
    catch(const char *e)
    {
      error() << e << eom;
      number_of_dropped_states++;
    }
    catch(int)
    {
      number_of_dropped_states++;
    }
  }

  report_statistics();

  return number_of_failed_properties==0?resultt::SAFE:resultt::UNSAFE;
}

void path_searcht::report_statistics()
{
  std::size_t number_of_visited_locations=0;
  for(const auto &l : loc_data)
    if(l.visited)
      number_of_visited_locations++;

  #if 0
  for(std::size_t l=0; l<loc_data.size(); l++)
    if(!loc_data[l].visited)
      status() << "NV: " << l << eom;
  #endif

  // report a bit
  status() << "Number of visited locations: "
           << number_of_visited_locations << " (out of "
           << number_of_locs << ')' << messaget::eom;

  status() << "Number of dropped states: "
           << number_of_dropped_states << messaget::eom;

  status() << "Number of paths: "
           << number_of_paths << messaget::eom;

  status() << "Number of infeasible paths: "
           << number_of_infeasible_paths << messaget::eom;

  status() << "Generated " << number_of_VCCs << " VCC(s), "
           << number_of_VCCs_after_simplification
           << " remaining after simplification"
           << messaget::eom;

  auto total_time=std::chrono::steady_clock::now()-start_time;
  status() << "Runtime total: "
           << std::chrono::duration<double>(total_time).count()
           << "s\n"
              "Runtime decision procedure: "
           << std::chrono::duration<double>(solver_time).count()
           << "s" << messaget::eom;
}

void path_searcht::pick_state()
{
  switch(search_heuristic)
  {
  case search_heuristict::DFS:
    // Picking the first one (most recently added) is a DFS.
    return;

  case search_heuristict::BFS:
    // Picking the last one is a BFS.
    if(queue.size()>=2)
      // move last to first position
      queue.splice(queue.begin(), queue, --queue.end(), queue.end());
    return;

  case search_heuristict::LOCS:
    return;
  }
}

/// decide whether to drop an overwise viable state
bool path_searcht::drop_state(const statet &state)
{
  goto_programt::const_targett pc=state.get_instruction();

  const source_locationt &source_location=pc->source_location;

  if(!source_location.is_nil() &&
     last_source_location!=source_location)
  {
    debug() << "SYMEX at file " << source_location.get_file()
            << " line " << source_location.get_line()
            << " function " << source_location.get_function()
            << eom;

    last_source_location=source_location;
  }

  // depth limit
  if(state.get_depth()>=depth_limit)
    return true;

  // context bound
  if(state.get_no_thread_interleavings()>=context_bound)
    return true;

  // branch bound
  if(state.get_no_branches()>=branch_bound)
    return true;

  // unwinding limit -- loops
  if(unwind_limit!=std::numeric_limits<unsigned>::max() &&
     pc->is_backwards_goto())
  {
    bool stop=false;

    for(const auto &loop_info : state.unwinding_map)
      if(loop_info.second>=unwind_limit)
      {
        stop=true;
        break;
      }

    const irep_idt id=goto_programt::loop_id(*pc);
    path_symex_statet::unwinding_mapt::const_iterator entry=
      state.unwinding_map.find(state.pc());
    debug() << (stop?"Not unwinding":"Unwinding")
      << " loop " << id << " iteration "
      << (entry==state.unwinding_map.end()?1:entry->second)
      << " (" << unwind_limit << " max)"
      << " " << source_location
      << " thread " << state.get_current_thread() << eom;

    if(stop && unwinding_assertions && is_feasible(state))
    {
      // record that failure
      status() << "Unwinding assertion failed: " << id << eom;
      irep_idt property=id2string(pc->function)+".unwind."+
                        std::to_string(pc->loop_number);
      auto &p=property_map[property];
      if(p.description.empty())
      {
        p.source_location=pc->source_location;
        p.description="unwinding assertion loop "+std::to_string(pc->loop_number);
        number_of_failed_properties++;
        p.status=FAILURE;
      }
    }

    if(stop)
      return true;
  }

  // unwinding limit -- recursion
  if(unwind_limit!=std::numeric_limits<unsigned>::max() &&
     pc->is_function_call())
  {
    exprt function=to_code_function_call(pc->code).function();
    const irep_idt id=function.get(ID_identifier); // could be nil
    path_symex_statet::recursion_mapt::const_iterator entry=
      state.recursion_map.find(id);

    if(entry!=state.recursion_map.end() &&
       entry->second!=0)
    {
      const bool stop=entry->second>=unwind_limit;

      debug() << (stop?"Not unwinding":"Unwinding")
        << " recursion " << id << " iteration "
        << entry->second+1
        << " (" << unwind_limit << " max)"
        << " " << source_location
        << " thread " << state.get_current_thread() << eom;

      if(stop)
        return true;
    }
  }

  // search time limit (--max-search-time)
  if(time_limit!=std::numeric_limits<unsigned>::max() &&
     std::chrono::steady_clock::now()>start_time+std::chrono::seconds(time_limit))
    return true;

  return false;
}

void path_searcht::check_assertion(statet &state)
{
  const goto_programt::instructiont &instruction=
    *state.get_instruction();

  PRECONDITION(instruction.is_assert());

  // keep statistics
  number_of_VCCs++;

  irep_idt property_name=instruction.source_location.get_property_id();
  property_entryt &property_entry=property_map[property_name];

  if(property_entry.status==FAILURE)
    return; // already failed
  else if(property_entry.status==NOT_REACHED)
    property_entry.status=SUCCESS; // well, for now!

  // the assertion in SSA
  exprt assertion=
    state.read(instruction.guard);

  if(assertion.is_true())
    return; // no error, trivially

  // keep statistics
  number_of_VCCs_after_simplification++;

  status() << "Checking property " << property_name << eom;

  // take the time
  auto solver_start_time=std::chrono::steady_clock::now();

  satcheckt satcheck;
  bv_pointerst bv_pointers(ns, satcheck);

  satcheck.set_message_handler(get_message_handler());
  bv_pointers.set_message_handler(get_message_handler());

  if(!state.check_assertion(bv_pointers))
  {
    property_entry.error_trace=build_goto_trace(state, bv_pointers);

    // add the assertion
    goto_trace_stept trace_step;

    trace_step.pc=state.get_instruction();
    trace_step.thread_nr=state.get_current_thread();
    trace_step.step_nr=property_entry.error_trace.steps.size();
    trace_step.type=goto_trace_stept::typet::ASSERT;

    const irep_idt &comment=
      instruction.source_location.get_comment();

    if(!comment.empty())
      trace_step.comment=id2string(comment);
    else
      trace_step.comment="assertion";

    property_entry.error_trace.add_step(trace_step);

    property_entry.status=FAILURE;
    number_of_failed_properties++;
  }

  solver_time+=std::chrono::steady_clock::now()-solver_start_time;
}

bool path_searcht::is_feasible(const statet &state)
{
  status() << "Feasibility check" << eom;

  // take the time
  auto solver_start_time=std::chrono::steady_clock::now();

  satcheckt satcheck;
  bv_pointerst bv_pointers(ns, satcheck);

  satcheck.set_message_handler(get_message_handler());
  bv_pointers.set_message_handler(get_message_handler());

  bool result=state.is_feasible(bv_pointers);

  solver_time+=std::chrono::steady_clock::now()-solver_start_time;

  return result;
}

void path_searcht::initialize_property_map(
  const goto_functionst &goto_functions)
{
  forall_goto_functions(it, goto_functions)
    if(!it->second.is_inlined())
    {
      const goto_programt &goto_program=it->second.body;

      forall_goto_program_instructions(i_it, goto_program)
      {
        if(!i_it->is_assert())
          continue;

        const source_locationt &source_location=i_it->source_location;

        irep_idt property_name=source_location.get_property_id();

        property_entryt &property_entry=property_map[property_name];
        property_entry.status=NOT_REACHED;
        property_entry.description=source_location.get_comment();
        property_entry.source_location=source_location;
      }
    }
}
