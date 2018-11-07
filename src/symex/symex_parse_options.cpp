/*******************************************************************\

Module: Symex Command Line Options Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symex Command Line Options Processing

#include "symex_parse_options.h"

#include <iostream>
#include <fstream>
#include <cstdlib>

#include <util/config.h>
#include <util/exception_utils.h>
#include <util/memory_info.h>
#include <util/options.h>
#include <util/string2int.h>
#include <util/unicode.h>
#include <util/version.h>

#include <ansi-c/ansi_c_language.h>
#include <ansi-c/cprover_library.h>
#include <cpp/cpp_language.h>

#include <goto-programs/adjust_float_expressions.h>
#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/goto_trace.h>
#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/instrument_preconditions.h>
#include <goto-programs/json_goto_trace.h>
#include <goto-programs/link_to_library.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/remove_complex.h>
#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/remove_returns.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/remove_unused_functions.h>
#include <goto-programs/remove_vector.h>
#include <goto-programs/remove_virtual_functions.h>
#include <goto-programs/rewrite_union.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/show_symbol_table.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/xml_goto_trace.h>

#include <goto-instrument/cover.h>

#include <langapi/mode.h>

#include "path_search.h"

symex_parse_optionst::symex_parse_optionst(int argc, const char **argv):
  parse_options_baset(SYMEX_OPTIONS, argc, argv),
  messaget(ui_message_handler),
  ui_message_handler(cmdline, std::string("Symex ") + CBMC_VERSION)
{
}

void symex_parse_optionst::eval_verbosity()
{
  // this is our default verbosity
  int v=messaget::M_STATISTICS;

  if(cmdline.isset("verbosity"))
  {
    v=unsafe_string2int(cmdline.get_value("verbosity"));
    if(v<0)
      v=0;
    else if(v>10)
      v=10;
  }

  ui_message_handler.set_verbosity(v);
}

void symex_parse_optionst::get_command_line_options(optionst &options)
{
  if(config.set(cmdline))
  {
    usage_error();
    exit(1);
  }

  if(cmdline.isset("debug-level"))
    options.set_option("debug-level", cmdline.get_value("debug-level"));

  if(cmdline.isset("unwindset"))
    options.set_option("unwindset", cmdline.get_value("unwindset"));

  // all checks supported by goto_check
  PARSE_OPTIONS_GOTO_CHECK(cmdline, options);

  // simplification in goto_check
  if(cmdline.isset("no-simplify"))
    options.set_option("simplify", false);
  else
    options.set_option("simplify", true);

  // check assertions
  if(cmdline.isset("no-assertions"))
    options.set_option("assertions", false);
  else
    options.set_option("assertions", true);

  // use assumptions
  if(cmdline.isset("no-assumptions"))
    options.set_option("assumptions", false);
  else
    options.set_option("assumptions", true);

  // magic error label
  if(cmdline.isset("error-label"))
    options.set_option("error-label", cmdline.get_values("error-label"));

  if(cmdline.isset("cover"))
    parse_cover_options(cmdline, options);
}

/// invoke main modules
int symex_parse_optionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << CBMC_VERSION << '\n';
    return 0;
  }

  register_language(new_ansi_c_language);
  register_language(new_cpp_language);

  //
  // command line options
  //

  optionst options;
  get_command_line_options(options);

  eval_verbosity();

  try
  {
    goto_model=initialize_goto_model(cmdline, get_message_handler(), options);
  }
  catch(const cprover_exception_baset &e)
  {
    error() << e.what() << messaget::eom;
    return 6;
  }
  catch(const std::string error_msg)
  {
    error() << error_msg << messaget::eom;
    return 6;
  }
  catch(const char *error_msg)
  {
    error() << error_msg << messaget::eom;
    return 6;
  }
  catch(...)
  {
    return 6;
  }

  if(cmdline.isset("show-symbol-table"))
  {
    show_symbol_table(goto_model, ui_message_handler);
    return 0;
  }

  if(process_goto_program(options))
    return 6;

  label_properties(goto_model);

  if(cmdline.isset("show-loops"))
  {
    show_loop_ids(get_ui(), goto_model);
    return 0;
  }

  if(cmdline.isset("show-goto-functions"))
  {
    show_goto_functions(goto_model, get_message_handler(), get_ui());
    return 0;
  }

  if(cmdline.isset("show-properties"))
  {
    show_properties(goto_model, get_message_handler(), get_ui());
    return 0;
  }

  if(set_properties())
    return 7;

  if(cmdline.isset("show-locs"))
  {
    const namespacet ns(goto_model.symbol_table);
    locst locs(ns);
    locs.build(goto_model.goto_functions);
    locs.output(std::cout);
    return 0;
  }

  // do actual Symex

  try
  {
    const namespacet ns(goto_model.symbol_table);
    path_searcht path_search(ns);

    path_search.set_message_handler(get_message_handler());

    if(cmdline.isset("depth"))
      path_search.set_depth_limit(
        unsafe_string2unsigned(cmdline.get_value("depth")));

    if(cmdline.isset("context-bound"))
      path_search.set_context_bound(
        unsafe_string2unsigned(cmdline.get_value("context-bound")));

    if(cmdline.isset("branch-bound"))
      path_search.set_branch_bound(
        unsafe_string2unsigned(cmdline.get_value("branch-bound")));

    if(cmdline.isset("unwind"))
      path_search.set_unwind_limit(
        unsafe_string2unsigned(cmdline.get_value("unwind")));

    path_search.set_unwinding_assertions(
      cmdline.isset("unwinding-assertions"));

    if(cmdline.isset("max-search-time"))
      path_search.set_time_limit(
        safe_string2unsigned(cmdline.get_value("max-search-time")));

    if(cmdline.isset("dfs"))
      path_search.set_dfs();

    if(cmdline.isset("bfs"))
      path_search.set_bfs();

    if(cmdline.isset("locs"))
      path_search.set_locs();

    if(cmdline.isset("show-vcc"))
    {
      path_search.show_vcc=true;
      path_search(goto_model.goto_functions);
      return 0;
    }

    path_search.eager_infeasibility=
      cmdline.isset("eager-infeasibility");

    path_search.stop_on_fail=
      cmdline.isset("stop-on-fail");

    if(cmdline.isset("cover"))
    {
      // test-suite generation
      path_search(goto_model.goto_functions);
      report_cover(path_search.property_map);
      return 0;
    }
    else
    {
      // do actual symex, for assertion checking
      switch(path_search(goto_model.goto_functions))
      {
      case safety_checkert::resultt::SAFE:
        report_properties(path_search.property_map);
        report_success();
        return 0;

      case safety_checkert::resultt::UNSAFE:
        report_properties(path_search.property_map);
        report_failure();
        return 10;

      default:
        return 8;
      }
    }
  }

  catch(const std::string error_msg)
  {
    error() << error_msg << messaget::eom;
    return 8;
  }

  catch(const char *error_msg)
  {
    error() << error_msg << messaget::eom;
    return 8;
  }

  #if 0
  // let's log some more statistics
  debug() << "Memory consumption:" << messaget::endl;
  memory_info(debug());
  debug() << eom;
  #endif
}

bool symex_parse_optionst::set_properties()
{
  try
  {
    if(cmdline.isset("property"))
      ::set_properties(
        goto_model.goto_functions, cmdline.get_values("property"));
  }

  catch(const char *e)
  {
    error() << e << eom;
    return true;
  }

  catch(const std::string e)
  {
    error() << e << eom;
    return true;
  }

  catch(int)
  {
    return true;
  }

  return false;
}

bool symex_parse_optionst::process_goto_program(const optionst &options)
{
  try
  {
    // we add the library
    link_to_library(goto_model, ui_message_handler, cprover_c_library_factory);

    // add generic checks
    status() << "Generic Property Instrumentation" << eom;
    goto_check(options, goto_model);

    // remove function pointers
    status() << "Removal of function pointers and virtual functions" << eom;
    remove_function_pointers(
      get_message_handler(),
      goto_model,
      cmdline.isset("pointer-check"));

    // Java virtual functions -> explicit dispatch tables:
    remove_virtual_functions(goto_model);

    // instrument library preconditions
    instrument_preconditions(goto_model);

    // remove more stuff
    remove_returns(goto_model);
    remove_complex(goto_model);
    remove_vector(goto_model);

    rewrite_union(goto_model);
    adjust_float_expressions(goto_model);

    // recalculate numbers, etc.
    goto_model.goto_functions.update();

    // add loop ids
    goto_model.goto_functions.compute_loop_numbers();

    if(cmdline.isset("drop-unused-functions"))
    {
      // Entry point will have been set before and function pointers removed
      status() << "Removing unused functions" << eom;
      remove_unused_functions(goto_model.goto_functions, ui_message_handler);
    }

    // remove skips such that trivial GOTOs are deleted and not considered
    // for coverage annotation:
    remove_skip(goto_model.goto_functions);

    if(cmdline.isset("cover"))
    {
      status() << "Instrumenting coverage goals" << eom;
      if(instrument_cover_goals(options, goto_model, get_message_handler()))
        return true;
    }
  }

  catch(const char *e)
  {
    error() << e << eom;
    return true;
  }

  catch(const std::string e)
  {
    error() << e << eom;
    return true;
  }

  catch(int)
  {
    return true;
  }

  catch(const std::bad_alloc &)
  {
    error() << "Out of memory" << eom;
    return true;
  }

  return false;
}

void symex_parse_optionst::report_properties(
  const path_searcht::property_mapt &property_map)
{
  if(get_ui()==ui_message_handlert::uit::PLAIN)
    status() << "\n** Results:" << eom;

  for(const auto &p : property_map)
  {
    if(get_ui()==ui_message_handlert::uit::XML_UI)
    {
      xmlt xml_result("result");
      xml_result.set_attribute("claim", id2string(p.first));

      std::string status_string;

      switch(p.second.status)
      {
      case path_searcht::SUCCESS: status_string="SUCCESS"; break;
      case path_searcht::FAILURE: status_string="FAILURE"; break;
      case path_searcht::NOT_REACHED: status_string="SUCCESS"; break;
      }

      xml_result.set_attribute("status", status_string);

      std::cout << xml_result << "\n";
    }
    else
    {
      status() << "[" << p.first << "] "
               << p.second.description << ": ";
      switch(p.second.status)
      {
      case path_searcht::SUCCESS: status() << green << "SUCCESS" << reset; break;
      case path_searcht::FAILURE: status() << red << "FAILURE" << reset; break;
      case path_searcht::NOT_REACHED: status() << yellow << "SUCCESS" << reset << " (not reached)"; break;
      }
      status() << eom;
    }

    if((cmdline.isset("show-trace") ||
        cmdline.isset("trace") ||
        cmdline.isset("stack-trace") ||
        cmdline.isset("xml-ui") ||
        cmdline.isset("stop-on-fail")) &&
       p.second.is_failure())
    {
      optionst options;
      PARSE_OPTIONS_GOTO_TRACE(cmdline, options);
      show_trace(p.first, p.second.error_trace, options);
    }
  }

  if(!cmdline.isset("property"))
  {
    status() << eom;

    unsigned failed=0;

    for(const auto &p : property_map)
      if(p.second.is_failure())
        failed++;

    status() << "** " << failed
             << " of " << property_map.size() << " failed"
             << eom;
  }
}

void symex_parse_optionst::report_success()
{
  result() << bold << "VERIFICATION SUCCESSFUL" << reset << eom;

  switch(get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
    break;

  case ui_message_handlert::uit::XML_UI:
    {
      xmlt xml("cprover-status");
      xml.data="SUCCESS";
      std::cout << xml;
      std::cout << '\n';
    }
    break;

  default:
    UNREACHABLE;
  }
}

void symex_parse_optionst::show_trace(
  const irep_idt &property,
  const goto_tracet &error_trace,
  const optionst &options)
{
  const namespacet ns(goto_model.symbol_table);
  trace_optionst trace_options(options);

  switch(get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
    result() << '\n' << "Trace for " << property
             << ":" << '\n';
    show_goto_trace(result(), ns, error_trace, trace_options);
    result() << eom;
    break;

  case ui_message_handlert::uit::XML_UI:
    {
      xmlt xml;
      convert(ns, error_trace, xml);
      std::cout << xml << std::flush;
    }
    break;

  case ui_message_handlert::uit::JSON_UI:
    {
      json_stream_objectt &json_result =
        ui_message_handler.get_json_stream().push_back_stream_object();
      const goto_trace_stept &step=error_trace.steps.back();
      json_result["property"] =
        json_stringt(step.pc->source_location.get_property_id());
      json_result["description"] =
        json_stringt(step.pc->source_location.get_comment());
      json_result["status"]=json_stringt("failed");
      json_stream_arrayt &json_trace =
        json_result.push_back_stream_array("trace");
      convert<json_stream_arrayt>(ns, error_trace, json_trace, trace_options);
    }
    break;

  default:
    UNREACHABLE;
  }
}

void symex_parse_optionst::report_failure()
{
  result() << bold << "VERIFICATION FAILED" << reset << eom;

  switch(get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
    break;

  case ui_message_handlert::uit::XML_UI:
    {
      xmlt xml("cprover-status");
      xml.data="FAILURE";
      std::cout << xml;
      std::cout << '\n';
    }
    break;

  case ui_message_handlert::uit::JSON_UI:
    {
      json_objectt json_result;
      json_result["cProverStatus"]=json_stringt("failure");
      result() << json_result;
    }
    break;

  default:
    UNREACHABLE;
  }
}

/// display command line help
void symex_parse_optionst::help()
{
  std::cout <<
    '\n' << banner_string("Symex", CBMC_VERSION) << '\n';

  std::cout <<
    "* *                    Daniel Kroening                      * *\n"
    "* *                 University of Oxford                    * *\n"
    "* *                 kroening@kroening.com                   * *\n"
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " symex [-?] [-h] [--help]     show help\n"
    " symex file.c ...             source file names\n"
    "\n"
    "Analysis options:\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --show-properties            show the properties, but don't run analysis\n"
    " --property id                only check one specific property\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --stop-on-fail               stop analysis once a failed property is detected\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --trace                      give a counterexample trace for failed properties\n"
    "\n"
    "Frontend options:\n"
    " -I path                      set include path (C/C++)\n"
    " -D macro                     define preprocessor macro (C/C++)\n"
    " --preprocess                 stop after preprocessing\n"
    " --16, --32, --64             set width of int\n"
    " --LP64, --ILP64, --LLP64,\n"
    "   --ILP32, --LP32            set width of int, long and pointers\n"
    " --little-endian              allow little-endian word-byte conversions\n"
    " --big-endian                 allow big-endian word-byte conversions\n"
    " --unsigned-char              make \"char\" unsigned by default\n"
    " --show-parse-tree            show parse tree\n"
    " --show-symbol-table          show symbol table\n"
    HELP_SHOW_GOTO_FUNCTIONS
    " --drop-unused-functions      drop functions trivially unreachable from main function\n" // NOLINT(*)
    " --ppc-macos                  set MACOS/PPC architecture\n"
    " --mm model                   set memory model (default: sc)\n"
    " --arch                       set architecture (default: "
                                   << configt::this_architecture() << ")\n"
    " --os                         set operating system (default: "
                                   << configt::this_operating_system() << ")\n"
    #ifdef _WIN32
    " --gcc                        use GCC as preprocessor\n"
    #endif
    " --no-arch                    don't set up an architecture\n"
    " --no-library                 disable built-in abstract C library\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --round-to-nearest           IEEE floating point rounding mode (default)\n"
    " --round-to-plus-inf          IEEE floating point rounding mode\n"
    " --round-to-minus-inf         IEEE floating point rounding mode\n"
    " --round-to-zero              IEEE floating point rounding mode\n"
    HELP_FUNCTIONS
    "\n"
    "Program instrumentation options:\n"
    HELP_GOTO_CHECK
    " --no-assertions              ignore user assertions\n"
    " --no-assumptions             ignore user assumptions\n"
    " --error-label label          check that label is unreachable\n"
    "\n"
    "Symex options:\n"
    " --unwind nr                  unwind nr times\n"
    " --depth nr                   limit search depth\n"
    " --context-bound nr           limit number of context switches\n"
    " --branch-bound nr            limit number of branches taken\n"
    " --max-search-time s          limit search to approximately s seconds\n"
    " --dfs                        use depth first search\n"
    " --bfs                        use breadth first search\n"
    " --eager-infeasibility        query solver early to determine whether a path is infeasible before searching it\n" // NOLINT(*)
    "\n"
    "Other options:\n"
    " --version                    show version and exit\n"
    " --xml-ui                     use XML-formatted output\n"
    " --verbosity #                verbosity level\n"
    "\n";
}
