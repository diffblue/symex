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

#include <util/string2int.h>
#include <util/config.h>
#include <util/options.h>
#include <util/memory_info.h>
#include <util/unicode.h>

#include <ansi-c/ansi_c_language.h>
#include <cpp/cpp_language.h>
#include <java_bytecode/java_bytecode_language.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/instrument_preconditions.h>
#include <goto-programs/link_to_library.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/remove_complex.h>
#include <goto-programs/remove_exceptions.h>
#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/remove_instanceof.h>
#include <goto-programs/remove_returns.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/remove_unused_functions.h>
#include <goto-programs/remove_vector.h>
#include <goto-programs/remove_virtual_functions.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/show_symbol_table.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/xml_goto_trace.h>

#include <goto-symex/rewrite_union.h>
#include <goto-symex/adjust_float_expressions.h>

#include <goto-instrument/cover.h>

#include <langapi/mode.h>

#include <cbmc/version.h>

#include <path-symex/locs.h>

#include "path_search.h"
#include "shortest_path_graph.h"

symex_parse_optionst::symex_parse_optionst(int argc, const char **argv):
  parse_options_baset(SYMEX_OPTIONS, argc, argv),
  messaget(ui_message_handler),
  ui_message_handler(cmdline, "Symex " CBMC_VERSION)
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
  register_language(new_java_bytecode_language);

  //
  // command line options
  //

  optionst options;
  get_command_line_options(options);

  eval_verbosity();

  try
  {
    goto_model=initialize_goto_model(cmdline, get_message_handler());
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
    show_symbol_table(goto_model, ui_message_handler.get_ui());
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
    show_properties(goto_model, get_ui());
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

  if(cmdline.isset("show-distances-to-property"))
  {
    const namespacet ns(goto_model.symbol_table);
    locst locs(ns);
    locs.build(goto_model.goto_functions);

    shortest_path_grapht path_search_graph(goto_model.goto_functions, locs);

    locs.output_reachable(std::cout);
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

    if(cmdline.isset("max-search-time"))
      path_search.set_time_limit(
        safe_string2unsigned(cmdline.get_value("max-search-time")));

    if(cmdline.isset("dfs"))
    {
      if(cmdline.isset("randomize"))
        path_search.set_randomized_dfs();
      else
        path_search.set_dfs();
    }

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
    link_to_library(goto_model, ui_message_handler);

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

    // Java throw and catch -> explicit exceptional return variables:
    // This introduces instanceof, so order is important:
    remove_exceptions(goto_model);
    // Java instanceof -> clsid comparison:
    remove_instanceof(goto_model);
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

  catch(std::bad_alloc)
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

  for(path_searcht::property_mapt::const_iterator
      it=property_map.begin();
      it!=property_map.end();
      it++)
  {
    if(get_ui()==ui_message_handlert::uit::XML_UI)
    {
      xmlt xml_result("result");
      xml_result.set_attribute("claim", id2string(it->first));

      std::string status_string;

      switch(it->second.status)
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
      status() << "[" << it->first << "] "
               << it->second.description << ": ";
      switch(it->second.status)
      {
      case path_searcht::SUCCESS: status() << "SUCCESS"; break;
      case path_searcht::FAILURE: status() << "FAILURE"; break;
      case path_searcht::NOT_REACHED: status() << "SUCCESS"; break;
      }
      status() << eom;
    }

    if((cmdline.isset("show-trace") ||
        cmdline.isset("trace") ||
        cmdline.isset("stop-on-fail")) &&
       it->second.is_failure())
      show_trace(it->first, it->second.error_trace);
  }

  if(!cmdline.isset("property"))
  {
    status() << eom;

    unsigned failed=0;

    for(path_searcht::property_mapt::const_iterator
        it=property_map.begin();
        it!=property_map.end();
        it++)
      if(it->second.is_failure())
        failed++;

    status() << "** " << failed
             << " of " << property_map.size() << " failed"
             << eom;
  }
}

void symex_parse_optionst::report_success()
{
  result() << "VERIFICATION SUCCESSFUL" << eom;

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
  const goto_tracet &error_trace)
{
  const namespacet ns(goto_model.symbol_table);

  switch(get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
    std::cout << '\n' << "Trace for " << property
              << ":" << '\n';
    show_goto_trace(std::cout, ns, error_trace);
    break;

  case ui_message_handlert::uit::XML_UI:
    {
      xmlt xml;
      convert(ns, error_trace, xml);
      std::cout << xml << std::flush;
    }
    break;

  default:
    UNREACHABLE;
  }
}

void symex_parse_optionst::report_failure()
{
  result() << "VERIFICATION FAILED" << eom;

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

  default:
    UNREACHABLE;
  }
}

/// display command line help
void symex_parse_optionst::help()
{
  std::cout <<
    "\n"
    "* *     Symex " CBMC_VERSION " - Copyright (C) 2013 ";

  std::cout << "(" << (sizeof(void *)*8) << "-bit version)";

  std::cout << "     * *\n";

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
    "Java Bytecode frontend options:\n"
    JAVA_BYTECODE_LANGUAGE_OPTIONS_HELP
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
    " --randomize                  used in conjunction with dfs, to search by randomized dfs\n" // NOLINT(*)
    " --eager-infeasibility        query solver early to determine whether a path is infeasible before searching it\n" // NOLINT(*)
    "\n"
    "Other options:\n"
    " --show-distances-to-property\n"
    "                              shows the (context free) shortest path from every reachable program location to a single property" // NOLINT(*)
    " --version                    show version and exit\n"
    " --xml-ui                     use XML-formatted output\n"
    " --verbosity #                verbosity level\n"
    "\n";
}
