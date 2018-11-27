/*******************************************************************\

Module: JBMC Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// JBMC Command Line Option Processing

#include "jsymex_parse_options.h"

#include <cstdlib> // exit()
#include <fstream>
#include <iostream>
#include <memory>

#include <util/config.h>
#include <util/exit_codes.h>
#include <util/invariant.h>
#include <util/unicode.h>
#include <util/version.h>
#include <util/xml.h>

#include <langapi/language.h>

#include <ansi-c/ansi_c_language.h>

#include <goto-programs/adjust_float_expressions.h>
#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/instrument_preconditions.h>
#include <goto-programs/lazy_goto_model.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/remove_asm.h>
#include <goto-programs/remove_returns.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/remove_unused_functions.h>
#include <goto-programs/remove_virtual_functions.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/show_goto_functions.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/show_symbol_table.h>

#include <goto-instrument/full_slicer.h>
#include <goto-instrument/nondet_static.h>
#include <goto-instrument/reachability_slicer.h>

#include <linking/static_lifetime_init.h>

#include <pointer-analysis/add_failed_symbols.h>

#include <langapi/mode.h>

#include "../goto-locs/locs.h"
#include "../symex/path_search.h"
#include <ansi-c/cprover_library.h>
#include <goto-instrument/cover.h>
#include <goto-programs/link_to_library.h>
#include <goto-programs/remove_complex.h>
#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/remove_vector.h>
#include <goto-programs/rewrite_union.h>
#include <goto-programs/xml_goto_trace.h>
#include <iomanip>
#include <java_bytecode/convert_java_nondet.h>
#include <java_bytecode/java_bytecode_language.h>
#include <java_bytecode/java_enum_static_init_unwind_handler.h>
#include <java_bytecode/remove_exceptions.h>
#include <java_bytecode/remove_instanceof.h>
#include <java_bytecode/remove_java_new.h>
#include <java_bytecode/replace_java_nondet.h>
#include <java_bytecode/simple_method_stubbing.h>
#include <langapi/language_util.h>
#include <util/json_expr.h>
#include <util/string2int.h>
#include <util/xml_expr.h>

jsymex_parse_optionst::jsymex_parse_optionst(int argc, const char **argv)
    : parse_options_baset(JSYMEX_OPTIONS, argc, argv),
      messaget(ui_message_handler),
      ui_message_handler(cmdline, std::string("JBMC ") + CBMC_VERSION),
      path_strategy_chooser() {}

::jsymex_parse_optionst::jsymex_parse_optionst(int argc, const char **argv,
                                               const std::string &extra_options)
    : parse_options_baset(JSYMEX_OPTIONS + extra_options, argc, argv),
      messaget(ui_message_handler),
      ui_message_handler(cmdline, std::string("JBMC ") + CBMC_VERSION),
      path_strategy_chooser() {}

void jsymex_parse_optionst::set_default_options(optionst &options) {
  // Default true
  options.set_option("assertions", true);
  options.set_option("assumptions", true);
  options.set_option("built-in-assertions", true);
  options.set_option("lazy-methods", true);
  options.set_option("pretty-names", true);
  options.set_option("propagation", true);
  options.set_option("refine-strings", true);
  options.set_option("sat-preprocessor", true);
  options.set_option("simplify", true);
  options.set_option("simplify-if", true);

  // Other default
  options.set_option("arrays-uf", "auto");
}

void jsymex_parse_optionst::get_command_line_options(optionst &options) {
  if (config.set(cmdline)) {
    usage_error();
    exit(1); // should contemplate EX_USAGE from sysexits.h
  }

  jsymex_parse_optionst::set_default_options(options);
  parse_java_language_options(cmdline, options);
  parse_object_factory_options(cmdline, options);

  if (cmdline.isset("show-symex-strategies")) {
    std::cout << path_strategy_chooser.show_strategies();
    exit(CPROVER_EXIT_SUCCESS);
  }

  path_strategy_chooser.set_path_strategy_options(cmdline, options, *this);

  if (cmdline.isset("program-only"))
    options.set_option("program-only", true);

  if (cmdline.isset("show-vcc"))
    options.set_option("show-vcc", true);

  if (cmdline.isset("nondet-static"))
    options.set_option("nondet-static", true);

  if (cmdline.isset("no-simplify"))
    options.set_option("simplify", false);

  if (cmdline.isset("stop-on-fail") || cmdline.isset("dimacs") ||
      cmdline.isset("outfile"))
    options.set_option("stop-on-fail", true);

  if (cmdline.isset("trace") || cmdline.isset("stack-trace") ||
      cmdline.isset("stop-on-fail"))
    options.set_option("trace", true);

  if (cmdline.isset("localize-faults"))
    options.set_option("localize-faults", true);
  if (cmdline.isset("localize-faults-method")) {
    options.set_option("localize-faults-method",
                       cmdline.get_value("localize-faults-method"));
  }

  if (cmdline.isset("unwind"))
    options.set_option("unwind", cmdline.get_value("unwind"));

  if (cmdline.isset("depth"))
    options.set_option("depth", cmdline.get_value("depth"));

  if (cmdline.isset("debug-level"))
    options.set_option("debug-level", cmdline.get_value("debug-level"));

  if (cmdline.isset("slice-by-trace"))
    options.set_option("slice-by-trace", cmdline.get_value("slice-by-trace"));

  if (cmdline.isset("unwindset"))
    options.set_option("unwindset", cmdline.get_value("unwindset"));

  // constant propagation
  if (cmdline.isset("no-propagation"))
    options.set_option("propagation", false);

  // transform self loops to assumptions
  options.set_option("self-loops-to-assumptions",
                     !cmdline.isset("no-self-loops-to-assumptions"));

  // all checks supported by goto_check
  PARSE_OPTIONS_GOTO_CHECK(cmdline, options);

  // unwind loops in java enum static initialization
  if (cmdline.isset("java-unwind-enum-static"))
    options.set_option("java-unwind-enum-static", true);

  // check assertions
  if (cmdline.isset("no-assertions"))
    options.set_option("assertions", false);

  // use assumptions
  if (cmdline.isset("no-assumptions"))
    options.set_option("assumptions", false);

  // generate unwinding assertions
  if (cmdline.isset("unwinding-assertions"))
    options.set_option("unwinding-assertions", true);

  // generate unwinding assumptions otherwise
  options.set_option("partial-loops", cmdline.isset("partial-loops"));

  if (options.get_bool_option("partial-loops") &&
      options.get_bool_option("unwinding-assertions")) {
    error() << "--partial-loops and --unwinding-assertions "
            << "must not be given together" << eom;
    exit(1); // should contemplate EX_USAGE from sysexits.h
  }

  // remove unused equations
  options.set_option("slice-formula", cmdline.isset("slice-formula"));

  // simplify if conditions and branches
  if (cmdline.isset("no-simplify-if"))
    options.set_option("simplify-if", false);

  if (cmdline.isset("arrays-uf-always"))
    options.set_option("arrays-uf", "always");
  else if (cmdline.isset("arrays-uf-never"))
    options.set_option("arrays-uf", "never");

  if (cmdline.isset("dimacs"))
    options.set_option("dimacs", true);

  if (cmdline.isset("refine-arrays")) {
    options.set_option("refine", true);
    options.set_option("refine-arrays", true);
  }

  if (cmdline.isset("refine-arithmetic")) {
    options.set_option("refine", true);
    options.set_option("refine-arithmetic", true);
  }

  if (cmdline.isset("refine")) {
    options.set_option("refine", true);
    options.set_option("refine-arrays", true);
    options.set_option("refine-arithmetic", true);
  }

  if (cmdline.isset("no-refine-strings"))
    options.set_option("refine-strings", false);

  if (cmdline.isset("string-printable"))
    options.set_option("string-printable", true);

  if (cmdline.isset("no-refine-strings") && cmdline.isset("string-printable")) {
    warning() << "--string-printable ignored due to --no-refine-strings" << eom;
  }

  if (cmdline.isset("no-refine-strings") &&
      cmdline.isset("max-nondet-string-length")) {
    warning() << "--max-nondet-string-length ignored due to "
              << "--no-refine-strings" << eom;
  }

  if (cmdline.isset("max-node-refinement"))
    options.set_option("max-node-refinement",
                       cmdline.get_value("max-node-refinement"));

  // SMT Options

  if (cmdline.isset("smt1")) {
    error() << "--smt1 is no longer supported" << eom;
    exit(CPROVER_EXIT_USAGE_ERROR);
  }

  if (cmdline.isset("smt2"))
    options.set_option("smt2", true);

  if (cmdline.isset("fpa"))
    options.set_option("fpa", true);

  bool solver_set = false;

  if (cmdline.isset("boolector")) {
    options.set_option("boolector", true), solver_set = true;
    options.set_option("smt2", true);
  }

  if (cmdline.isset("mathsat")) {
    options.set_option("mathsat", true), solver_set = true;
    options.set_option("smt2", true);
  }

  if (cmdline.isset("cvc4")) {
    options.set_option("cvc4", true), solver_set = true;
    options.set_option("smt2", true);
  }

  if (cmdline.isset("yices")) {
    options.set_option("yices", true), solver_set = true;
    options.set_option("smt2", true);
  }

  if (cmdline.isset("z3")) {
    options.set_option("z3", true), solver_set = true;
    options.set_option("smt2", true);
  }

  if (cmdline.isset("smt2") && !solver_set) {
    if (cmdline.isset("outfile")) {
      // outfile and no solver should give standard compliant SMT-LIB
      options.set_option("generic", true);
    } else {
      // the default smt2 solver
      options.set_option("z3", true);
    }
  }

  if (cmdline.isset("beautify"))
    options.set_option("beautify", true);

  if (cmdline.isset("no-sat-preprocessor"))
    options.set_option("sat-preprocessor", false);

  options.set_option("pretty-names", !cmdline.isset("no-pretty-names"));

  if (cmdline.isset("outfile"))
    options.set_option("outfile", cmdline.get_value("outfile"));

  if (cmdline.isset("graphml-witness")) {
    options.set_option("graphml-witness", cmdline.get_value("graphml-witness"));
    options.set_option("stop-on-fail", true);
    options.set_option("trace", true);
  }

  if (cmdline.isset("symex-coverage-report"))
    options.set_option("symex-coverage-report",
                       cmdline.get_value("symex-coverage-report"));

  PARSE_OPTIONS_GOTO_TRACE(cmdline, options);

  if (cmdline.isset("no-lazy-methods"))
    options.set_option("lazy-methods", false);

  if (cmdline.isset("symex-driven-lazy-loading")) {
    options.set_option("symex-driven-lazy-loading", true);
    for (const char *opt : {"nondet-static", "full-slice", "reachability-slice",
                            "reachability-slice-fb"}) {
      if (cmdline.isset(opt)) {
        throw std::string("Option ") + opt +
            " can't be used with --symex-driven-lazy-loading";
      }
    }
  }

  // The 'allow-pointer-unsoundness' option prevents symex from throwing an
  // exception when it encounters pointers that are shared across threads.
  // This is unsound but given that pointers are ubiquitous in java this check
  // must be disabled in order to support the analysis of multithreaded java
  // code.
  if (cmdline.isset("java-threading"))
    options.set_option("allow-pointer-unsoundness", true);
}

bool jsymex_parse_optionst::process_goto_program(const optionst &options,
                                                 goto_modelt &goto_model) {
  try {
    // we add the library
    link_to_library(goto_model, ui_message_handler, cprover_c_library_factory);

    // add generic checks
    status() << "Generic Property Instrumentation" << eom;
    goto_check(options, goto_model);

    // remove function pointers
    status() << "Removal of function pointers and virtual functions" << eom;
    remove_function_pointers(get_message_handler(), goto_model,
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

    if (cmdline.isset("drop-unused-functions")) {
      // Entry point will have been set before and function pointers removed
      status() << "Removing unused functions" << eom;
      remove_unused_functions(goto_model.goto_functions, ui_message_handler);
    }

    // remove skips such that trivial GOTOs are deleted and not considered
    // for coverage annotation:
    remove_skip(goto_model.goto_functions);

    if (cmdline.isset("cover")) {
      status() << "Instrumenting coverage goals" << eom;
      if (instrument_cover_goals(options, goto_model, get_message_handler()))
        return true;
    }
  }

  catch (const char *e) {
    error() << e << eom;
    return true;
  }

  catch (const std::string e) {
    error() << e << eom;
    return true;
  }

  catch (int) {
    return true;
  }

  catch (const std::bad_alloc &) {
    error() << "Out of memory" << eom;
    return true;
  }

  return false;
}

int jsymex_parse_optionst::path_symex_main_procedure(goto_modelt &goto_model,
                                                     messaget *log,
                                                     bool show_locs,
                                                     cmdlinet &cmdline,
                                                     optionst &options) {

  if (cmdline.isset("show-symbol-table")) {
    show_symbol_table(goto_model, ui_message_handler);
    return 0;
  }

  if (process_goto_program(options, goto_model))
    return 6;

  if (cmdline.isset("show-loops")) {
    show_loop_ids(get_ui(), goto_model);
    return 0;
  }

  if (cmdline.isset("show-goto-functions")) {
    show_goto_functions(goto_model, get_message_handler(), get_ui());
    return 0;
  }

  if (cmdline.isset("show-properties")) {
    show_properties(goto_model, get_message_handler(), get_ui());
    return 0;
  }

  if (set_properties(goto_model))
    return 7;

  label_properties(goto_model);

  if (show_locs) {
    const namespacet ns(goto_model.symbol_table);
    locst locs(ns);
    locs.build(goto_model.goto_functions);
    locs.output(std::cout);
    return 0;
  }

  // do actual Symex

  try {
    const namespacet ns(goto_model.symbol_table);
    path_searcht path_search(ns);

    path_search.set_message_handler(log->get_message_handler());

    if (cmdline.isset("depth"))
      path_search.set_depth_limit(
          unsafe_string2unsigned(cmdline.get_value("depth")));

    if (cmdline.isset("context-bound"))
      path_search.set_context_bound(
          unsafe_string2unsigned(cmdline.get_value("context-bound")));

    if (cmdline.isset("branch-bound"))
      path_search.set_branch_bound(
          unsafe_string2unsigned(cmdline.get_value("branch-bound")));

    if (cmdline.isset("unwind"))
      path_search.set_unwind_limit(
          unsafe_string2unsigned(cmdline.get_value("unwind")));

    path_search.set_unwinding_assertions(cmdline.isset("unwinding-assertions"));

    if (cmdline.isset("max-search-time"))
      path_search.set_time_limit(
          safe_string2unsigned(cmdline.get_value("max-search-time")));

    if (cmdline.isset("dfs"))
      path_search.set_dfs();

    if (cmdline.isset("bfs"))
      path_search.set_bfs();

    if (cmdline.isset("locs"))
      path_search.set_locs();

    if (cmdline.isset("show-vcc")) {
      path_search.show_vcc = true;
      path_search(goto_model.goto_functions);
      return 0;
    }

    path_search.eager_infeasibility = cmdline.isset("eager-infeasibility");

    path_search.stop_on_fail = cmdline.isset("stop-on-fail");

    if (cmdline.isset("cover")) {
      // test-suite generation
      std::cout << "test-suite generation" << std::endl;
      path_search(goto_model.goto_functions);
      report_cover(path_search.property_map, goto_model.symbol_table);
      return 0;
    } else {
      std::cout << "Do actual symex for assertion checking" << std::endl;
      // do actual symex, for assertion checking
      switch (path_search(goto_model.goto_functions)) {
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

  catch (const std::string error_msg) {
    log->error() << error_msg << messaget::eom;
    return 8;
  }

  catch (const char *error_msg) {
    log->error() << error_msg << messaget::eom;
    return 8;
  }

#if 0
  // let's log some more statistics
  debug() << "Memory consumption:" << messaget::endl;
  memory_info(debug());
  debug() << eom;
#endif
}

/// invoke main modules
int jsymex_parse_optionst::doit() {
  if (cmdline.isset("version")) {
    std::cout << CBMC_VERSION << '\n';
    return 0; // should contemplate EX_OK from sysexits.h
  }

  eval_verbosity(cmdline.get_value("verbosity"), messaget::M_STATISTICS,
                 ui_message_handler);

  //
  // command line options
  //

  optionst options;
  try {
    get_command_line_options(options);
  }

  catch (const char *error_msg) {
    error() << error_msg << eom;
    return 6; // should contemplate EX_SOFTWARE from sysexits.h
  }

  catch (const std::string &error_msg) {
    error() << error_msg << eom;
    return 6; // should contemplate EX_SOFTWARE from sysexits.h
  }

  status() << "JBMCPS version " << CBMC_VERSION << " " << sizeof(void *) * 8
           << "-bit " << config.this_architecture() << " "
           << config.this_operating_system() << eom;

  // output the options
  switch (ui_message_handler.get_ui()) {
  case ui_message_handlert::uit::PLAIN:
    conditional_output(debug(), [&options](messaget::mstreamt &mstream) {
      mstream << "\nOptions: \n";
      options.output(mstream);
      mstream << messaget::eom;
    });
    break;
  case ui_message_handlert::uit::JSON_UI: {
    json_objectt json_options;
    json_options["options"] = options.to_json();
    debug() << json_options;
    break;
  }
  case ui_message_handlert::uit::XML_UI:
    debug() << options.to_xml();
    break;
  }

  register_language(new_ansi_c_language);
  register_language(new_java_bytecode_language);

  std::function<void(bmct &, const symbol_tablet &)> configure_bmc = nullptr;
  if (options.get_bool_option("java-unwind-enum-static")) {
    configure_bmc = [](bmct &bmc, const symbol_tablet &symbol_table) {
      bmc.add_loop_unwind_handler([&symbol_table](
          const goto_symex_statet::call_stackt &context, unsigned loop_number,
          unsigned unwind, unsigned &max_unwind) {
        return java_enum_static_init_unwind_handler(
            context, loop_number, unwind, max_unwind, symbol_table);
      });
    };
  }

  object_factory_params.set(options);

  stub_objects_are_not_null =
      options.get_bool_option("java-assume-inputs-non-null");

  std::unique_ptr<goto_modelt> goto_model_ptr;
  int get_goto_program_ret = get_goto_program(goto_model_ptr, options);
  if (get_goto_program_ret != -1)
    return get_goto_program_ret;

  goto_modelt &goto_model = *goto_model_ptr;

  if (cmdline.isset("show-properties")) {
    show_properties(goto_model, get_message_handler(),
                    ui_message_handler.get_ui());
    return 0; // should contemplate EX_OK from sysexits.h
  }

  if (set_properties(goto_model))
    return 7; // should contemplate EX_USAGE from sysexits.h

  return path_symex_main_procedure(goto_model, static_cast<messaget *>(this),
                                   false, cmdline, options);
}

bool jsymex_parse_optionst::set_properties(goto_modelt &goto_model) {
  try {
    if (cmdline.isset("property"))
      ::set_properties(goto_model, cmdline.get_values("property"));
  }

  catch (const char *e) {
    error() << e << eom;
    return true;
  }

  catch (const std::string &e) {
    error() << e << eom;
    return true;
  }

  catch (int) {
    return true;
  }

  return false;
}

int jsymex_parse_optionst::get_goto_program(
    std::unique_ptr<goto_modelt> &goto_model, const optionst &options) {
  if (cmdline.args.empty()) {
    error() << "Please provide a program to verify" << eom;
    return 6;
  }

  try {
    lazy_goto_modelt lazy_goto_model = lazy_goto_modelt::from_handler_object(
        *this, options, get_message_handler());
    lazy_goto_model.initialize(cmdline, options);

    class_hierarchy =
        util_make_unique<class_hierarchyt>(lazy_goto_model.symbol_table);

    // Show the class hierarchy
    if (cmdline.isset("show-class-hierarchy")) {
      show_class_hierarchy(*class_hierarchy, ui_message_handler);
      return CPROVER_EXIT_SUCCESS;
    }

    // Add failed symbols for any symbol created prior to loading any
    // particular function:
    add_failed_symbols(lazy_goto_model.symbol_table);

    status() << "Generating GOTO Program" << messaget::eom;
    lazy_goto_model.load_all_functions();

    // Show the symbol table before process_goto_functions mangles return
    // values, etc
    if (cmdline.isset("show-symbol-table")) {
      show_symbol_table(lazy_goto_model.symbol_table, ui_message_handler);
      return 0;
    } else if (cmdline.isset("list-symbols")) {
      show_symbol_table_brief(lazy_goto_model.symbol_table, ui_message_handler);
      return 0;
    }

    // Move the model out of the local lazy_goto_model
    // and into the caller's goto_model
    goto_model = lazy_goto_modelt::process_whole_model_and_freeze(
        std::move(lazy_goto_model));
    if (goto_model == nullptr)
      return 6;

    // show it?
    if (cmdline.isset("show-loops")) {
      show_loop_ids(ui_message_handler.get_ui(), *goto_model);
      return 0;
    }

    // show it?
    if (cmdline.isset("show-goto-functions") ||
        cmdline.isset("list-goto-functions")) {
      show_goto_functions(*goto_model, get_message_handler(),
                          ui_message_handler.get_ui(),
                          cmdline.isset("list-goto-functions"));
      return 0;
    }

    status() << config.object_bits_info() << eom;
  }

  catch (const char *e) {
    error() << e << eom;
    return 6;
  }

  catch (const std::string &e) {
    error() << e << eom;
    return 6;
  }

  catch (int) {
    return 6;
  }

  catch (const std::bad_alloc &) {
    error() << "Out of memory" << eom;
    return 6;
  }

  return -1; // no error, continue
}

void jsymex_parse_optionst::process_goto_function(
    goto_model_functiont &function, const abstract_goto_modelt &model,
    const optionst &options) {
  journalling_symbol_tablet &symbol_table = function.get_symbol_table();
  namespacet ns(symbol_table);
  goto_functionst::goto_functiont &goto_function = function.get_goto_function();

  bool using_symex_driven_loading =
      options.get_bool_option("symex-driven-lazy-loading");

  try {
    // Removal of RTTI inspection:
    remove_instanceof(goto_function, symbol_table, *class_hierarchy,
                      get_message_handler());
    // Java virtual functions -> explicit dispatch tables:
    remove_virtual_functions(function);

    auto function_is_stub = [&symbol_table, &model](const irep_idt &id) {
      return symbol_table.lookup_ref(id).value.is_nil() &&
             !model.can_produce_function(id);
    };

    remove_returns(function, function_is_stub);

    replace_java_nondet(function);

    // Similar removal of java nondet statements:
    convert_nondet(function, get_message_handler(), object_factory_params,
                   ID_java);

    if (using_symex_driven_loading) {
      // remove exceptions
      // If using symex-driven function loading we need to do this now so that
      // symex doesn't have to cope with exception-handling constructs; however
      // the results are slightly worse than running it in whole-program mode
      // (e.g. dead catch sites will be retained)
      remove_exceptions(goto_function.body, symbol_table,
                        *class_hierarchy.get(), get_message_handler());
    }

    // add generic checks
    goto_check(ns, options, ID_java, function.get_goto_function());

    // Replace Java new side effects
    remove_java_new(goto_function, symbol_table, get_message_handler());

    // checks don't know about adjusted float expressions
    adjust_float_expressions(goto_function, ns);

    // add failed symbols for anything created relating to this particular
    // function (note this means subseqent passes mustn't create more!):
    journalling_symbol_tablet::changesett new_symbols =
        symbol_table.get_inserted();
    for (const irep_idt &new_symbol_name : new_symbols) {
      add_failed_symbol_if_needed(symbol_table.lookup_ref(new_symbol_name),
                                  symbol_table);
    }

    // If using symex-driven function loading we must label the assertions
    // now so symex sees its targets; otherwise we leave this until
    // process_goto_functions, as we haven't run remove_exceptions yet, and that
    // pass alters the CFG.
    if (using_symex_driven_loading) {
      // label the assertions
      label_properties(goto_function.body);

      goto_function.body.update();
      function.compute_location_numbers();
      goto_function.body.compute_loop_numbers();
    }

    // update the function member in each instruction
    function.update_instructions_function();
  }

  catch (const char *e) {
    error() << e << eom;
    throw;
  }

  catch (const std::string &e) {
    error() << e << eom;
    throw;
  }

  catch (const std::bad_alloc &) {
    error() << "Out of memory" << eom;
    throw;
  }
}

bool jsymex_parse_optionst::show_loaded_functions(
    const abstract_goto_modelt &goto_model) {
  if (cmdline.isset("show-symbol-table")) {
    show_symbol_table(goto_model.get_symbol_table(), ui_message_handler);
    return true;
  } else if (cmdline.isset("list-symbols")) {
    show_symbol_table_brief(goto_model.get_symbol_table(), ui_message_handler);
    return true;
  }

  if (cmdline.isset("show-loops")) {
    show_loop_ids(ui_message_handler.get_ui(), goto_model.get_goto_functions());
    return true;
  }

  if (cmdline.isset("show-goto-functions") ||
      cmdline.isset("list-goto-functions")) {
    namespacet ns(goto_model.get_symbol_table());
    show_goto_functions(ns, get_message_handler(), ui_message_handler.get_ui(),
                        goto_model.get_goto_functions(),
                        cmdline.isset("list-goto-functions"));
    return true;
  }

  if (cmdline.isset("show-properties")) {
    namespacet ns(goto_model.get_symbol_table());
    show_properties(ns, get_message_handler(), ui_message_handler.get_ui(),
                    goto_model.get_goto_functions());
    return true;
  }

  return false;
}

bool jsymex_parse_optionst::process_goto_functions(goto_modelt &goto_model,
                                                   const optionst &options) {
  try {
    status() << "Running GOTO functions transformation passes" << eom;

    bool using_symex_driven_loading =
        options.get_bool_option("symex-driven-lazy-loading");

    // When using symex-driven lazy loading, *all* relevant processing is done
    // during process_goto_function, so we have nothing to do here.
    if (using_symex_driven_loading)
      return false;

    // remove catch and throw
    remove_exceptions(goto_model, *class_hierarchy.get(),
                      get_message_handler());

    // instrument library preconditions
    instrument_preconditions(goto_model);

    // ignore default/user-specified initialization
    // of variables with static lifetime
    if (cmdline.isset("nondet-static")) {
      status() << "Adding nondeterministic initialization "
                  "of static/global variables"
               << eom;
      nondet_static(goto_model);
    }

    // recalculate numbers, etc.
    goto_model.goto_functions.update();

    if (cmdline.isset("drop-unused-functions")) {
      // Entry point will have been set before and function pointers removed
      status() << "Removing unused functions" << eom;
      remove_unused_functions(goto_model, get_message_handler());
    }

    // remove skips such that trivial GOTOs are deleted
    remove_skip(goto_model);

    // label the assertions
    // This must be done after adding assertions and
    // before using the argument of the "property" option.
    // Do not re-label after using the property slicer because
    // this would cause the property identifiers to change.
    label_properties(goto_model);

    // reachability slice?
    if (cmdline.isset("reachability-slice-fb")) {
      if (cmdline.isset("reachability-slice")) {
        error() << "--reachability-slice and --reachability-slice-fb "
                << "must not be given together" << eom;
        return true;
      }

      status() << "Performing a forwards-backwards reachability slice" << eom;
      if (cmdline.isset("property"))
        reachability_slicer(goto_model, cmdline.get_values("property"), true);
      else
        reachability_slicer(goto_model, true);
    }

    if (cmdline.isset("reachability-slice")) {
      status() << "Performing a reachability slice" << eom;
      if (cmdline.isset("property"))
        reachability_slicer(goto_model, cmdline.get_values("property"));
      else
        reachability_slicer(goto_model);
    }

    // full slice?
    if (cmdline.isset("full-slice")) {
      status() << "Performing a full slice" << eom;
      if (cmdline.isset("property"))
        property_slicer(goto_model, cmdline.get_values("property"));
      else
        full_slicer(goto_model);
    }

    // remove any skips introduced
    remove_skip(goto_model);
  }

  catch (const char *e) {
    error() << e << eom;
    return true;
  }

  catch (const std::string &e) {
    error() << e << eom;
    return true;
  }

  catch (int) {
    return true;
  }

  catch (const std::bad_alloc &) {
    error() << "Out of memory" << eom;
    return true;
  }

  return false;
}

bool jsymex_parse_optionst::can_generate_function_body(const irep_idt &name) {
  static const irep_idt initialize_id = INITIALIZE_FUNCTION;

  return name != goto_functionst::entry_point() && name != initialize_id;
}

bool jsymex_parse_optionst::generate_function_body(
    const irep_idt &function_name, symbol_table_baset &symbol_table,
    goto_functiont &function, bool body_available) {
  // Provide a simple stub implementation for any function we don't have a
  // bytecode implementation for:

  if (body_available)
    return false;

  if (!can_generate_function_body(function_name))
    return false;

  if (symbol_table.lookup_ref(function_name).mode == ID_java) {
    java_generate_simple_method_stub(
        function_name, symbol_table, stub_objects_are_not_null,
        object_factory_params, get_message_handler());

    goto_convert_functionst converter(symbol_table, get_message_handler());
    converter.convert_function(function_name, function);

    return true;
  } else {
    return false;
  }
}

void jsymex_parse_optionst::report_properties(
    const path_searcht::property_mapt &property_map) {
  if (get_ui() == ui_message_handlert::uit::PLAIN)
    status() << "\n** Results:" << eom;

  for (const auto &p : property_map) {
    if (get_ui() == ui_message_handlert::uit::XML_UI) {
      xmlt xml_result("result");
      xml_result.set_attribute("claim", id2string(p.first));

      std::string status_string;

      switch (p.second.status) {
      case path_searcht::SUCCESS:
        status_string = "SUCCESS";
        break;
      case path_searcht::FAILURE:
        status_string = "FAILURE";
        break;
      case path_searcht::NOT_REACHED:
        status_string = "SUCCESS";
        break;
      }

      xml_result.set_attribute("status", status_string);

      std::cout << xml_result << "\n";
    } else {
      status() << "[" << p.first << "] ";
      if (!p.second.source_location.get_line().empty())
        status() << "line " << p.second.source_location.get_line() << ' ';
      status() << p.second.description << ": ";
      switch (p.second.status) {
      case path_searcht::SUCCESS:
        status() << green << "SUCCESS" << reset;
        break;
      case path_searcht::FAILURE:
        status() << red << "FAILURE" << reset;
        break;
      case path_searcht::NOT_REACHED:
        status() << yellow << "SUCCESS" << reset << " (not reached)";
        break;
      }
      status() << eom;
    }

    if ((cmdline.isset("show-trace") || cmdline.isset("trace") ||
         cmdline.isset("stack-trace") || cmdline.isset("xml-ui") ||
         cmdline.isset("stop-on-fail")) &&
        p.second.is_failure()) {
      optionst options;
      PARSE_OPTIONS_GOTO_TRACE(cmdline, options);
      UNREACHABLE;
      // show_trace(p.first, p.second.error_trace, options);
    }
  }

  if (!cmdline.isset("property")) {
    status() << eom;

    unsigned failed = 0;

    for (const auto &p : property_map)
      if (p.second.is_failure())
        failed++;

    status() << "** " << failed << " of " << property_map.size() << " failed"
             << eom;
  }
}

void jsymex_parse_optionst::report_success() {
  result() << bold << "VERIFICATION SUCCESSFUL" << reset << eom;

  switch (get_ui()) {
  case ui_message_handlert::uit::PLAIN:
    break;

  case ui_message_handlert::uit::XML_UI: {
    xmlt xml("cprover-status");
    xml.data = "SUCCESS";
    std::cout << xml;
    std::cout << '\n';
  } break;

  default:
    UNREACHABLE;
  }
}

#if 0
void jsymex_parse_optionst::show_trace(
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
#endif

void jsymex_parse_optionst::report_failure() {
  result() << bold << "VERIFICATION FAILED" << reset << eom;

  switch (get_ui()) {
  case ui_message_handlert::uit::PLAIN:
    break;

  case ui_message_handlert::uit::XML_UI: {
    xmlt xml("cprover-status");
    xml.data = "FAILURE";
    std::cout << xml;
    std::cout << '\n';
  } break;

  case ui_message_handlert::uit::JSON_UI: {
    json_objectt json_result;
    json_result["cProverStatus"] = json_stringt("failure");
    result() << json_result;
  } break;

  default:
    UNREACHABLE;
  }
}

std::string jsymex_parse_optionst::get_test(const goto_tracet &goto_trace,
                                            const symbol_tablet &symbol_table) {
  bool first = true;
  std::string test;
  const namespacet ns(symbol_table);

  for (const auto &step : goto_trace.steps) {
    if (step.is_input()) {
      if (first)
        first = false;
      else
        test += ", ";

      test += id2string(step.io_id) + "=";

      if (step.io_args.size() == 1)
        test += from_expr(ns, "", step.io_args.front());
    }
  }
  return test;
}

void jsymex_parse_optionst::report_cover(
    const path_searcht::property_mapt &property_map,
    const symbol_tablet &symbol_table) {
  // report
  unsigned goals_covered = 0;

  for (const auto &prop_pair : property_map)
    if (prop_pair.second.is_failure())
      goals_covered++;

  switch (get_ui()) {
  case ui_message_handlert::uit::PLAIN: {
    status() << "\n** coverage results:" << eom;

    for (const auto &prop_pair : property_map) {
      const auto &property = prop_pair.second;

      status() << "[" << prop_pair.first << "]";

      if (property.source_location.is_not_nil())
        status() << ' ' << property.source_location;

      if (!property.description.empty())
        status() << ' ' << property.description;

      status() << ": " << (property.is_failure() ? "SATISFIED" : "FAILED")
               << eom;
    }

    status() << '\n';

    break;
  }

  case ui_message_handlert::uit::XML_UI: {
    for (const auto &prop_pair : property_map) {
      const auto &property = prop_pair.second;

      xmlt xml_result("result");
      xml_result.set_attribute("goal", id2string(prop_pair.first));
      xml_result.set_attribute("description", id2string(property.description));
      xml_result.set_attribute("status",
                               property.is_failure() ? "SATISFIED" : "FAILED");

      if (property.source_location.is_not_nil())
        xml_result.new_element() = xml(property.source_location);

      if (property.is_failure()) {
        const namespacet ns(symbol_table);

        if (cmdline.isset("trace")) {
          convert(ns, property.error_trace, xml_result.new_element());
        } else {
          xmlt &xml_test = xml_result.new_element("test");

          for (const auto &step : property.error_trace.steps) {
            if (step.is_input()) {
              xmlt &xml_input = xml_test.new_element("input");
              xml_input.set_attribute("id", id2string(step.io_id));
              if (step.io_args.size() == 1)
                xml_input.new_element("value") = xml(step.io_args.front(), ns);
            }
          }
        }
      }

      std::cout << xml_result << "\n";
    }

    break;
  }
  case ui_message_handlert::uit::JSON_UI: {
    json_objectt json_result;
    json_arrayt &result_array = json_result["results"].make_array();
    for (const auto &prop_pair : property_map) {
      const auto &property = prop_pair.second;

      json_objectt &result = result_array.push_back().make_object();
      result["status"] =
          json_stringt(property.is_failure() ? "satisfied" : "failed");
      result["goal"] = json_stringt(id2string(prop_pair.first));
      result["description"] = json_stringt(id2string(property.description));

      if (property.source_location.is_not_nil())
        result["sourceLocation"] = json(property.source_location);

      if (property.is_failure()) {
        const namespacet ns(symbol_table);

        if (cmdline.isset("trace")) {
          //            auto &json_trace=result["trace"].make_array();
          // convert(ns, property.error_trace, json_trace);
        } else {
          json_arrayt &json_test = result["test"].make_array();

          for (const auto &step : property.error_trace.steps) {
            if (step.is_input()) {
              json_objectt json_input;
              json_input["id"] = json_stringt(id2string(step.io_id));
              if (step.io_args.size() == 1)
                json_input["value"] =
                    json(step.io_args.front(), ns, ID_unknown);
              json_test.push_back(json_input);
            }
          }
        }
      }
    }
    json_result["totalGoals"] =
        json_numbert(std::to_string(property_map.size()));
    json_result["goalsCovered"] = json_numbert(std::to_string(goals_covered));
    std::cout << ",\n" << json_result;
    break;
  }
  }

  status() << "** " << goals_covered << " of " << property_map.size()
           << " covered (" << std::fixed << std::setw(1) << std::setprecision(1)
           << (property_map.empty() ? 100.0 : 100.0 * goals_covered /
                                                  property_map.size())
           << "%)" << eom;

  if (get_ui() == ui_message_handlert::uit::PLAIN) {
    std::set<std::string> tests;

    for (const auto &prop_pair : property_map)
      if (prop_pair.second.is_failure())
        tests.insert(get_test(prop_pair.second.error_trace, symbol_table));

    std::cout << "Test suite:" << '\n';

    for (const auto &t : tests)
      std::cout << t << '\n';
  }
}

/// display command line help
void jsymex_parse_optionst::help() {
  // clang-format off
  std::cout << '\n' << banner_string("JBMC", CBMC_VERSION) << '\n'
            <<
    "* *                 Copyright (C) 2001-2018                 * *\n"
    "* *              Daniel Kroening, Edmund Clarke             * *\n"
    "* * Carnegie Mellon University, Computer Science Department * *\n"
    "* *                 kroening@kroening.com                   * *\n"
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " jbmc [-?] [-h] [--help]      show help\n"
    " jbmc class                   name of class or JAR file to be checked\n"
    "                              In the case of a JAR file, if a main class can be\n" // NOLINT(*)
    "                              inferred from --main-class, --function, or the JAR\n" // NOLINT(*)
    "                              manifest (checked in this order), the behavior is\n" // NOLINT(*)
    "                              the same as running jbmc on the corresponding\n" // NOLINT(*)
    "                              class file."
    "\n"
    "Analysis options:\n"
    HELP_SHOW_PROPERTIES
    " --symex-coverage-report f    generate a Cobertura XML coverage report in f\n" // NOLINT(*)
    " --property id                only check one specific property\n"
    " --stop-on-fail               stop analysis once a failed property is detected\n" // NOLINT(*)
    " --trace                      give a counterexample trace for failed properties\n" //NOLINT(*)
    "\n"
    HELP_FUNCTIONS
    "\n"
    "Program representations:\n"
    " --show-parse-tree            show parse tree\n"
    " --show-symbol-table          show loaded symbol table\n"
    " --list-symbols               list symbols with type information\n"
    HELP_SHOW_GOTO_FUNCTIONS
    " --drop-unused-functions      drop functions trivially unreachable\n"
    "                              from main function\n"
    HELP_SHOW_CLASS_HIERARCHY
    "\n"
    "Program instrumentation options:\n"
    " --no-assertions              ignore user assertions\n"
    " --no-assumptions             ignore user assumptions\n"
    " --error-label label          check that label is unreachable\n"
    " --mm MM                      memory consistency model for concurrent programs\n" // NOLINT(*)
    HELP_REACHABILITY_SLICER
    " --full-slice                 run full slicer (experimental)\n" // NOLINT(*)
    "\n"
    "Java Bytecode frontend options:\n"
    " --classpath dir/jar          set the classpath\n"
    " --main-class class-name      set the name of the main class\n"
    JAVA_BYTECODE_LANGUAGE_OPTIONS_HELP
    // This one is handled by jbmc_parse_options not by the Java frontend,
    // hence its presence here:
    " --java-threading             enable java multi-threading support (experimental)\n" // NOLINT(*)
    " --java-unwind-enum-static    unwind loops in static initialization of enums\n" // NOLINT(*)
    // Currently only supported in the JBMC frontend:
    " --symex-driven-lazy-loading  only load functions when first entered by symbolic\n" // NOLINT(*)
    "                              execution. Note that --show-symbol-table,\n"
    "                              --show-goto-functions/properties output\n"
    "                              will be restricted to loaded methods in this case,\n" // NOLINT(*)
    "                              and only output after the symex phase.\n"
    "\n"
    "Semantic transformations:\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --nondet-static              add nondeterministic initialization of variables with static lifetime\n"
    "\n"
    "BMC options:\n"
    HELP_BMC
    "\n"
    "Backend options:\n"
    " --object-bits n              number of bits used for object addresses\n"
    " --dimacs                     generate CNF in DIMACS format\n"
    " --beautify                   beautify the counterexample (greedy heuristic)\n" // NOLINT(*)
    " --localize-faults            localize faults (experimental)\n"
    " --smt1                       use default SMT1 solver (obsolete)\n"
    " --smt2                       use default SMT2 solver (Z3)\n"
    " --boolector                  use Boolector\n"
    " --mathsat                    use MathSAT\n"
    " --cvc4                       use CVC4\n"
    " --yices                      use Yices\n"
    " --z3                         use Z3\n"
    " --refine                     use refinement procedure (experimental)\n"
    HELP_STRING_REFINEMENT
    " --outfile filename           output formula to given file\n"
    " --arrays-uf-never            never turn arrays into uninterpreted functions\n" // NOLINT(*)
    " --arrays-uf-always           always turn arrays into uninterpreted functions\n" // NOLINT(*)
    "\n"
    "Other options:\n"
    " --version                    show version and exit\n"
    " --xml-ui                     use XML-formatted output\n"
    " --json-ui                    use JSON-formatted output\n"
    HELP_GOTO_TRACE
    HELP_FLUSH
    " --verbosity #                verbosity level\n"
    HELP_TIMESTAMP
    "\n";
  // clang-format on
}
