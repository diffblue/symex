/// Copyright 2016-2018 DiffBlue Limited. All Rights Reserved.

/// \file
/// JSYMEX Command Line Option Processing

#include "jsymex_parse_options.h"

#include <iomanip>
#include <iostream>

#include <ansi-c/ansi_c_language.h>
#include <goto-instrument/cover.h>
#include <goto-instrument/nondet_static.h>
#include <goto-instrument/reachability_slicer.h>
#include <goto-programs/adjust_float_expressions.h>
#include <goto-programs/instrument_preconditions.h>
#include <goto-programs/json_goto_trace.h>
#include <goto-programs/link_to_library.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/remove_complex.h>
#include <goto-programs/remove_returns.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/remove_unused_functions.h>
#include <goto-programs/remove_vector.h>
#include <goto-programs/remove_virtual_functions.h>
#include <goto-programs/rewrite_union.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/show_goto_functions.h>
#include <goto-programs/show_symbol_table.h>
#include <goto-programs/xml_goto_trace.h>
#include <java_bytecode/convert_java_nondet.h>
#include <java_bytecode/java_enum_static_init_unwind_handler.h>
#include <java_bytecode/remove_exceptions.h>
#include <java_bytecode/remove_instanceof.h>
#include <java_bytecode/remove_java_new.h>
#include <java_bytecode/replace_java_nondet.h>
#include <java_bytecode/simple_method_stubbing.h>
#include <langapi/language_util.h>
#include <langapi/mode.h>
#include <linking/static_lifetime_init.h>
#include <pointer-analysis/add_failed_symbols.h>
#include <util/config.h>
#include <util/exit_codes.h>
#include <util/json_expr.h>
#include <util/string2int.h>
#include <util/version.h>
#include <util/xml.h>
#include <util/xml_expr.h>

#include "../goto-locs/locs.h"
#include "../symex/path_search.h"

jsymex_parse_optionst::jsymex_parse_optionst(int argc, const char **argv)
    : parse_options_baset(JSYMEX_OPTIONS, argc, argv),
      messaget(ui_message_handler),
      ui_message_handler(cmdline, std::string("JBMC ") + CBMC_VERSION),
      path_strategy_chooser() {}

void jsymex_parse_optionst::get_command_line_options(optionst &options) {
  if (config.set(cmdline)) {
    usage_error();
    exit(1); // should contemplate EX_USAGE from sysexits.h
  }

  parse_java_language_options(cmdline, options);
  parse_object_factory_options(cmdline, options);

  if (cmdline.isset("debug-level"))
    options.set_option("debug-level", cmdline.get_value("debug-level"));

  if (cmdline.isset("unwindset"))
    options.set_option("unwindset", cmdline.get_value("unwindset"));

  // all checks supported by goto_check
  PARSE_OPTIONS_GOTO_CHECK(cmdline, options);

  options.set_option("simplify", !cmdline.isset("no-simplify"));
  options.set_option("assertions", !cmdline.isset("no-assertions"));
  options.set_option("assumptions", !cmdline.isset("no-assumptions"));

  // magic error label
  if (cmdline.isset("error-label"))
    options.set_option("error-label", cmdline.get_values("error-label"));

  if (cmdline.isset("cover"))
    parse_cover_options(cmdline, options);
}

struct jsymex_configt {
  optionalt<std::string> show;
  bool cover;
};

static jsymex_configt jsymex_config(const cmdlinet &cmdline) {
  jsymex_configt config;
  if (cmdline.isset("show-symbol-table"))
    config.show.emplace("symbol-table");
  else if (cmdline.isset("show-loops"))
    config.show.emplace("loops");
  else if (cmdline.isset("show-goto-functions"))
    config.show.emplace("goto-functions");
  else if (cmdline.isset("show-properties"))
    config.show.emplace("properties");
  else if (cmdline.isset("show-locs"))
    config.show.emplace("locs");
  config.cover = cmdline.isset("cover");
  return config;
}

static void configure(path_searcht &path_search, const cmdlinet &cmdline) {
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

  path_search.eager_infeasibility = cmdline.isset("eager-infeasibility");

  path_search.stop_on_fail = cmdline.isset("stop-on-fail");
}

// Should correspond to symex::doit
int jsymex_parse_optionst::path_symex_main_procedure(goto_modelt &goto_model,
                                                     messaget *log,
                                                     cmdlinet &cmdline,
                                                     optionst &options) {
  auto config = jsymex_config(cmdline);
  if (config.show && *config.show == "properties") {
    show_properties(goto_model, get_message_handler(),
                    ui_message_handler.get_ui());
    return 0; // should contemplate EX_OK from sysexits.h
  }

  if (set_properties(goto_model))
    return 7; // should contemplate EX_USAGE from sysexits.h

  if (config.show && *config.show == "symbol-table") {
    show_symbol_table(goto_model, ui_message_handler);
    return 0;
  }

  if (process_goto_program(options, goto_model))
    return 6;

  if (config.show) {
    if (*config.show == "loops") {
      show_loop_ids(get_ui(), goto_model);
      return 0;
    }
    if (*config.show == "goto-functions") {
      show_goto_functions(goto_model, get_message_handler(), get_ui());
      return 0;
    }
    if (*config.show == "properties") {
      show_properties(goto_model, get_message_handler(), get_ui());
      return 0;
    }
  }

  if (set_properties(goto_model))
    return 7;

  label_properties(goto_model);

  if (config.show && *config.show == "locs") {
    const namespacet ns(goto_model.symbol_table);
    locst locs(ns);
    locs.build(goto_model.goto_functions);
    locs.output(std::cout);
    return 0;
  }

  // do actual Symex
  const namespacet ns(goto_model.symbol_table);
  path_searcht path_search(ns);
  path_search.set_message_handler(log->get_message_handler());
  configure(path_search, cmdline);
  if (config.show && *config.show == "vcc") {
    path_search.show_vcc = true;
    path_search(goto_model.goto_functions);
    return 0;
  }

  if (config.cover) {
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

/// invoke main modules
int jsymex_parse_optionst::doit() {
  if (cmdline.isset("version")) {
    std::cout << CBMC_VERSION << '\n';
    return 0; // should contemplate EX_OK from sysexits.h
  }

  eval_verbosity(cmdline.get_value("verbosity"), messaget::M_STATISTICS,
                 ui_message_handler);

  optionst options;
  get_command_line_options(options);

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

  return path_symex_main_procedure(goto_model, static_cast<messaget *>(this),
                                   cmdline, options);
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
  } catch (const std::bad_alloc &) {
    error() << "Out of memory" << eom;
    return 6;
  }

  return -1; // no error, continue
}

bool jsymex_parse_optionst::process_goto_program(const optionst &options,
                                                 goto_modelt &goto_model) {
  try {
    status() << "Generic Property Instrumentation" << eom;
    goto_check(options, goto_model);
    remove_virtual_functions(goto_model);
    instrument_preconditions(goto_model);
    remove_returns(goto_model);
    remove_complex(goto_model);
    remove_vector(goto_model);
    rewrite_union(goto_model);
    adjust_float_expressions(goto_model);

    // recalculate numbers, etc.
    goto_model.goto_functions.update();

    goto_model.goto_functions.compute_loop_numbers();

    if (cmdline.isset("drop-unused-functions")) {
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
  } catch (const std::bad_alloc &) {
    error() << "Out of memory" << eom;
    return true;
  }
  return false;
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
  } catch (const std::bad_alloc &) {
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

    // remove any skips introduced
    remove_skip(goto_model);
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
          auto &json_trace = result["trace"].make_array();
          convert(ns, property.error_trace, json_trace);
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
  std::cout << '\n' << banner_string("JSymex", CBMC_VERSION) << '\n'
            << "* *                    DiffBlue Limited."
    "                              * *\n"
    "* *                   All Rights Reserved"
    "                             * *\n"
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " jsymex [-?] [-h] [--help]      show help\n"
    "\n"
    HELP_SHOW_GOTO_FUNCTIONS
    "\n"
    "Java Bytecode frontend options:\n"
    " --classpath dir/jar          set the classpath\n"
    " --main-class class-name      set the name of the main class\n"
    JAVA_BYTECODE_LANGUAGE_OPTIONS_HELP
    "\n";
  // clang-format on
}
