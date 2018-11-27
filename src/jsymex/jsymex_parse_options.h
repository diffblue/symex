/*******************************************************************\

Module: JBMC Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// JBMC Command Line Option Processing

#ifndef CPROVER_JBMC_JBMCPS_PARSE_OPTIONS_H
#define CPROVER_JBMC_JBMCPS_PARSE_OPTIONS_H

#include <util/parse_options.h>
#include <util/timestamper.h>
#include <util/ui_message.h>

#include <langapi/language.h>

#include <analyses/goto_check.h>

#include <cbmc/bmc.h>

#include <goto-programs/class_hierarchy.h>
#include <goto-programs/goto_trace.h>
#include <goto-programs/lazy_goto_model.h>
#include <goto-programs/show_properties.h>

#include <goto-symex/path_storage.h>

#include <solvers/refinement/string_refinement.h>

#include "../symex/path_search.h"
#include <java_bytecode/java_bytecode_language.h>

class bmct;
class goto_functionst;
class optionst;

// clang-format off
#define JSYMEX_OPTIONS \
  OPT_FUNCTIONS \
  OPT_PATH_SEARCH \
  OPT_GOTO_CHECK \
  OPT_STRING_REFINEMENT \
  JAVA_BYTECODE_LANGUAGE_OPTIONS \
  "D:I:" \
  "(version)(verbosity):" \
  "(show-locs)(show-vcc)(show-loops)(show-properties)(show-symbol-table)" \
  "(cover):(cover-function-only)(trace)" \
  "(json-ui)(xml-ui)" \
  "(classpath):" \
  "(debug-level)(unwindset)(simplify)(assertions)(assumptions)(error-label)"\
  "(max-nondet-string-length):"
// clang-format on

class jsymex_parse_optionst : public parse_options_baset, public messaget {
public:
  int doit() override;
  void help() override;

  jsymex_parse_optionst(int argc, const char **argv);

  void process_goto_function(goto_model_functiont &function,
                             const abstract_goto_modelt &, const optionst &);
  bool process_goto_functions(goto_modelt &goto_model, const optionst &options);

  bool can_generate_function_body(const irep_idt &name);

  bool generate_function_body(const irep_idt &function_name,
                              symbol_table_baset &symbol_table,
                              goto_functiont &function, bool body_available);

protected:
  ui_message_handlert ui_message_handler;
  path_strategy_choosert path_strategy_chooser;
  object_factory_parameterst object_factory_params;
  bool stub_objects_are_not_null;

  std::unique_ptr<class_hierarchyt> class_hierarchy;

  int get_goto_program(std::unique_ptr<goto_modelt> &goto_model,
                       const optionst &);
  bool set_properties(goto_modelt &goto_model);

  void report_success();
  void report_failure();
  void report_properties(
    const path_searcht::property_mapt &,
    const symbol_tablet &symbol_table);

  void report_cover(const path_searcht::property_mapt &,
                    const symbol_tablet &symbol_table);
  std::string get_test(const goto_tracet &goto_trace,
                       const symbol_tablet &symbol_table);

  bool process_goto_program(const optionst &options, goto_modelt &goto_model);

  ui_message_handlert::uit get_ui() const {
    return ui_message_handler.get_ui();
  }

  int path_symex(
    goto_modelt &goto_model, messaget *log,
    cmdlinet &cmdline, optionst &options);

  void show_trace(
    const irep_idt &property,
    const goto_tracet &error_trace,
    const optionst &options,
    const symbol_tablet &symbol_table);
};

#endif // CPROVER_JBMC_JBMCPS_PARSE_OPTIONS_H
