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
  "D:I:" \
  "(depth):(context-bound):(branch-bound):(unwind):(max-search-time):" \
  OPT_GOTO_CHECK \
  "(no-assertions)(no-assumptions)" \
  "(unwinding-assertions)" \
  "(graphml-witness):" \
  "(16)(32)(64)(LP64)(ILP64)(LLP64)(ILP32)(LP32)" \
  "(little-endian)(big-endian)" \
  "(error-label):(verbosity):(no-library)" \
  "(version)" \
  "(bfs)(dfs)(locs)" \
  "(cover):" \
  "(i386-linux)(i386-macos)(i386-win32)(win32)(winx64)(gcc)" \
  "(ppc-macos)(unsigned-char)" \
  "(string-abstraction)(smt2)(z3)(refine)(outfile):" \
  "(no-arch)(arch):(floatbv)(fixedbv)" \
  "(round-to-nearest)(round-to-plus-inf)(round-to-minus-inf)(round-to-zero)" \
  "(show-locs)(show-vcc)(show-loops)(show-properties)(show-symbol-table)" \
  "(drop-unused-functions)" \
  "(object-bits):" \
  OPT_SHOW_GOTO_FUNCTIONS \
  "(property):(trace)(stop-on-fail)(eager-infeasibility)" \
  OPT_GOTO_TRACE \
  "(no-simplify)(no-unwinding-assertions)(no-propagation)" \
  "(no-self-loops-to-assumptions)" \
  "(json-ui)(xml-ui)" \
  JAVA_BYTECODE_LANGUAGE_OPTIONS \
// clang-format on

class jsymex_parse_optionst:
  public parse_options_baset,
  public messaget
{
public:
  virtual int doit() override;
  virtual void help() override;

  jsymex_parse_optionst(int argc, const char **argv);
  jsymex_parse_optionst(
    int argc,
    const char **argv,
    const std::string &extra_options);

  /// \brief Set the options that have default values
  ///
  /// This function can be called from clients that wish to emulate JBMC's
  /// default behaviour, for example unit tests.
  static void set_default_options(optionst &);

  void process_goto_function(
    goto_model_functiont &function,
    const abstract_goto_modelt &,
    const optionst &);
  bool process_goto_functions(goto_modelt &goto_model, const optionst &options);

  bool can_generate_function_body(const irep_idt &name);

  bool generate_function_body(
    const irep_idt &function_name,
    symbol_table_baset &symbol_table,
    goto_functiont &function,
    bool body_available);

protected:
  ui_message_handlert ui_message_handler;
  path_strategy_choosert path_strategy_chooser;
  object_factory_parameterst object_factory_params;
  bool stub_objects_are_not_null;

  std::unique_ptr<class_hierarchyt> class_hierarchy;

  void get_command_line_options(optionst &);
  int get_goto_program(
    std::unique_ptr<goto_modelt> &goto_model, const optionst &);
  bool show_loaded_functions(const abstract_goto_modelt &goto_model);

  bool set_properties(goto_modelt &goto_model);

  void report_success();
  void report_failure();
  void report_properties(const path_searcht::property_mapt &);

  void report_cover(
    const path_searcht::property_mapt &,
    const symbol_tablet &symbol_table);
  void show_trace(const irep_idt &, const class goto_tracet &, const optionst &);
  std::string get_test(
    const goto_tracet &goto_trace,
    const symbol_tablet &symbol_table);

  bool process_goto_program(
    const optionst &options,
    goto_modelt &goto_model);

  ui_message_handlert::uit get_ui() const
  {
    return ui_message_handler.get_ui();
  }

  int path_symex_main_procedure(
    goto_modelt &goto_model,
    messaget *log,
    bool show_locs,
    cmdlinet &cmdline,
    optionst &options);
};

#endif // CPROVER_JBMC_JBMCPS_PARSE_OPTIONS_H
