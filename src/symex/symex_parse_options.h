/*******************************************************************\

Module: Command Line Parsing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Command Line Parsing

#ifndef CPROVER_SYMEX_SYMEX_PARSE_OPTIONS_H
#define CPROVER_SYMEX_SYMEX_PARSE_OPTIONS_H

#include <util/ui_message.h>
#include <util/parse_options.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/goto_trace.h>
#include <goto-programs/show_goto_functions.h>
#include <goto-programs/rebuild_goto_start_function.h>

#include <analyses/goto_check.h>

#include "path_search.h"

class goto_functionst;
class optionst;

#define SYMEX_OPTIONS \
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
  "(c89)(c99)(c11)" \
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
  // the last line is for CBMC-regression testing only

class symex_parse_optionst:
  public parse_options_baset,
  public messaget
{
public:
  virtual int doit();
  virtual void help();

  symex_parse_optionst(int argc, const char **argv);

protected:
  ui_message_handlert ui_message_handler;
  goto_modelt goto_model;

  void get_command_line_options(optionst &options);
  bool process_goto_program(const optionst &options);
  bool set_properties();

  void report_success();
  void report_failure();
  void report_properties(const path_searcht::property_mapt &);
  void report_cover(const path_searcht::property_mapt &);
  void show_trace(const irep_idt &, const class goto_tracet &, const optionst &);

  void eval_verbosity();

  std::string get_test(const goto_tracet &goto_trace);

  ui_message_handlert::uit get_ui() const
  {
    return ui_message_handler.get_ui();
  }
};

#endif // CPROVER_SYMEX_SYMEX_PARSE_OPTIONS_H
