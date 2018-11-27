/// Copyright 2016-2018 DiffBlue Limited. All Rights Reserved.

/// \file
/// JSYMEX, symex for Java

#include "jsymex_parse_options.h"

#include <util/unicode.h>

#ifdef _MSC_VER
int wmain(int argc, const wchar_t **argv_wide) {
  auto vec = narrow_argv(argc, argv_wide);
  auto narrow = to_c_str_array(std::begin(vec), std::end(vec));
  auto argv = narrow.data();
#else
int main(int argc, const char **argv) {
#endif
  return jsymex_parse_optionst(argc, argv).main();
}
