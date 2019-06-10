/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PATH_SYMEX_ERROR_H
#define CPROVER_PATH_SYMEX_ERROR_H

#include <util/exception_utils.h>

class path_symex_errort : public cprover_exception_baset
{
public:
  std::string what() const override
  {
    return get_message();
  }

  std::ostringstream &message_ostream()
  {
    return message;
  }

  std::string get_message() const
  {
    return message.str();
  }

protected:
  std::ostringstream message;
};

/// add to the diagnostic information in the given exception
template <typename T>
path_symex_errort
operator<<(path_symex_errort &&e, const T &message)
{
  e.message_ostream() << message;
  return std::move(e);
}

template <typename T>
path_symex_errort &
operator<<(path_symex_errort &e, const T &message)
{
  e.message_ostream() << message;
  return e;
}

#endif
