void foo_rec(int arg)
{
  int local;
  local = arg;

  if(arg == 1)
  {
    foo_rec(2);
    __CPROVER_assert(local==arg, "local variables are preserved");
  }
}

int main()
{
  foo_rec(1);
}
