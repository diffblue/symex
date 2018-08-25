int global_array[20];

struct S
{
  int some_array[20];
} s;

int main()
{
  global_array[1]=1;
  global_array[2]=2;

  s.some_array[1]=1;
  s.some_array[2]=2;
  int *p=s.some_array+5;
  *p=5;

  int local_array[10];
  local_array[1]=1;
  local_array[2]=2;
  __CPROVER_assert(0, "");
}
