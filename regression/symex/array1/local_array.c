#include <assert.h>

int main()
{
  int size;

  if(size>=10 && size<=100)
  {
    int some_array[size];
    some_array[0]=0;
    some_array[1]=1;
    some_array[2]=2;
    assert(0);
  }
}
