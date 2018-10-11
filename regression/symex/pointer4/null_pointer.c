#include <stdlib.h>
#include <assert.h>

struct whatnot
{
  int *ptr;
  char member;
} *whatelse, *z;

int main()
{
  int input;
  int *p;
  p=malloc(sizeof(int));
  whatelse=malloc(sizeof(struct whatnot));
  whatelse->ptr=p;
  *whatelse->ptr=2;

  whatelse=input?0:whatelse;
  z=whatelse;

  if(whatelse)
  {
    // should fail
    int data=*whatelse->ptr;
    assert(data==3);
  }
}
