struct S
{
  int a, b;
};

int main()
{
  struct S *p=malloc(sizeof(struct S));
  p->a=1;
  p->b=2;  
  assert(0);
}
