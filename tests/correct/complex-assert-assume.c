// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int t;

int foo()
  ensures \result == 4
{
  int t;
  t = 3;
  assert t == 3;
  assert(t == 3);
  assert(3 == t);

  havoc t;
  assume(t == 4);
  assert t == 4;
  assume t == 4;
  assert t == 4;

  return t;
}
