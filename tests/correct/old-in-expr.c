// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int x;

int iffy()
  requires \old(x) == 2,
  ensures \result == 3
{
  int x;
  x = 2;

  assert x == \old(x);

  assume x == 3;
  assert x == 3;

  havoc x;
  assert x == 3;

  return x;
}
