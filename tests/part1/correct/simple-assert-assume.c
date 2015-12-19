// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo()
  ensures \result == 2
{
  assume 0;
  assert 0;
  return 1;
}
