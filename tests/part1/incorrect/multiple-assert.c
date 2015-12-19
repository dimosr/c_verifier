// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int x;
int y;

int iffy(int i, int j)
  requires i == j,
  requires i == \old(x)
{
  assert j == x;
  assert i == x;
  x = x + 1;

  assert (x > i) && (x > j);

    return 0;
}
