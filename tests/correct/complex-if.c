// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int x;
int y;

int iffy(int i, int j)
  requires i == j,
  requires i == \old(x),
  ensures \result == \old(x),
  ensures \result == j,
  ensures \result == i
{
  assert j == x;
  x = x + 1;

  if(x > i && x > j) {
    assert 1;
  }

    int x;
    int y;
    x = i;
    y = j;
    if(x < (1 << 24)) {
        x = x + 1;
        y = y + 1;
    } else {
        if(x > 24) {
            x = x + y;
            y = y + y;
        }
    }
    assert x == y;
    assert j == \old(x);
    return \old(x);
}
