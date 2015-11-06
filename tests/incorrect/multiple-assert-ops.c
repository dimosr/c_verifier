// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int iffy() {
  int x;
  x = 4;

  assert(7 - 4 + 2 == 5);

  assert(3 < 2 ? 3 : 3 + 2 == 5 ? 1 : 0);

  if (x > 3 < 2 ? (3 < 2 ? 0 : 10) : 10) {
    int y;
    y = x;
    int x;
    x = x;
    x = y + 1;
    assert x == 5;

    assert 1;
  } else {
    x = x;
    assert 0;
  }

  if (x > 0) {
    int x;
    x = x;
    x = x + 1;
    assert x == 5;
  }

  return 0;
}
