// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int iffy() {
  int x;
  x = 3;

  assume x == 3;

  havoc x;
  assert x == 3;

  return 0;
}
