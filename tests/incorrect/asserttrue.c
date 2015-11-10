// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int foo() {
  assume 100;
  assert 0;
  return 1;
}
