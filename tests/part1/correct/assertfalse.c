// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo() {
  assume 0;
  assert 0;
  return 1;
}
