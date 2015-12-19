// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo(int i) {
    int x;
    int y;

	x = 4;
	y = 3;


    return x;
}
