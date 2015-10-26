// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int foo() {

    int x;
    int y;
    x = 20;
    y = x - 5*4;
    assert (y - 10 ) == 50;
    int z;
    int k;
    k = 2;
    k = (2 + x)*k;
    assert k == 44;
    k = k - 4;
    
    assert (k == 40) && (y == 15) && (x < 21);
    return 0;
}
