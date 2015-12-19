// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int g;

int foo() {

    int x;
    int y;
    
    x = 5;
    if(x == 5) {
    	g = 100;
    	x = 10;
    }
    else {
    	g = 20;
    }
    assert(g == 100);
    return 0;

}
