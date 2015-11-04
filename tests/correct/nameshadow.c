// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int g;

int globals() {

    int x;
    int y;
    
    x = 5;
    if(x == 5) {
    	g = 100;
        x = 20;
        int x;
    	x = 10;
    }
    else {
    	g = 20;
        x = 35;
    }
    assert(x == 20);
    return 0;

}