// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int globals() {

    int x;
    
    x = 5;
    if(x == 5) {
    	int y;
        y = 20;
    }
    assert(x == 5);
    return 0;

}