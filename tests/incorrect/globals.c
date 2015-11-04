int g;

int globals() {

	g = 0;
	int a;
	a = 2;
	if(a == 2) {
		int g;
		g = 5;
	}
	else {
		g = 7;
	}
	assert(g == 5);
	return 0;
}