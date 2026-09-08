void divide(int n, int *p)

{
	int cnt = 0;

	for (int i = 2; i <= n; i++) {

		while (n % i == 0) {

			cnt++;
			p[cnt] = i;
			n /= i;
		}
		if (n == 1) {
			break;
		}

	}
}
