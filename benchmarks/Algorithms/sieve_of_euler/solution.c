int *get_prime(int n, int tot, int *prime)

{
     int flag[46341];

     for (int z = 2; z <= n; ++z) {
          flag[z] = 0;
     }

     tot = 0;

     for (int i = 2; i <= n; i++)
		flag[i] = i;

	for (int i = 2; i <= n; i++) {
		if (flag[i] == i) {
               tot = tot + 1;
               prime[tot] = i;
          }

		for (int j = 1; i * prime[j] <= n && j <= tot; j++) {
			flag[i * prime[j]] = prime[j];

			if (i % prime[j] == 0) {

                    break;
               }

		}

	}

     return prime;
}
