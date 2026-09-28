int coinChange(int *coins, int coinsSize, int amount)

{
  int dp[100001];

  dp[0] = 1;
  
  for (int j = 1; j <= amount; ++j) {
    dp[j] = 0;
  }

  for (int i = 0; i < coinsSize; ++i) {
    int coin = coins[i];
    if (coin <= amount) {
      
      for (int j = coin; j <= amount; ++j) {
        if (dp[j - coin] != 0) {
          dp[j] = 1;
        }
      }
    }
  }

  int res = amount;
  
  while (res > 0 && dp[res] == 0) {
    --res;
  }
  
  return res;
}
