/*@ Extern Coq
      (MaxReachableAmount : list Z -> Z -> Z -> Prop)
      (DpReachableTable : list Z -> list Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.coin_change.rocq.spec_lib */

int coinChange(int *coins, int coinsSize, int amount, int *dp)
/*@ With (coins_l : list Z)
    Require
      0 <= coinsSize && coinsSize <= 100000 &&
      0 <= amount && amount <= 100000 &&
      Zlength(coins_l) == coinsSize &&
      IntArray::full(coins, coinsSize, coins_l) *
      IntArray::undef_full(dp, amount + 1) &&
      (forall (k : Z), (0 <= k && k < coinsSize) => (1 <= coins_l[k] && coins_l[k] <= INT_MAX))
    Ensure
      exists dp_l,
      MaxReachableAmount(coins_l, amount, __return) &&
      DpReachableTable(coins_l, dp_l, amount + 1) &&
      IntArray::full(coins, coinsSize, coins_l) *
      IntArray::full(dp, amount + 1, dp_l)
 */
{
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
