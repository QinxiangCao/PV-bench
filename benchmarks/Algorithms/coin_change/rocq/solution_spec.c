/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (MaxReachableAmount : list Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Algorithms.coin_change.rocq.spec_lib */

int coinChange(int *coins, int coinsSize, int amount)
/*@ With (coins_l : list Z)
    Require
      0 <= coinsSize && coinsSize <= 100000 &&
      0 <= amount && amount <= 100000 &&
      Forall(Z::le(1), coins_l) && Forall(Z::ge(INT_MAX), coins_l) &&
      IntArray::full(coins, coinsSize, coins_l)
    Ensure
      MaxReachableAmount(coins_l, amount, __return) &&
      IntArray::full(coins, coinsSize, coins_l)
 */
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
