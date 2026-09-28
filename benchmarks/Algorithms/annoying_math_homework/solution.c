#define N 20
#define M 10
#define P 1000000007

#include "int_array_def.h"

void digits_sum_init(int *dp, int *power)

{
  power[0] = 1;
  
  for (int i = 1; i < N; i++) {
    long long bef = power[i - 1];
    bef = bef * 10 % P;
    power[i] = (int)bef;
  }

  for (int i = 0; i < N; i++) {
    
    for (int j = 0; j < M; j++) {
      dp[i * M + j] = 0;
    }
  }

  for (int j = 0; j < M; j++) {
    dp[M + j] = j;
  }

  for (int i = 2; i < N; i++) {
    
    for (int j = 0; j < M; j++) {
      
      for (int k = 0; k < M; k++) {
        long long sub_power = power[i - 2];
        long long moving =
            (dp[(i - 1) * M + k] + sub_power * j % P) % P;
        long long new_dp = (dp[i * M + j] + moving) % P;
        dp[i * M + j] = (int)new_dp;
      }
    }
  }
}

int prefix_digits_sum(long long x, int *dp, int *digits)

{
  int m = 0;
  int ans = 0;
  long long power_ll = 1;

  if (x < 1) {
    return 0;
  }

  for (int i = 0; i < N; i++) {
    digits[i] = 0;
  }

  long long tmpx = x;
  
  while (tmpx) {
    m = m + 1;
    digits[m] = (int)(tmpx % 10);
    tmpx /= 10;
  }

  for (int i = 1; i < m; i++) {
    power_ll *= 10;
  }

  for (int i = m; i > 0; i--) {
    
    for (int j = 0; j < digits[i]; j++) {
      ans = (ans + dp[i * M + j]) % P;
    }

    {
      long long current_digit = (x / power_ll) % 10;
      long long lower_digits = (x % power_ll + 1) % P;
      long long moving = lower_digits * current_digit % P;
      long long new_ans = (ans + moving) % P;
      ans = (int)new_ans;
    }

    power_ll /= 10;
  }

  return ans;
}

int interval_digits_sum(long long x, long long y)

{
  int dp[200];
  int power[20];
  int digits[20];
  
  digits_sum_init(dp, power);
  int ans1 = prefix_digits_sum(y, dp, digits);
  int ans2 = prefix_digits_sum(x - 1, dp, digits);
  
  return ((ans1 - ans2) % P + P) % P;
}
