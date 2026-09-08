int climbStairs(int n)

{
    int prev = 1;
    int curr = 1;
    int i = 2;

    while (i <= n) {
        int next = prev + curr;
        prev = curr;
        curr = next;
        i = i + 1;
    }

    return curr;
}
