int max(int a, int b)

{
    return (a > b) ? a : b;
}

int max_sub_array(int *arr, int n)

{
    if (n == 0) {
        return 0;
    }

    int cur = arr[0]; 
    int res = arr[0];  

    for (int i = 1; i < n; i++) {

        cur = max(arr[i], cur + arr[i]);

        res = max(res, cur);

    }

    return res;
}
