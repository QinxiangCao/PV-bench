#include "int_array_def.h"
#include "array2_def.h"

void stock_init_storage(int *storage, int length)

{

    for (int index = 0; index < length; ++index) {
        storage[index] = 0;
    }

}

int maximum_profit(int days, int max_stock, int wait_days,
                         int *ap, int *bp, int *buy_limit, int *sell_limit)

{
    int queue_index[991];
    int dp[982081];

    stock_init_storage(queue_index, max_stock + 1);
    stock_init_storage(dp, (days + 1) * (max_stock + 1));

    int neg_inf = -1000000000;
    int width = max_stock + 1;

    for (int q_init = 0; q_init < width; ++q_init) {
        queue_index[q_init] = 0;
    }

    for (int i = 0; i < days + 1; ++i) {

        for (int j = 0; j < width; ++j) {
            if (i == 0 && j == 0) {
                *(dp + i * width + j) = 0;
            } else {
                *(dp + i * width + j) = neg_inf;
            }
        }
    }

    for (int i = 1; i <= days; ++i) {

        for (int j = 0; j <= max_stock; ++j) {
            int previous_value = *(dp + (i - 1) * width + j);

            *(dp + i * width + j) = previous_value;
        }
        if (i - 1 <= wait_days) {
            int buy_cap = buy_limit[i - 1];
            int ask_price = ap[i - 1];

            for (int j = 1; j <= buy_cap; ++j) {
                int candidate = -j * ask_price;
                if (candidate > *(dp + i * width + j)) {
                    *(dp + i * width + j) = candidate;
                }
            }

            continue;
        }
        int source_day = i - wait_days - 1;
        int bid_price = bp[i - 1];
        int sell_cap = sell_limit[i - 1];
        int head = 0;
        int tail = 0;

        for (int j = max_stock - 1; j >= 0; --j) {

            while (head < tail && queue_index[head] - sell_cap > j) {
                ++head;
            }

            if (*(dp + source_day * width + (j + 1)) != neg_inf) {
            int last_index = j + 1;
            if (head < tail) {
                last_index = queue_index[tail - 1];
            }
            int incoming_score = *(dp + source_day * width + (j + 1)) + (j + 1) * bid_price;

            while (head < tail &&
                   *(dp + source_day * width + last_index) +
                       last_index * bid_price <= incoming_score) {
                --tail;
                if (head < tail) {
                    last_index = queue_index[tail - 1];
                }
            }

            queue_index[tail] = j + 1;
            ++tail;

            }

            if (head < tail) {
            int best_index = queue_index[head];

            int sell_candidate = *(dp + source_day * width + best_index) + best_index * bid_price - j * bid_price;

            if (sell_candidate > *(dp + i * width + j)) {
                *(dp + i * width + j) = sell_candidate;
            }
            }
        }
        int ask_price = ap[i - 1];
        int buy_cap = buy_limit[i - 1];
        head = 0;
        tail = 0;

        for (int j = 1; j <= max_stock; ++j) {

            while (head < tail && queue_index[head] + buy_cap < j) {
                ++head;
            }

            if (*(dp + source_day * width + (j - 1)) != neg_inf) {
            int last_index = j - 1;
            if (head < tail) {
                last_index = queue_index[tail - 1];
            }
            int incoming_score = *(dp + source_day * width + (j - 1)) + (j - 1) * ask_price;

            while (head < tail &&
                   *(dp + source_day * width + last_index) +
                       last_index * ask_price <= incoming_score) {
                --tail;
                if (head < tail) {
                    last_index = queue_index[tail - 1];
                }
            }

            queue_index[tail] = j - 1;
            ++tail;

            }

            if (head < tail) {
            int best_index = queue_index[head];

            int buy_candidate =
                *(dp + source_day * width + best_index) +
                best_index * ask_price - j * ask_price;

            if (buy_candidate > *(dp + i * width + j)) {
                *(dp + i * width + j) = buy_candidate;
            }
            }
        }

    }
    int answer = 0;

    for (int j = 0; j <= max_stock; ++j) {
        if (*(dp + days * width + j) > answer) {
            answer = *(dp + days * width + j);
        }
    }

    return answer;
}
