#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

int maxAreaLinear(const int *height, int heightSize)

{
    int left;
    int right;
    int maximumArea;

    if (height == 0 || heightSize < 2) {
        return 0;
    }

    left = 0;
    right = heightSize - 1;
    maximumArea = 0;

    while (left < right) {
        int width = right - left;
        int shorterHeight;
        int area;

        if (height[left] < height[right]) {
            shorterHeight = height[left];
        } else {
            shorterHeight = height[right];
        }

        area = width * shorterHeight;
        if (area > maximumArea) {
            maximumArea = area;
        }

        if (height[left] < height[right]) {
            ++left;
        } else {
            --right;
        }
    }

    return maximumArea;
}
