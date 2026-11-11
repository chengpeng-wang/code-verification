#include <stddef.h>
#include <stdint.h>

// Partition a nonempty array around its original first element. Return the
// pivot's new index. Smaller elements precede it; the rest follow it.
size_t quicksort_partition(volatile uint8_t *a, size_t n) {
    uint8_t pivot = a[0];
    size_t left = 0;

    for (size_t i = 1; i < n; ++i) {
        uint8_t value = a[i];
        if (value < pivot) {
            ++left;
            uint8_t previous = a[left];
            a[left] = value;
            a[i] = previous;
        }
    }

    uint8_t previous = a[left];
    a[0] = previous;
    a[left] = pivot;
    return left;
}
