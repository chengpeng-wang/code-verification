#include <stddef.h>
#include <stdint.h>

size_t quicksort_partition(volatile uint8_t *a, size_t n);

// Sort n bytes in place. For n >= 2, a points to n readable and writable bytes.
void quicksort_u8(volatile uint8_t *a, size_t n) {
    if (n < 2) {
        return;
    }

    size_t pivot = quicksort_partition(a, n);
    quicksort_u8(a, pivot);
    quicksort_u8(a + pivot + 1, n - pivot - 1);
}
