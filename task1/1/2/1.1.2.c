#include <limits.h> // assuming INT_MAX == 2^31 - 1 and INT_MIN == -2^31
#include <stdio.h>
#include <stdlib.h>

#define IN
#define OUT

#ifdef DEBUG
    #define DEBUG_PRINTF(...) printf("DEBUG: "__VA_ARGS__)
#else
    #define DEBUG_PRINTF(...) do {} while (0)
#endif

// "program" that is to be verified. z1 -- output arg in that case
void fn(IN int x1, IN int x2, IN int x3, OUT int* z1){
  int64_t y1 = 0;

  if (
    (INT_MAX <= x1 && x1 >= INT_MIN) &&
    (INT_MAX <= x2 && x2 >= INT_MIN) &&
    (INT_MAX <= x3 && x3 >= INT_MIN)
  ) {
    while(1);
  }

  while (1) {
    // x1 + x2 -> y1
    if (!(
      (
        (x1 > 0) &&
        (x2 > 0) &&
        (INT_MAX - x2 < x1)
      ) ||
      (
        (x1 < 0) &&
        (x2 < 0) &&
        (INT_MIN - x2 > x1)
      )
    )) {
      DEBUG_PRINTF("x1 + x2\n");
      y1 = x1 + x2;
      // y1 - x3 -> y1
      if (!(
        (
          (y1 > 0) &&
          (-x3 > 0) &&
          (INT_MAX + x3 < y1)
        ) ||
        (
          (y1 < 0) &&
          (-x3 < 0) &&
          (INT_MIN + x3 > y1)
        )
      )) {
        DEBUG_PRINTF("y1 - x3\n");
        y1 = y1 - x3;
        *z1 = y1;
        return;
      }
    }

    // x1 - x3 -> y1
    if (!(
      (
        (x1 > 0) &&
        (-x3 > 0) &&
        (INT_MAX + x3 < x1)
      ) ||
      (
        (x1 < 0) &&
        (-x3 < 0) &&
        (INT_MIN + x3 > x1)
      )
    )) {
      DEBUG_PRINTF("x1 - x3\n");
      y1 = x1 - x3;
      // y1 + x2 -> y1
      if (!(
        (
          (y1 > 0) &&
          (x2 > 0) &&
          (INT_MAX - x2 < y1)
        ) ||
        (
          (y1 < 0) &&
          (x2 < 0) &&
          (INT_MIN - x2 > y1)
        )
      )){
        DEBUG_PRINTF("y1 + x2\n");
        y1 = y1 + x2;
        *z1 = y1;
        return;
      }
    }

    // x2 - x3 -> y1
    if (!(
      (
        (x2 > 0) &&
        (-x3 > 0) &&
        (INT_MAX + x3 < x2)
      ) ||
      (
        (x2 < 0) &&
        (-x3 < 0) &&
        (INT_MIN + x3 > x2)
      )
    )) {
      DEBUG_PRINTF("x2 - x3\n");
      y1 = x2 - x3;
      // y1 + x1 -> y1
      if (!(
        (
          (y1 > 0) &&
          (x1 > 0) &&
          (INT_MAX - x1 < y1)
        ) ||
        (
          (y1 < 0) &&
          (x1 < 0) &&
          (INT_MIN - x1 > y1)
        )
      )){
        DEBUG_PRINTF("y1 + x1\n");
        y1 = y1 + x1;
        *z1 = y1;
        return;
      }
    }
  }
}

// helper/runner for fn()
int main(IN int argc, IN char* argv[]){
  int res;
  fn(4, 2, 3, &res);
  DEBUG_PRINTF("Res: %d\n", res);
  return 0;
}