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
void fn(IN int64_t x1, IN int64_t x2, IN int64_t x3, OUT int64_t* z1){
  int64_t y1 = 0;

  if (
    (INT_MAX <= x1 && x1 >= INT_MIN) &&
    (INT_MAX <= x2 && x2 >= INT_MIN) &&
    (INT_MAX <= x3 && x3 >= INT_MIN)
  ) {
    while(1);
  }

  y1 = x1 - x3;
  if (!(y1 <= INT_MAX && y1 >= INT_MIN)){
    while (1);
  }
  y1 = y1 + x2;
  if (!(y1 <= INT_MAX && y1 >= INT_MIN)){
    while (1);
  }
  *z1 = y1;
}

// helper/runner for fn()
int main(IN int argc, IN char* argv[]){
  int64_t res;
  fn(4, 2, 3, &res);
  DEBUG_PRINTF("Res: %lld\n", res);
  return 0;
}