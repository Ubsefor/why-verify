#include <limits.h>
#include <stdio.h>
#include <stdlib.h>

#define IN
#define OUT

// "program" that is to be verified. z1 -- output arg in that case
void fn(IN int x1, IN int x2, IN int x3, OUT int* z1){
  int y1 = 0;
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
  int res;
  fn(4, 2, 3, &res);
  printf("Res: %d\n", res);
  return 0;
}