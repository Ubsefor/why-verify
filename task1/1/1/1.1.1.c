#include <limits.h>
#include <stdio.h>

// "program" that is to be verified. z1 -- output arg in that case
int* fn(int x1, int x2, int x3, int* z1){
  *z1 = x1 + x2 - x3;
  return z1;
}

// helper/runner for fn()
int main(int argc, char* argv[]){
  int res = 0;
  res = fn(1, 2, 3, res);
  printf("Res: %d\n", res);
}
