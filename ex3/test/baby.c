#include "../include/Verifier.h"

int main() {
  int x = input();
  if (x > 0)
    x = 2;
  assume(x > 1);
  assert(x > 0);
  return 0;
}