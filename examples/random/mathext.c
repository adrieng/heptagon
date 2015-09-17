
#include <stdlib.h>
#include "mathext.h"

void Mathext__power_step(float x, int n, Mathext__power_out *o) {
  float r;
  int i;

  r = 1.0;
  for (i = 1; i <= n; i++) {
    r = r * x;
  }
  o->y = r;
}

