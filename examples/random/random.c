
#include <stdlib.h>
#include "random.h"

void Random__random_step(Random__random_out *o) {
  o->z = ((double)random())/((double)RAND_MAX);
}

