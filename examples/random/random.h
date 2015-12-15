
#ifndef RANDOM_H
#define RANDOM_H


/* Example of a combinatorial function */
typedef struct Random__random_out {
  float z;
} Random__random_out;

void Random__random_step(Random__random_out *o);

#endif

