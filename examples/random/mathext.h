
#ifndef MATHEXT_H
#define MATHEXT_H


/* Example of a combinatorial function */
typedef struct Mathext__power_out {
  float y;
} Mathext__power_out;

void Mathext__power_step(float x, int n, Mathext__power_out *o);

#endif

