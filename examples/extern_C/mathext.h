#ifndef MATHEXT_H
#define MATHEXT_H

/* Example of a combinatorial function */
typedef struct Mathext__mycos_out {
  float o;
} Mathext__mycos_out;

void Mathext__mycos_step(float a, Mathext__mycos_out *o);

/* Example of a statefull function. */
typedef struct Mathext__st_cos_out {
  float o;
} Mathext__st_cos_out;

typedef struct Mathext__st_cos_mem {
  int i;
  float mem[100];
} Mathext__st_cos_mem;

void Mathext__st_cos_reset(Mathext__st_cos_mem *self);
void Mathext__st_cos_step(float a, Mathext__st_cos_out *out, Mathext__st_cos_mem *self);

#endif

