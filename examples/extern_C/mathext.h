#ifndef MATHEXT_H
#define MATHEXT_H

/* Example of a combinatorial function */
typedef struct mycos_out {
  float o;
} mycos_out;

void mycos_step(float a, mycos_out *o);

/* Example of a statefull function. */
typedef struct st_cos_out {
  float o;
} st_cos_out;

typedef struct st_cos_mem {
  int i;
  float mem[100];
} st_cos_mem;

void st_cos_reset(st_cos_mem *self);
void st_cos_step(float a, st_cos_out *out, st_cos_mem *self);

#endif

