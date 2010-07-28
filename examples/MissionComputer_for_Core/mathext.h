#ifndef MATHEXT_H
#define MATHEXT_H

/* atan(x) */
typedef struct atanr_out {
  float o;
} atanr_out;

void atanr_step(float a, atanr_out *o);

/* acos(x) */
typedef struct acosr_out {
  float o;
} acosr_out;

void acosr_step(float a, acosr_out *o);

/* cos(x) */
typedef struct cosr_out {
  float o;
} cosr_out;

void cosr_step(float a, cosr_out *o);

/* asin(x) */
typedef struct asinr_out {
  float o;
} asinr_out;

void asinr_step(float a, asinr_out *o);

/* sin(x) */
typedef struct sinr_out {
  float o;
} sinr_out;

void sinr_step(float a, sinr_out *o);

/* sin(x) */
typedef struct sqrtr_out {
  float o;
} sqrtr_out;

void sqrtr_step(float a, sqrtr_out *o);

#endif
