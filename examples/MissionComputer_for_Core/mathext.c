#include <math.h>
#include "mathext.h"

void atanr_step(float a, atanr_out *out)
{
  out->o = atan(a);
}

void acosr_step(float a, acosr_out *out)
{
  out->o = acos(a);
}

void cosr_step(float a, cosr_out *out)
{
  out->o = cos(a);
}

void asinr_step(float a, asinr_out *out)
{
  out->o = asin(a);
}

void sinr_step(float a, sinr_out *out)
{
  out->o = sin(a);
}

void sqrtr_step(float a, sqrtr_out *out)
{
  out->o = sqrt(a);
}
