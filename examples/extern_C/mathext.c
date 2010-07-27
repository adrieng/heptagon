#include <math.h>
#include "mathext.h"

void mycos_step(float a, mycos_out *out)
{
  out->o = cos(a);
}

void st_cos_reset(st_cos_mem *self)
{
  self->i = 0;
  for(int j = 0; j < 100; ++j)
    self->mem[j] = 0.0;
}

void st_cos_step(float a, st_cos_out *out, st_cos_mem *self)
{
  out->o = self->mem[self->i];
  self->i = (self->i++) % 100;
  self->mem[self->i] = cos(a);
}
