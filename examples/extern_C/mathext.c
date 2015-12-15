#include <math.h>
#include "mathext.h"

void Mathext__mycos_step(float a, Mathext__mycos_out *out)
{
  out->o = cosf(a);
}

void Mathext__st_cos_reset(Mathext__st_cos_mem *self)
{
  int j;
  self->i = 0;
  for(j = 0; j < 100; ++j)
    self->mem[j] = 0.0;
}

void Mathext__st_cos_step(float a, Mathext__st_cos_out *out, Mathext__st_cos_mem *self)
{
  out->o = self->mem[self->i];
  self->i = (self->i+1) % 100;
  self->mem[self->i] = cosf(a);
}
