#include <math.h>
#include "mathext.h"

#define WRAP_FUN_DEF(FNAME, CNAME, TY_IN, TY_OUT) \
  void FNAME ## _step(TY_IN a, FNAME ## _out *out) { \
    out->o = CNAME(a); \
  }

WRAP_FUN_DEF(atanr, atan, float, float)
WRAP_FUN_DEF(acosr, acos, float, float)
WRAP_FUN_DEF(cosr, cos, float, float)
WRAP_FUN_DEF(asinr, asin, float, float)
WRAP_FUN_DEF(sinr, sin, float, float)
WRAP_FUN_DEF(sqrtr, sqrt, float, float)
