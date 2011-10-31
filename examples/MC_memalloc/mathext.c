#include <math.h>
#include "mathext.h"

#define WRAP_FUN_DEF(FNAME, CNAME, TY_IN, TY_OUT) \
  void FNAME ## _step(TY_IN a, FNAME ## _out *out) { \
    out->o = CNAME(a); \
  }

WRAP_FUN_DEF(Mathext__atanr, atan, float, float)
WRAP_FUN_DEF(Mathext__acosr, acos, float, float)
WRAP_FUN_DEF(Mathext__cosr, cos, float, float)
WRAP_FUN_DEF(Mathext__asinr, asin, float, float)
WRAP_FUN_DEF(Mathext__sinr, sin, float, float)
WRAP_FUN_DEF(Mathext__sqrtr, sqrt, float, float)
