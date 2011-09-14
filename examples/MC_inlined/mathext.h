#ifndef MATHEXT_H
#define MATHEXT_H

#define WRAP_FUN_DECL(FNAME, TY_IN, TY_OUT) \
  typedef struct { \
    TY_OUT o; \
  } FNAME ## _out; \
  \
  void FNAME ## _step(TY_IN, FNAME ## _out *)

WRAP_FUN_DECL(Mathext__atanr, float, float);
WRAP_FUN_DECL(Mathext__acosr, float, float);
WRAP_FUN_DECL(Mathext__cosr, float, float);
WRAP_FUN_DECL(Mathext__asinr, float, float);
WRAP_FUN_DECL(Mathext__sinr, float, float);
WRAP_FUN_DECL(Mathext__sqrtr, float, float);

#endif
