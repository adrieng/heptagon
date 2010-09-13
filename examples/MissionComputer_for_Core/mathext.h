#ifndef MATHEXT_H
#define MATHEXT_H

#define WRAP_FUN_DECL(FNAME, TY_IN, TY_OUT) \
  typedef struct { \
    TY_OUT o; \
  } FNAME ## _out; \
  \
  void FNAME ## _step(TY_IN, FNAME ## _out *)

WRAP_FUN_DECL(atanr, float, float);
WRAP_FUN_DECL(acosr, float, float);
WRAP_FUN_DECL(cosr, float, float);
WRAP_FUN_DECL(asinr, float, float);
WRAP_FUN_DECL(sinr, float, float);
WRAP_FUN_DECL(sqrtr, float, float);

#endif
