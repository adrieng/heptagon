/* Pervasives module for the Decades compiler */

#ifndef DECADES_PERVASIVES_H
#define DECADES_PERVASIVES_H

/* between(i, n) returns idx between 0 and n-1. */
static inline int between(int idx, int n)
{
  int o = (idx >= n) ? n-1 : (idx < 0 ? 0 : idx);
  return o;
}

#endif

