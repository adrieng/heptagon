#ifndef MC_EXT_H
#define MC_EXT_H

#include "typeArray_types.h"

typedef struct mc_tracks_prio_sorttracks_out {
  TMissionTrack OutputTrack1;
  TMissionTrack OutputTrack2;
  TMissionTrack OutputTrack3;
  TMissionTrack OutputTrack4;
} mc_tracks_prio_sorttracks_out;

/* =============== */
/* CYCLIC FUNCTION */
/* =============== */
void mc_tracks_prio_sorttracks(
 const TMissionTrack *InputTrack1, const TMissionTrack *InputTrack2,
 const TMissionTrack *InputTrack3, const TMissionTrack *InputTrack4,
 mc_tracks_prio_sorttracks_out *out);

void SortBlockPriorities(const TMissionTrack *InputTrackA, const TMissionTrack *InputTrackB, TMissionTrack *OutputTrackA, TMissionTrack *OutputTrackB);

real CalculateVrDivD(const float _I0_Vr, const float _I1_D);


/* rand() */
typedef struct {
  float o;
} rand_out;

void rand_step(rand_out *out);

/* int_of_float */
typedef struct {
  int o;
} int_of_float_out;

void int_of_float_step(float a, int_of_float_out *out);

/* float_of_int */
typedef struct {
  float o;
} float_of_int_out;

void float_of_int_step(int a, float_of_int_out *out);

#endif

