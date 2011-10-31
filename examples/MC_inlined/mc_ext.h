#ifndef MC_EXT_H
#define MC_EXT_H

#include "mctypes.h"

typedef struct Mc_ext__mc_tracks_prio_sorttracks_out {
  Mctypes__tmissiontrack OutputTrack1;
  Mctypes__tmissiontrack OutputTrack2;
  Mctypes__tmissiontrack OutputTrack3;
  Mctypes__tmissiontrack OutputTrack4;
} Mc_ext__mc_tracks_prio_sorttracks_out;

/* =============== */
/* CYCLIC FUNCTION */
/* =============== */
void Mc_ext__mc_tracks_prio_sorttracks(
 const Mctypes__tmissiontrack *InputTrack1, const Mctypes__tmissiontrack *InputTrack2,
 const Mctypes__tmissiontrack *InputTrack3, const Mctypes__tmissiontrack *InputTrack4,
 Mc_ext__mc_tracks_prio_sorttracks_out *out);

void Mc_ext__SortBlockPriorities(const Mctypes__tmissiontrack *InputTrackA, const Mctypes__tmissiontrack *InputTrackB, Mctypes__tmissiontrack *OutputTrackA, Mctypes__tmissiontrack *OutputTrackB);

float Mc_ext__CalculateVrDivD(const float _I0_Vr, const float _I1_D);


/* rand() */
typedef struct {
  float o;
} Mc_ext__rand_out;

void Mc_ext__rand_step(Mc_ext__rand_out *out);

/* int_of_float */
typedef struct {
  int o;
} Mc_ext__int_of_float_out;

void Mc_ext__int_of_float_step(float a, Mc_ext__int_of_float_out *out);

/* float_of_int */
typedef struct {
  float o;
} Mc_ext__float_of_int_out;

void Mc_ext__float_of_int_step(int a, Mc_ext__float_of_int_out *out);

#endif

