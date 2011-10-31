#ifndef MC_EXT_H
#define MC_EXT_H

#include "typeArray.h"

typedef struct Mc_ext__mc_tracks_prio_sorttracks_out {
  TypeTracks__tmissiontrack OutputTrack1;
  TypeTracks__tmissiontrack OutputTrack2;
  TypeTracks__tmissiontrack OutputTrack3;
  TypeTracks__tmissiontrack OutputTrack4;
} Mc_ext__mc_tracks_prio_sorttracks_out;

/* =============== */
/* CYCLIC FUNCTION */
/* =============== */
void Mc_ext__mc_tracks_prio_sorttracks(
 const TypeTracks__tmissiontrack *InputTrack1, const TypeTracks__tmissiontrack *InputTrack2,
 const TypeTracks__tmissiontrack *InputTrack3, const TypeTracks__tmissiontrack *InputTrack4,
 Mc_ext__mc_tracks_prio_sorttracks_out *out);

void Mc_ext__SortBlockPriorities(const TypeTracks__tmissiontrack *InputTrackA, const TypeTracks__tmissiontrack *InputTrackB, TypeTracks__tmissiontrack *OutputTrackA, TypeTracks__tmissiontrack *OutputTrackB);

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

