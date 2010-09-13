#include <math.h>
#include <stdlib.h>
#include "mc_ext.h"

/*$**************************************
NAME : MC_Tracks_Prio_SortTracks
INPUTS :
InputTrack1 : TMissionTrack
InputTrack2 : TMissionTrack
InputTrack3 : TMissionTrack
InputTrack4 : TMissionTrack
OUPUTS :
OutputTrack1 : TMissionTrack
OutputTrack2 : TMissionTrack
OutputTrack3 : TMissionTrack
OutputTrack4 : TMissionTrack
***************************************$*/

void mc_tracks_prio_sorttracks(
 const TMissionTrack *InputTrack1, const TMissionTrack *InputTrack2,
 const TMissionTrack *InputTrack3, const TMissionTrack *InputTrack4,
 mc_tracks_prio_sorttracks_out *out)
{
    TMissionTrack _LO1_newA = *InputTrack1;
    TMissionTrack _LO1_newB = *InputTrack1;
    TMissionTrack _LO2_newA = *InputTrack1;
    TMissionTrack _LO2_newB = *InputTrack1;
    TMissionTrack _LO3_newA = *InputTrack1;
    TMissionTrack _LO3_newB = *InputTrack1;
    TMissionTrack _LO4_newA = *InputTrack1;
    TMissionTrack _LO4_newB = *InputTrack1;
    TMissionTrack _LO5_newA = *InputTrack1;
    TMissionTrack _LO5_newB = *InputTrack1;
    TMissionTrack _LO6_newA = *InputTrack1;
    TMissionTrack _LO6_newB = *InputTrack1;

    TMissionTrack _LI_A = *InputTrack1;
    TMissionTrack _LI_B = *InputTrack2;

    SortBlockPriorities(&_LI_A, &_LI_B, &_LO4_newA, &_LO4_newB);

    _LI_A = *InputTrack3;
    _LI_B = *InputTrack4;
    SortBlockPriorities(&_LI_A, &_LI_B, &_LO6_newA, &_LO6_newB);

    SortBlockPriorities(&_LO4_newB, &_LO6_newA, &_LO2_newA, &_LO2_newB);

    SortBlockPriorities(&_LO4_newA, &_LO2_newA, &_LO1_newA, &_LO1_newB);

    out->OutputTrack1 = _LO1_newA;

    SortBlockPriorities(&_LO2_newB, &_LO6_newB, &_LO5_newA, &_LO5_newB);

    SortBlockPriorities(&_LO1_newB, &_LO5_newA, &_LO3_newA, &_LO3_newB);

    out->OutputTrack2 = _LO3_newA;
    out->OutputTrack3 = _LO3_newB;
    out->OutputTrack4 = _LO5_newB;
}

/* ROLE :,
Sort two mission tracks according to:,
1) their (rate of closing / distance) ratio,
2) target type,
3) detection or not by the Radar */
void SortBlockPriorities(const TMissionTrack *InputTrackA, const TMissionTrack *InputTrackB, TMissionTrack *OutputTrackA, TMissionTrack *OutputTrackB)
{
    bool bInvertTracks = false;
	real vrDivDResultTrackA = 0.0;
	real vrDivDResultTrackB = 0.0;

    vrDivDResultTrackA = CalculateVrDivD(InputTrackA->Vr, InputTrackA->D);
    vrDivDResultTrackB = CalculateVrDivD(InputTrackB->Vr, InputTrackB->D);

    bInvertTracks = (InputTrackA->targetType == TTargetType_FRIEND);
	bInvertTracks = bInvertTracks || !(InputTrackA->detectedByRadar);
	if ( ( fabs(vrDivDResultTrackA) < 0.0001 ) && ( fabs(vrDivDResultTrackB) < 0.0001 ) ) {
		bInvertTracks = bInvertTracks ||
			( (InputTrackA->detectedByRadar) &&
			  (InputTrackB->detectedByRadar) &&
			  ( InputTrackA->D > InputTrackB->D ) );

	} else {
		bInvertTracks = bInvertTracks ||
			( (InputTrackA->detectedByRadar) &&
			  (InputTrackB->detectedByRadar) &&
			  (vrDivDResultTrackA < vrDivDResultTrackB) );
	}

    if (bInvertTracks) {
		*OutputTrackA = *InputTrackB;
		*OutputTrackB = *InputTrackA;
    } else {
		*OutputTrackA = *InputTrackA;
		*OutputTrackB = *InputTrackB;
    }
}

/* ROLE :,
Calculate: result = rate of closing / distance */
real CalculateVrDivD(const float _I0_Vr, const float _I1_D)
{
    bool bDIsNotZero = (_I1_D > 0.1);

    if (bDIsNotZero) {
	  return ( _I0_Vr / _I1_D ) ;
    } else {
	  return ( 0.0 );
    }
}

void rand_step(rand_out *out)
{
  float a = (float)(rand());
  kcg_real b = (float)RAND_MAX;
  out->o = a/b;
}

void int_of_float_step(float a, int_of_float_out *out)
{
  return (int) a;
}

void float_of_int_step(int a, int_of_float_out *out)
{
  return (float) a;
}
