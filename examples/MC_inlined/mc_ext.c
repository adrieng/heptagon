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
 const Mctypes__tmissiontrack *InputTrack1, const Mctypes__tmissiontrack *InputTrack2,
 const Mctypes__tmissiontrack *InputTrack3, const Mctypes__tmissiontrack *InputTrack4,
 Mc_ext__mc_tracks_prio_sorttracks_out *out)
{
    Mctypes__tmissiontrack _LO1_newA = *InputTrack1;
    Mctypes__tmissiontrack _LO1_newB = *InputTrack1;
    Mctypes__tmissiontrack _LO2_newA = *InputTrack1;
    Mctypes__tmissiontrack _LO2_newB = *InputTrack1;
    Mctypes__tmissiontrack _LO3_newA = *InputTrack1;
    Mctypes__tmissiontrack _LO3_newB = *InputTrack1;
    Mctypes__tmissiontrack _LO4_newA = *InputTrack1;
    Mctypes__tmissiontrack _LO4_newB = *InputTrack1;
    Mctypes__tmissiontrack _LO5_newA = *InputTrack1;
    Mctypes__tmissiontrack _LO5_newB = *InputTrack1;
    Mctypes__tmissiontrack _LO6_newA = *InputTrack1;
    Mctypes__tmissiontrack _LO6_newB = *InputTrack1;

    Mctypes__tmissiontrack _LI_A = *InputTrack1;
    Mctypes__tmissiontrack _LI_B = *InputTrack2;

    Mc_ext__SortBlockPriorities(&_LI_A, &_LI_B, &_LO4_newA, &_LO4_newB);

    _LI_A = *InputTrack3;
    _LI_B = *InputTrack4;
    Mc_ext__SortBlockPriorities(&_LI_A, &_LI_B, &_LO6_newA, &_LO6_newB);

    Mc_ext__SortBlockPriorities(&_LO4_newB, &_LO6_newA, &_LO2_newA, &_LO2_newB);

    Mc_ext__SortBlockPriorities(&_LO4_newA, &_LO2_newA, &_LO1_newA, &_LO1_newB);

    out->OutputTrack1 = _LO1_newA;

    Mc_ext__SortBlockPriorities(&_LO2_newB, &_LO6_newB, &_LO5_newA, &_LO5_newB);

    Mc_ext__SortBlockPriorities(&_LO1_newB, &_LO5_newA, &_LO3_newA, &_LO3_newB);

    out->OutputTrack2 = _LO3_newA;
    out->OutputTrack3 = _LO3_newB;
    out->OutputTrack4 = _LO5_newB;
}

/* ROLE :,
Sort two mission tracks according to:,
1) their (rate of closing / distance) ratio,
2) target type,
3) detection or not by the Radar */
void Mc_ext__SortBlockPriorities(const Mctypes__tmissiontrack *InputTrackA, const Mctypes__tmissiontrack *InputTrackB, Mctypes__tmissiontrack *OutputTrackA, Mctypes__tmissiontrack *OutputTrackB)
{
    bool bInvertTracks = false;
    float vrDivDResultTrackA = 0.0;
    float vrDivDResultTrackB = 0.0;

    vrDivDResultTrackA = Mc_ext__CalculateVrDivD(InputTrackA->m_sr, InputTrackA->m_d);
    vrDivDResultTrackB = Mc_ext__CalculateVrDivD(InputTrackB->m_sr, InputTrackB->m_d);

    bInvertTracks = (InputTrackA->m_targettype == Mctypes__Ttargettype_unknown);
	bInvertTracks = bInvertTracks || !(InputTrackA->m_detectedbyradar);
	if ( ( fabs(vrDivDResultTrackA) < 0.0001 ) && ( fabs(vrDivDResultTrackB) < 0.0001 ) ) {
		bInvertTracks = bInvertTracks ||
			( (InputTrackA->m_detectedbyradar) &&
			  (InputTrackB->m_detectedbyradar) &&
			  ( InputTrackA->m_d > InputTrackB->m_d ) );

	} else {
		bInvertTracks = bInvertTracks ||
			( (InputTrackA->m_detectedbyradar) &&
			  (InputTrackB->m_detectedbyradar) &&
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
float Mc_ext__CalculateVrDivD(const float _I0_Vr, const float _I1_D)
{
    bool bDIsNotZero = (_I1_D > 0.1);

    if (bDIsNotZero) {
	  return ( _I0_Vr / _I1_D ) ;
    } else {
	  return ( 0.0 );
    }
}

void Mc_ext__rand_step(Mc_ext__rand_out *out)
{
  float a = (float)(rand());
  float b = (float)RAND_MAX;
  out->o = a/b;
}

void Mc_ext__int_of_float_step(float a, Mc_ext__int_of_float_out *out)
{
  out->o = (int) a;
}

void Mc_ext__float_of_int_step(int a, Mc_ext__float_of_int_out *out)
{
  out->o = (float) a;
}
