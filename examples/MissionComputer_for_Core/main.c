#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "debug.h"

void print_mission_track(TypeArray__tmissiontracksarray mt) {
  for(int i = 0; i < TypeArray__ksizemissiontracksarray; i++) {
    printf("track nb %d\n", i);
    printf("pos: x=%f -- y=%f \n", mt[i].m_pos.x, mt[i].m_pos.y);
    printf("speed: sx=%f -- sy=%f\n", mt[i].m_speed.sx, mt[i].m_speed.sy);
  }
}

/* fighterdebug(res, rdronoffclicked, iffonoffclicked)
   res est le reset: mettre a 1 le premier coup puis a 0

 */

int main(int argc, char** argv) {
  int step_c;
  int step_max;

  Debug__fighterdebug_mem _mem;
  Debug__fighterdebug_out _res;

  int res;
  int rdronoffclicked;
  int iffonoffclicked;

  step_c = 0;
  step_max = 0;
  if ((argc==2)) {
    step_max = atoi(argv[1]);
  };
  Debug__fighterdebug_reset(&_mem);

  Debug__fighterdebug_step(true, false, false, &_res, &_mem);
  Debug__fighterdebug_step(false, false, false, &_res, &_mem);
  Debug__fighterdebug_step(false, true, false, &_res, &_mem);
  Debug__fighterdebug_step(false, false, false, &_res, &_mem);
  Debug__fighterdebug_step(false, false, false, &_res, &_mem);
  Debug__fighterdebug_step(false, true, false, &_res, &_mem);
  Debug__fighterdebug_step(false, false, true, &_res, &_mem);
  Debug__fighterdebug_step(false, false, false, &_res, &_mem);
  Debug__fighterdebug_step(false, false, true, &_res, &_mem);
  Debug__fighterdebug_step(false, false, false, &_res, &_mem);

  printf("init:\n");
  printf("=> \n");
  print_mission_track(_res.missiontracks);
  fflush(stdout);

  while ((!(step_max)||(step_c<step_max))) {
    step_c = (step_c+1);

    /*
    printf("res ? ");
    scanf("%d", &res);;

    printf("rdronoffclicked ? ");
    scanf("%d", &rdronoffclicked);;

    printf("iffonoffclicked ? ");
    scanf("%d", &iffonoffclicked);;
    */

    Debug__fighterdebug_step(res, rdronoffclicked, iffonoffclicked, &_res,
                                &_mem);
    printf("=> \n");
    print_mission_track(_res.missiontracks);
    fflush(stdout);
  };
  return 0;
}

