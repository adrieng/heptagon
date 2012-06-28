(***********************************************************************)
(*                                                                     *)
(*                             Heptagon                                *)
(*                                                                     *)
(* Gwenael Delaval, LIG/INRIA, UJF                                     *)
(* Leonard Gerard, Parkas, ENS                                         *)
(* Adrien Guatto, Parkas, ENS                                          *)
(* Cedric Pasteur, Parkas, ENS                                         *)
(* Marc Pouzet, Parkas, ENS                                            *)
(*                                                                     *)
(* Copyright 2012 ENS, INRIA, UJF                                      *)
(*                                                                     *)
(* This file is part of the Heptagon compiler.                         *)
(*                                                                     *)
(* Heptagon is free software: you can redistribute it and/or modify it *)
(* under the terms of the GNU General Public License as published by   *)
(* the Free Software Foundation, either version 3 of the License, or   *)
(* (at your option) any later version.                                 *)
(*                                                                     *)
(* Heptagon is distributed in the hope that it will be useful,         *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of      *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the       *)
(* GNU General Public License for more details.                        *)
(*                                                                     *)
(* You should have received a copy of the GNU General Public License   *)
(* along with Heptagon.  If not, see <http://www.gnu.org/licenses/>    *)
(*                                                                     *)
(***********************************************************************)

open Clocks
open Types
open Idents
open Misc

let rec clock_compare ck1 ck2 = match ck1, ck2 with
  | Cvar { contents = Clink ck1; }, _ -> clock_compare ck1 ck2
  | _, Cvar { contents = Clink ck2; } -> clock_compare ck1 ck2
  | Cbase, Cbase -> 0
  | Cvar lr1, Cvar lr2 -> link_compare !lr1 !lr2
  | Con (ck1, cn1, vi1), Con (ck2, cn2, vi2) ->
      let cr1 = compare cn1 cn2 in
      if cr1 <> 0 then cr1 else
        let cr2 = ident_compare vi1 vi2 in
        if cr2 <> 0 then cr2 else clock_compare ck1 ck2
  | Cbase , _ -> 1

  | Cvar _, Cbase -> -1
  | Cvar _, _ -> 1

  | Con _, _ -> -1

and link_compare li1 li2 = match li1, li2 with
  | Cindex _, Cindex _ -> 0
  | Clink ck1, Clink ck2 -> clock_compare ck1 ck2
  | Cindex _, _ -> 1
  | Clink _, _ -> -1


let rec static_exp_compare se1 se2 =
  let cr = type_compare se1.se_ty se2.se_ty in
  if cr <> 0 then cr else static_exp_desc_compare se1.se_desc se2.se_desc


and static_exp_desc_compare sed1 sed2 =
  let c = Pervasives.compare in
  match sed1, sed2 with
    | Svar cn1, Svar cn2 -> Pervasives.compare cn1 cn2
    | Sint i1, Sint i2 -> c i1 i2
    | Sfloat f1, Sfloat f2 -> c f1 f2
    | Sbool b1, Sbool b2 -> c b1 b2
    | Sstring s1, Sstring s2 -> c s1 s2
    | Sconstructor c1, Sconstructor c2 -> c c1 c2
    | Sfield f1, Sfield f2 -> c f1 f2
    | Stuple sel1, Stuple sel2 ->
        list_compare static_exp_compare sel1 sel2
    | Sarray_power (se11, sel1), Sarray_power (se12, sel2) ->
        let cr = static_exp_compare se11 se12 in
        if cr <> 0 then cr else list_compare static_exp_compare sel1 sel2
    | Sarray sel1, Sarray sel2 ->
        list_compare static_exp_compare sel1 sel2
    | Srecord fnsel1, Srecord fnsel2 ->
        let compare_field (fn1, se1) (fn2, se2) =
          let cr = c fn1 fn2 in
          if cr <> 0 then cr else static_exp_compare se1 se2 in
        list_compare compare_field fnsel1 fnsel2
    | Sop (fn1, sel1), Sop (fn2, sel2) ->
        let cr = c fn1 fn2 in
        if cr <> 0 then cr else list_compare static_exp_compare sel1 sel2

    | Svar _, _ -> 1

    | Sint _, Svar _ -> -1
    | Sint _, _ -> 1

    | Sfloat _, (Svar _ | Sint _) -> -1
    | Sfloat _, _ -> 1

    | Sbool _, (Svar _ | Sint _ | Sfloat _) -> -1
    | Sbool _, _ -> 1

    | Sstring _, (Svar _ | Sint _ | Sfloat _ | Sbool _) -> -1
    | Sstring _, _ -> 1

    | Sconstructor _, (Svar _ | Sint _ | Sfloat _ | Sbool _ | Sstring _) -> -1
    | Sconstructor _, _ -> 1

    | Sfield _, (Svar _ | Sint _ | Sfloat _ | Sbool _ | Sstring _ | Sconstructor _) -> -1
    | Sfield _, _ -> 1

    | Stuple _, (Srecord _ | Sop _ | Sarray _ | Sarray_power _ ) -> 1
    | Stuple _, _ -> -1

    | Sarray_power _, (Srecord _ | Sop _ | Sarray _) -> -1
    | Sarray_power _, _ -> 1

    | Sarray _, (Srecord _ | Sop _) -> 1
    | Sarray _, _ -> -1

    | Srecord _, Sop _ -> 1
    | Srecord _, _ -> -1

    | Sop _, _ -> -1

and type_compare ty1 ty2 = match ty1, ty2 with
  | Tprod tyl1, Tprod tyl2 -> list_compare type_compare tyl1 tyl2
  | Tid tyn1, Tid tyn2 -> Pervasives.compare tyn1 tyn2
  | Tarray (ty1, se1), Tarray (ty2, se2) ->
      let cr = type_compare ty1 ty2 in
      if cr <> 0 then cr else static_exp_compare se1 se2
  | Tinvalid, _ | _, Tinvalid -> -1
  | Tprod _, _ -> 1
  | Tid _, Tprod _ -> -1
  | Tid _, _ -> 1
  | Tarray _, (Tprod _ | Tid _) -> -1
