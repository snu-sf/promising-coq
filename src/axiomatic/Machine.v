(******************************************************************************)
(** * Definitions of the axiomatic machine   *)
(******************************************************************************)

Require Import Classical List Relations Peano_dec.
Require Import sflib.
Require Import paco.
Require Import Hahn.

Require Import Axioms.
Require Import Basic.
Require Import Language.
Require Import Event.
Require Import Time.
Require Import Configuration.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import Thread.
Require Import Commit.

Require Import Gevents.
Require Import model.
Require Import Gsteps.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section Operational. 

Record configuration := 
  { ts : IdentMap.t {lang:Language.t & lang.(Language.state)};
    acts : list event ;
    sb : event -> event -> Prop ; 
    rmw : event -> event -> Prop ; 
    rf : event -> event -> Prop ; 
    mo : event -> event -> Prop ; 
    sc : event -> event -> Prop }.

Inductive mstep mc mc' e i : Prop :=
  | silent (SILENT: e = None) 
      (SAME_ACTS: acts mc = acts mc')
      (SAME_SB: sb mc = sb mc') 
      (SAME_RMW: rmw mc = rmw mc') 
      (SAME_RF: rf mc = rf mc')
      (SAME_MO: mo mc = mo mc') 
      (SAME_SC: sc mc = sc mc')
  | read a l v o 
      (EVENT: e = Some (ProgramEvent.read l v o)) 
      (LABa: lab a = Aload l v o) 
      (TIDa: thread a = i) 
      (GSTEP: gstep (acts mc) (sb mc) (rmw mc) (rf mc) (mo mc) (sc mc)
                    (acts mc') (sb mc') (rmw mc') (rf mc') (mo mc') (sc mc') a)
  | write a l v o 
      (EVENT: e = Some (ProgramEvent.write l v o)) 
      (LABa: lab a = Astore l v o) 
      (TIDa: thread a = i) 
      (GSTEP: gstep (acts mc) (sb mc) (rmw mc) (rf mc) (mo mc) (sc mc)
                    (acts mc') (sb mc') (rmw mc') (rf mc') (mo mc') (sc mc') a)
  | update a_r a_w l v_r v_w o_r o_w 
      (EVENT: e = Some (ProgramEvent.update l v_r v_w o_r o_w)) 
      (LABar: lab a_r = Aload l v_r o_r) (LABaw: lab a_w = Astore l v_w o_w) 
      (TIDar: thread a_r = i) (TIDaw: thread a_w = i) 
      mc_mid
      (GSTEPr: gstep (acts mc) (sb mc) (rmw mc) (rf mc) (mo mc) (sc mc)
           (acts mc_mid) (sb mc_mid) (rmw mc_mid) (rf mc_mid) (mo mc_mid) (sc mc_mid) a_r)
      (GSTEPw: gstep (acts mc_mid) (sb mc_mid) (rmw mc_mid) (rf mc_mid) (mo mc_mid) (sc mc_mid)
                     (acts mc') (sb mc') (rmw mc') (rf mc') (mo mc') (sc mc') a_w)
  | fence a o_r o_w (EVENT: e = Some (ProgramEvent.fence o_r o_w)) 
      (LABa: lab a = Afence o_r o_w) 
      (TIDa: thread a = i) 
      (GSTEP: gstep (acts mc) (sb mc) (rmw mc) (rf mc) (mo mc) (sc mc)
                    (acts mc') (sb mc') (rmw mc') (rf mc') (mo mc') (sc mc') a).

Inductive step mc mc' : Prop :=
| step_intro  
    lang st st' i e
    (TID: IdentMap.find i (ts mc) = Some (existT _ lang st))
    (STATE: lang.(Language.step) e st st')
    (MTS: ts mc' = IdentMap.add i (existT _ _ st') (ts mc))
    (MSTEP: mstep mc mc' e i)
.

End Operational.

