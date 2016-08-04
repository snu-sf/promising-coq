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
Require Import TView.

Require Import Gevents.
Require Import model.
Require Import Gstep.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section Operational. 

Record execution := 
  { acts : list event ;
    sb : event -> event -> Prop ; 
    rmw : event -> event -> Prop ; 
    rf : event -> event -> Prop ; 
    mo : event -> event -> Prop ; 
    sc : event -> event -> Prop }.

(* Definition Coherent_exec G :=
  Coherent (acts G) (sb G) (rmw G) (rf G) (mo G) (sc G).
 *)
Record configuration := 
  { ts : IdentMap.t {lang:Language.t & lang.(Language.state)};
    exec : execution }.

Inductive mstep G G' e i : Prop :=
  | silent (SILENT: e = None) (SAME_EXEC: G' = G)
  | read a l v o 
      (EVENT: e = Some (ProgramEvent.read l v o)) 
      (LABa: lab a = Aload l v o) 
      (TIDa: thread a = i) 
      (GSTEP: gstep (acts G) (sb G) (rmw G) (rf G) (mo G) (sc G)
                    (acts G') (sb G') (rmw G') (rf G') (mo G') (sc G') a a)
      (COH': Coherent (acts G') (sb G') (rmw G') (rf G') (mo G') (sc G'))
  | write a l v o 
      (EVENT: e = Some (ProgramEvent.write l v o)) 
      (LABa: lab a = Astore l v o) 
      (TIDa: thread a = i) 
      (GSTEP: gstep (acts G) (sb G) (rmw G) (rf G) (mo G) (sc G)
                    (acts G') (sb G') (rmw G') (rf G') (mo G') (sc G') a a)
      (COH': Coherent (acts G') (sb G') (rmw G') (rf G') (mo G') (sc G'))
  | update a_r a_w l v_r v_w o_r o_w 
      (EVENT: e = Some (ProgramEvent.update l v_r v_w o_r o_w)) 
      (LABar: lab a_r = Aload l v_r o_r) (LABaw: lab a_w = Astore l v_w o_w) 
      (SC_IMPL_ACQ: is_sc a_w -> is_acq a_r)
      (TIDar: thread a_r = i) (TIDaw: thread a_w = i) 
      G_mid
      (GSTEPr: gstep (acts G) (sb G) (rmw G) (rf G) (mo G) (sc G)
           (acts G_mid) (sb G_mid) (rmw G_mid) (rf G_mid) (mo G_mid) (sc G_mid) a_r a_r)
      (GSTEPw: gstep (acts G_mid) (sb G_mid) (rmw G_mid) (rf G_mid) (mo G_mid) (sc G_mid)
                     (acts G') (sb G') (rmw G') (rf G') (mo G') (sc G') a_r a_w)
      (COH': Coherent (acts G_mid) (sb G_mid) (rmw G_mid) (rf G_mid) (mo G_mid) (sc G_mid))
      (COH': Coherent (acts G') (sb G') (rmw G') (rf G') (mo G') (sc G'))
  | fence a o_r o_w (EVENT: e = Some (ProgramEvent.fence o_r o_w)) 
      (LABa: lab a = Afence o_r o_w) 
      (TIDa: thread a = i) 
      (GSTEP: gstep (acts G) (sb G) (rmw G) (rf G) (mo G) (sc G)
                    (acts G') (sb G') (rmw G') (rf G') (mo G') (sc G') a a)
      (COH': Coherent (acts G') (sb G') (rmw G') (rf G') (mo G') (sc G'))
  | syscall a ee (EVENT: e = Some (ProgramEvent.syscall ee)) 
      (LABa: lab a = Afence Ordering.seqcst Ordering.seqcst) 
      (TIDa: thread a = i) 
      (GSTEP: gstep (acts G) (sb G) (rmw G) (rf G) (mo G) (sc G)
                    (acts G') (sb G') (rmw G') (rf G') (mo G') (sc G') a a)
      (COH': Coherent (acts G') (sb G') (rmw G') (rf G') (mo G') (sc G')).

Inductive step mc mc' : Prop :=
| step_intro  
    lang st st' i e
    (TID: IdentMap.find i (ts mc) = Some (existT _ lang st))
    (STATE: lang.(Language.step) e st st')
    (MTS: ts mc' = IdentMap.add i (existT _ lang st') (ts mc))
    (MSTEP: mstep (exec mc) (exec mc') e (Some i)).

End Operational.

