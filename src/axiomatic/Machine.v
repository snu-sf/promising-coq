(******************************************************************************)
(** * Definitions of the axiomatic machine   *)
(******************************************************************************)

Require Import Classical List Relations Peano_dec.
Require Import Vbase ExtraRelations.

Require Import sflib.
Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import Language.
Require Import Event.
Require Import Time.
Require Import Configuration.
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

(*Definition Coherent_configuration (mc : configuration) := 
  Coherent (Macts mc) (Mlab mc) (Msb mc) (Mrmw mc) (Mrf mc) (Mmo mc) (Msc mc).*)

Inductive m_step (mc mc' : configuration) : Prop :=
  | Mstep_read lang  st st' a l v o
      (TID: IdentMap.find (thread a) (ts mc) = Some (existT _ lang st))
      (STATE: lang.(Language.step) (Some (ProgramEvent.read l v o)) st st')
      (MTS: ts mc' = IdentMap.add (thread a) (existT _ _ st') (ts mc))
      (LAB_STEP: lab a = (Aload l v o))
      (GSTEP: gstep (acts mc) (sb mc) (rmw mc) (rf mc) (mo mc) (sc mc)
                         (acts mc') (sb mc') (rmw mc') (rf mc') (mo mc') (sc mc') a).
(* TODO: add more steps *)


End Operational.

