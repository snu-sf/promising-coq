Require Import sflib.
Require Import paco.

Require Import Basic.
Require Import Event.
Require Import Language.
Require Import Memory.
Require Import Commit.
Require Import Thread.
Require Import Configuration.
Require Import MemInv.
Require Import Simulation.
Require Import Behavior.

Lemma sim_adequacy
      ths_src sc_src mem_src
      ths_tgt sc_tgt mem_tgt
      (SRC: Configuration.consistent (Configuration.mk ths_src sc_src mem_src))
      (TGT: Configuration.consistent (Configuration.mk ths_tgt sc_tgt mem_tgt))
      (MEMORY: Memory.sim mem_tgt mem_src)
      (SIM: sim ths_src sc_src mem_src ths_tgt sc_tgt mem_tgt):
  behaviors (Configuration.mk ths_src sc_src mem_src) <1=
  behaviors (Configuration.mk ths_tgt sc_tgt mem_tgt).
Proof.
Admitted.
