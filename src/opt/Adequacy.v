Require Import sflib.
Require Import paco.

Require Import Basic.
Require Import Event.
Require Import Language.
Require Import Memory.
Require Import Commit.
Require Import Thread.
Require Import Configuration.
Require Import Simulation.
Require Import Behavior.

Lemma sim_adequacy
      ths_src mem_src
      ths_tgt mem_tgt
      (SRC: Configuration.consistent (Configuration.mk ths_src mem_src))
      (TGT: Configuration.consistent (Configuration.mk ths_tgt mem_tgt))
      (MEMORY: sim_memory mem_src mem_tgt)
      (SIM: sim ths_src mem_src ths_tgt mem_tgt):
  behaviors (Configuration.mk ths_src mem_src) <1=
  behaviors (Configuration.mk ths_tgt mem_tgt).
Proof.
Admitted.
