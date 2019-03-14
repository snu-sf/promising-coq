Require Import RelationClasses.

Require Import Basic.
Require Import Axioms.
Require Import List.
Require Import Event.
Require Import Syntax.
Require Import Language.

Require Import sflib.
From Paco Require Import paco.

Set Implicit Arguments.

Module RegFile.
  Definition t := RegFun.t Const.t.

  Definition init := RegFun.init Const.zero.

  Definition eval_value (rf:t) (val:Value.t): Const.t :=
    match val with
    | Value.reg r => RegFun.find r rf
    | Value.const c => c
    end.

  Definition eval_expr (rf:t) (rhs:Instr.expr): Const.t :=
    match rhs with
    | Instr.expr_val val => eval_value rf val
    | Instr.expr_op1 op op1 => Op1.eval op (eval_value rf op1)
    | Instr.expr_op2 op op1 op2 => Op2.eval op (eval_value rf op1) (eval_value rf op2)
    end.

  Definition eval_rmw (rf:t) (rmw:Instr.rmw) (val:Const.t): Const.t * option Const.t :=
    match rmw with
    | Instr.fetch_add addendum =>
      (Const.add val (eval_value rf addendum), Some (Const.add val (eval_value rf addendum)))
    | Instr.cas o n =>
      if Const.eq_dec (eval_value rf o) val
      then (1, Some (eval_value rf n))
      else (0, None)
    end.

  Inductive eval_instr: forall (rf1:t) (i:Instr.t) (e:ProgramEvent.t) (rf2:t), Prop :=
  | eval_skip
      rf:
      eval_instr
        rf
        Instr.skip
        ProgramEvent.silent
        rf
  | eval_assign
      rf lhs rhs:
      eval_instr
        rf
        (Instr.assign lhs rhs)
        ProgramEvent.silent
        (RegFun.add lhs (eval_expr rf rhs) rf)
  | eval_load
      rf lhs rhs ord val:
      eval_instr
        rf
        (Instr.load lhs rhs ord)
        (ProgramEvent.read rhs val ord)
        (RegFun.add lhs val rf)
  | eval_store
      rf lhs rhs ord:
      eval_instr
        rf
        (Instr.store lhs rhs ord)
        (ProgramEvent.write lhs (eval_value rf rhs) ord)
        rf
  | eval_update_success
      rf lhs loc rmw ordr ordw valr valret valw
      (RMW: eval_rmw rf rmw valr = (valret, Some valw)):
      eval_instr
        rf
        (Instr.update lhs loc rmw ordr ordw)
        (ProgramEvent.update loc valr valw ordr ordw)
        (RegFun.add lhs valret rf)
  | eval_update_fail
      rf lhs loc rmw ordr ordw valr valret
      (RMW: eval_rmw rf rmw valr = (valret, None)):
      eval_instr
        rf
        (Instr.update lhs loc rmw ordr ordw)
        (ProgramEvent.read loc valr ordr)
        (RegFun.add lhs valret rf)
  | eval_fence
      rf ordr ordw:
      eval_instr
        rf
        (Instr.fence ordr ordw)
        (ProgramEvent.fence ordr ordw)
        rf
  | eval_syscall
      rf lhs rhses lhs_val:
      eval_instr
        rf
        (Instr.syscall lhs rhses)
        (ProgramEvent.syscall (Event.mk lhs_val (map (eval_value rf) rhses)))
        (RegFun.add lhs lhs_val rf)
  .

  Definition eq_except (regs:RegSet.t) (rs_src rs_tgt:RegFile.t): Prop :=
    forall reg (REG: ~ RegSet.In reg regs), rs_src reg = rs_tgt reg.

  Global Program Instance eq_except_Equivalence regs: Equivalence (eq_except regs).
  Next Obligation.
    ii. auto.
  Qed.
  Next Obligation.
    ii. rewrite H; auto.
  Qed.
  Next Obligation.
    ii. rewrite H; auto.
  Qed.

  Lemma eq_except_nil rs_src rs_tgt:
    rs_src = rs_tgt <-> eq_except RegSet.empty rs_src rs_tgt.
  Proof.
    econs; i; subst; auto.
    - econs.
    - apply RegFun.ext. i. apply H.
      ii. eapply RegSet.Facts.empty_iff; eauto.
  Qed.

  Lemma eq_except_mon regs1 regs2
        (SUB: RegSet.Subset regs1 regs2):
    eq_except regs1 <2= eq_except regs2.
  Proof.
    ii. specialize (PR reg). apply PR. contradict REG.
    apply SUB. auto.
  Qed.

  Lemma eq_except_singleton r v rs:
    eq_except (RegSet.singleton r) (RegFun.add r v rs) rs.
  Proof.
    ii. unfold RegFun.add, RegFun.find. condtac; auto. subst.
    contradict REG. apply RegSet.Facts.singleton_iff. auto.
  Qed.

  Lemma eq_except_add
        regs rs_src rs_tgt lhs val
        (EQ: eq_except regs rs_src rs_tgt):
    eq_except regs (RegFun.add lhs val rs_src) (RegFun.add lhs val rs_tgt).
  Proof.
    ii. unfold RegFun.add. condtac; ss.
    apply EQ. ss.
  Qed.

  Lemma eq_except_value
        rs_src rs_tgt regs v
        (REGS: RegSet.disjoint regs (Value.regs_of v))
        (RS: eq_except regs rs_src rs_tgt):
    RegFile.eval_value rs_src v = RegFile.eval_value rs_tgt v.
  Proof.
    destruct v; auto. ss. apply RS. ii.
    eapply REGS; eauto.
    apply RegSet.Facts.singleton_iff. auto.
  Qed.

  Lemma eq_except_value_list
        rs_src rs_tgt regs vl
        (REGS: RegSet.disjoint regs (Value.regs_of_list vl))
        (RS: eq_except regs rs_src rs_tgt):
    map (RegFile.eval_value rs_src) vl = map (RegFile.eval_value rs_tgt) vl.
  Proof.
    revert REGS. induction vl; ss. i. f_equal.
    - eapply eq_except_value; eauto.
      ii. eapply REGS; eauto.
      destruct a; ss.
      + apply RegSet.singleton_spec in RHS. subst.
        apply RegSet.add_spec. auto.
      + inv RHS.
    - apply IHvl.
      ii. eapply REGS; eauto.
      destruct a; ss.
      apply RegSet.add_spec. auto.
  Qed.

  Lemma eq_except_expr
        rs_src rs_tgt regs e
        (REGS: RegSet.disjoint regs (Instr.regs_of_expr e))
        (RS: eq_except regs rs_src rs_tgt):
    RegFile.eval_expr rs_src e = RegFile.eval_expr rs_tgt e.
  Proof.
    destruct e; ss.
    - erewrite eq_except_value; eauto.
    - erewrite eq_except_value; eauto.
    - erewrite (eq_except_value op1); eauto.
      + erewrite (eq_except_value op2); eauto.
        ii. eapply REGS; eauto.
        apply RegSet.union_spec. auto.
      + ii. eapply REGS; eauto.
        apply RegSet.union_spec. auto.
  Qed.

  Lemma eq_except_rmw
        rs_src rs_tgt regs rmw val
        (REGS: RegSet.disjoint regs (Instr.regs_of_rmw rmw))
        (RS: eq_except regs rs_src rs_tgt):
    RegFile.eval_rmw rs_src rmw val = RegFile.eval_rmw rs_tgt rmw val.
  Proof.
    destruct rmw; ss.
    - erewrite ? (@eq_except_value rs_src rs_tgt); eauto.
    - erewrite ? (@eq_except_value rs_src rs_tgt); eauto.
      + ii. eapply REGS; eauto.
        apply RegSet.union_spec. auto.
      + ii. eapply REGS; eauto.
        apply RegSet.union_spec. auto.
  Qed.

  Lemma eq_except_instr
        rs1_src rs1_tgt rs2_tgt regs instr e
        (TGT: RegFile.eval_instr rs1_tgt instr e rs2_tgt)
        (REGS: RegSet.disjoint regs (Instr.regs_of instr))
        (RS: eq_except regs rs1_src rs1_tgt):
    exists rs2_src,
      <<SRC: RegFile.eval_instr rs1_src instr e rs2_src>> /\
      <<RS: eq_except regs rs2_src rs2_tgt>>.
  Proof.
    inv TGT; ss.
    - eexists. splits; eauto. econs.
    - eexists. splits; [econs|].
      ii. generalize (RS reg). i.
      unfold RegFun.add, RegFun.find. condtac; auto. subst.
      eapply eq_except_expr; eauto.
      ii. eapply REGS; eauto.
      apply RegSet.add_spec. auto.
    - eexists. splits; [econs|].
      ii. specialize (RS reg).
      unfold RegFun.add, RegFun.find. condtac; auto.
    - erewrite <- eq_except_value; eauto.
      eexists. splits; [econs|].
      ii. eauto.
    - erewrite <- eq_except_rmw in RMW; eauto.
      + eexists. splits.
        * econs. eauto.
        * ii. unfold RegFun.add. condtac; auto.
          eapply RS; eauto.
      + ii. eapply REGS; eauto.
        apply RegSet.add_spec. auto.
    - erewrite <- eq_except_rmw in RMW; eauto.
      + eexists. splits.
        * econs. eauto.
        * ii. unfold RegFun.add. condtac; auto.
          eapply RS; eauto.
      + ii. eapply REGS; eauto.
        apply RegSet.add_spec. auto.
    - eexists. splits; [econs|]. auto.
    - erewrite <- eq_except_value_list; eauto.
      + eexists. splits; [econs|].
        ii. specialize (RS reg).
        unfold RegFun.add, RegFun.find. condtac; auto.
      + ii. eapply REGS; eauto.
        apply RegSet.add_spec. auto.
  Qed.

  Lemma instr_ord_eval_instr
        rf1 instr_src instr_tgt e_tgt rf2
        (ORD: Instr.ord instr_src instr_tgt)
        (EVAL: RegFile.eval_instr rf1 instr_tgt e_tgt rf2):
    exists e_src,
      <<EVAL: RegFile.eval_instr rf1 instr_src e_src rf2>> /\
      <<ORD: ProgramEvent.ord e_src e_tgt>>.
  Proof.
    inv ORD; inv EVAL; esplits; try by repeat (econs; eauto).
  Qed.
End RegFile.

Module State.
  Structure t := mk {
    regs: RegFile.t;
    stmts: list Stmt.t;
  }.

  Definition init (text:list Stmt.t): t :=
    mk RegFile.init text.

  Definition is_terminal (s:t): Prop :=
    stmts s = nil.

  Inductive step: forall (e:ProgramEvent.t) (s1:t) (s1:t), Prop :=
  | step_instr
      rf1 i e rf2 stmts
      (INSTR: RegFile.eval_instr rf1 i e rf2):
      step e
           (mk rf1 ((Stmt.instr i)::stmts))
           (mk rf2 stmts)
  | step_ite
      rf cond s1 s2 stmts:
      step ProgramEvent.silent
           (mk rf ((Stmt.ite cond s1 s2)::stmts))
           (mk rf ((if RegFile.eval_expr rf cond
                    then s1
                    else s2) ++ stmts))
  | step_dowhile
      rf s cond stmts:
      step ProgramEvent.silent
           (mk rf ((Stmt.dowhile s cond)::stmts))
           (mk rf (s ++ (Stmt.ite cond ((Stmt.dowhile s cond)::nil) nil) :: stmts))
  .
End State.

Program Definition lang :=
  Language.mk
    State.init
    State.is_terminal
    State.step.
