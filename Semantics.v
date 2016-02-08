Require Import Event.
Require Import Syntax.
Require Import Thread.

Set Implicit Arguments.

Module RegSet.
  Definition t := Reg.Fun.t Const.t.

  Definition empty := Reg.Fun.empty Const.zero.

  Definition eval_value (rs:t) (val:Value.t): Const.t :=
    match val with
    | Value.reg r => Reg.Fun.find r rs
    | Value.const c => c
    end.

  Definition eval_rhs (rs:t) (rhs:Instr.rhs): Const.t :=
    match rhs with
    | Instr.rhs_val val => eval_value rs val
    | Instr.rhs_op1 op op1 => Op1.eval op (eval_value rs op1)
    | Instr.rhs_op2 op op1 op2 => Op2.eval op (eval_value rs op1) (eval_value rs op2)
    end.
End RegSet.

Module Semantics.
  Structure state: Type := mk {
    regs: RegSet.t;
    stmts: list Stmt.t;
  }.

  Definition is_terminal (s:state): Prop :=
    stmts s = nil.

  Inductive eval_instr: forall (rs1:RegSet.t) (i:Instr.t) (e:option Event.t) (rs2:RegSet.t), Prop :=
  | eval_load
      rs lhs rhs ord val:
      eval_instr
        rs
        (Instr.load lhs rhs ord)
        (Some (Event.read rhs val ord))
        (Reg.Fun.add lhs val rs)
  | eval_store
      rs lhs rhs ord:
      eval_instr
        rs
        (Instr.store lhs rhs ord)
        (Some (Event.write lhs (RegSet.eval_value rs rhs) ord))
        rs
  | eval_fetch_add
      rs lhs loc addendum ord val:
      eval_instr
        rs
        (Instr.fetch_add lhs loc addendum ord)
        (Some (Event.update loc val (Const.add val (RegSet.eval_value rs addendum)) ord))
        (Reg.Fun.add lhs val rs)
  | eval_assign
      rs lhs rhs:
      eval_instr
        rs
        (Instr.assign lhs rhs)
        None
        (Reg.Fun.add lhs (RegSet.eval_rhs rs rhs) rs)
  .

  Inductive step: forall (s1:state) (e:option Event.t) (s1:state), Prop :=
  | step_instr
      rs1 i e rs2 stmts
      (INSTR: eval_instr rs1 i e rs2):
      step
        (mk rs1 ((Stmt.instr i)::stmts))
        e
        (mk rs2 stmts)
  | step_ite
      rs cond s1 s2 stmts:
      step
        (mk rs ((Stmt.ite cond s1 s2)::stmts))
        None
        (mk rs ((if RegSet.eval_value rs cond
                 then s1
                 else s2) ++ stmts))
  | step_dowhile
      rs s cond stmts:
      step
        (mk rs ((Stmt.dowhile s cond)::stmts))
        None
        (mk rs (s ++ (Stmt.ite cond (cons (Stmt.dowhile s cond) nil) nil) :: stmts))
  .

  Definition lang :=
    Language.mk
      is_terminal
      step.
End Semantics.
