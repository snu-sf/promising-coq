Require Import List.
Require Import Event.
Require Import Syntax.
Require Import Thread.

Set Implicit Arguments.

Module RegSet.
  Definition t := Reg.Fun.t Const.t.

  Definition empty := Reg.Fun.init Const.zero.

  Definition eval_value (rs:t) (val:Value.t): Const.t :=
    match val with
    | Value.reg r => Reg.Fun.find r rs
    | Value.const c => c
    end.

  Definition eval_expr (rs:t) (rhs:Instr.expr): Const.t :=
    match rhs with
    | Instr.expr_val val => eval_value rs val
    | Instr.expr_op1 op op1 => Op1.eval op (eval_value rs op1)
    | Instr.expr_op2 op op1 op2 => Op2.eval op (eval_value rs op1) (eval_value rs op2)
    end.

  Inductive eval_instr: forall (rs1:t) (i:Instr.t) (e:option ThreadEvent.t) (rs2:t), Prop :=
  | eval_load
      rs lhs rhs ord val:
      eval_instr
        rs
        (Instr.load lhs rhs ord)
        (Some (ThreadEvent.rw (RWEvent.read rhs val ord)))
        (Reg.Fun.add lhs val rs)
  | eval_store
      rs lhs rhs ord:
      eval_instr
        rs
        (Instr.store lhs rhs ord)
        (Some (ThreadEvent.rw (RWEvent.write lhs (eval_value rs rhs) ord)))
        rs
  | eval_fetch_add
      rs lhs loc addendum ord val:
      eval_instr
        rs
        (Instr.fetch_add lhs loc addendum ord)
        (Some (ThreadEvent.rw (RWEvent.update loc val (Const.add val (eval_value rs addendum)) ord)))
        (Reg.Fun.add lhs val rs)
  | eval_assign
      rs lhs rhs:
      eval_instr
        rs
        (Instr.assign lhs rhs)
        None
        (Reg.Fun.add lhs (eval_expr rs rhs) rs)
  | eval_fence
      rs ord:
      eval_instr
        rs
        (Instr.fence ord)
        (Some (ThreadEvent.fence ord))
        rs
  | eval_syscall
      rs lhs rhses lhs_val:
      eval_instr
        rs
        (Instr.syscall lhs rhses)
        (Some (ThreadEvent.syscall (Event.mk lhs_val (map (eval_value rs) rhses))))
        (Reg.Fun.add lhs lhs_val rs)
  .
End RegSet.

Module State.
  Structure t: Type := mk {
    regs: RegSet.t;
    stmts: list Stmt.t;
  }.

  Definition is_terminal (s:t): Prop :=
    stmts s = nil.

  Inductive step: forall (s1:t) (e:option ThreadEvent.t) (s1:t), Prop :=
  | step_instr
      rs1 i e rs2 stmts
      (INSTR: RegSet.eval_instr rs1 i e rs2):
      step
        (mk rs1 ((Stmt.instr i)::stmts))
        e
        (mk rs2 stmts)
  | step_ite
      rs cond s1 s2 stmts:
      step
        (mk rs ((Stmt.ite cond s1 s2)::stmts))
        None
        (mk rs ((if RegSet.eval_expr rs cond
                 then s1
                 else s2) ++ stmts))
  | step_dowhile
      rs s cond stmts:
      step
        (mk rs ((Stmt.dowhile s cond)::stmts))
        None
        (mk rs (s ++ (Stmt.ite cond ((Stmt.dowhile s cond)::nil) nil) :: stmts))
  .
End State.

Definition lang :=
  Language.mk
    State.is_terminal
    State.step.
