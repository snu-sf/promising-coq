Require Import Event.
Require Import Syntax.

Set Implicit Arguments.

Module RegSet.
  Definition t := Reg.Map.t Const.t.

  Definition find (r:Reg.t) (rs:t): Const.t :=
    match Reg.Map.find r rs with
    | Some v => v
    | None => Const.zero
    end.

  Definition add := Reg.Map.add.

  Definition eval_value (rs:t) (val:Value.t): Const.t :=
    match val with
    | Value.reg r => find r rs
    | Value.const c => c
    end.

  Definition eval_rhs (rs:t) (rhs:Instr.rhs): Const.t :=
    match rhs with
    | Instr.rhs_val val => eval_value rs val
    | Instr.rhs_op1 op op1 => Op1.eval op (eval_value rs op1)
    | Instr.rhs_op2 op op1 op2 => Op2.eval op (eval_value rs op1) (eval_value rs op2)
    end.
End RegSet.

Inductive eval_instr: forall (rs1:RegSet.t) (i:Instr.t) (e:option Event.t) (rs2:RegSet.t), Prop :=
| eval_load
    rs lhs rhs ord val:
    eval_instr
      rs
      (Instr.load lhs rhs ord)
      (Some (Event.read rhs val ord))
      (RegSet.add lhs val rs)
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
      (RegSet.add lhs val rs)
.

Module Thread.
  Structure t: Type := mk {
    regs: Reg.Map.t Const.t;
    stmts: list Stmt.t
  }.

  Definition is_terminal (c:t): bool :=
    match stmts c with
    | nil => true
    | _ => false
    end.

  Inductive step: forall (c1:t) (e:option Event.t) (c2:t), Prop :=
  | step_instr
      rs1 i e rs2 c
      (INSTR: eval_instr rs1 i e rs2):
      step
        (mk rs1 ((Stmt.instr i)::c))
        e
        (mk rs2 c)
  | step_ite
      rs cond s1 s2 c:
      step
        (mk rs ((Stmt.ite cond s1 s2)::c))
        None
        (mk rs ((if RegSet.eval_value rs cond
                 then s1
                 else s2) ++ c))
  | step_dowhile
      rs s cond c:
      step
        (mk rs ((Stmt.dowhile s cond)::c))
        None
        (mk rs (s ++ (Stmt.ite cond (cons (Stmt.dowhile s cond) nil) nil) :: c))
  .
End Thread.
