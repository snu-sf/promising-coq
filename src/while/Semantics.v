Require Import List.
Require Import Event.
Require Import Syntax.
Require Import Program.

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

  Inductive eval_instr: forall (rf1:t) (i:Instr.t) (e:option ThreadEvent.t) (rf2:t), Prop :=
  | eval_load
      rf lhs rhs ord val:
      eval_instr
        rf
        (Instr.load lhs rhs ord)
        (Some (ThreadEvent.mem (ThreadEvent.rw (RWEvent.read rhs val ord))))
        (RegFun.add lhs val rf)
  | eval_store
      rf lhs rhs ord:
      eval_instr
        rf
        (Instr.store lhs rhs ord)
        (Some (ThreadEvent.mem (ThreadEvent.rw (RWEvent.write lhs (eval_value rf rhs) ord))))
        rf
  | eval_fetch_add
      rf lhs loc addendum ord val:
      eval_instr
        rf
        (Instr.fetch_add lhs loc addendum ord)
        (Some (ThreadEvent.mem (ThreadEvent.rw (RWEvent.update loc val (Const.add val (eval_value rf addendum)) ord))))
        (RegFun.add lhs val rf)
  | eval_assign
      rf lhs rhs:
      eval_instr
        rf
        (Instr.assign lhs rhs)
        None
        (RegFun.add lhs (eval_expr rf rhs) rf)
  | eval_fence
      rf ord:
      eval_instr
        rf
        (Instr.fence ord)
        (Some (ThreadEvent.mem (ThreadEvent.fence ord)))
        rf
  | eval_syscall
      rf lhs rhses lhs_val:
      eval_instr
        rf
        (Instr.syscall lhs rhses)
        (Some (ThreadEvent.syscall (Event.mk lhs_val (map (eval_value rf) rhses))))
        (RegFun.add lhs lhs_val rf)
  .
End RegFile.

Module State.
  Structure t: Type := mk {
    regs: RegFile.t;
    stmts: list Stmt.t;
  }.

  Definition load (text:list Stmt.t): t :=
    mk RegFile.init text.

  Definition is_terminal (s:t): Prop :=
    stmts s = nil.

  Inductive step: forall (s1:t) (e:option ThreadEvent.t) (s1:t), Prop :=
  | step_instr
      rf1 i e rf2 stmts
      (INSTR: RegFile.eval_instr rf1 i e rf2):
      step
        (mk rf1 ((Stmt.instr i)::stmts))
        e
        (mk rf2 stmts)
  | step_ite
      rf cond s1 s2 stmts:
      step
        (mk rf ((Stmt.ite cond s1 s2)::stmts))
        None
        (mk rf ((if RegFile.eval_expr rf cond
                 then s1
                 else s2) ++ stmts))
  | step_dowhile
      rf s cond stmts:
      step
        (mk rf ((Stmt.dowhile s cond)::stmts))
        None
        (mk rf (s ++ (Stmt.ite cond ((Stmt.dowhile s cond)::nil) nil) :: stmts))
  .
End State.

Definition lang :=
  Language.mk
    State.load
    State.is_terminal
    State.step.
