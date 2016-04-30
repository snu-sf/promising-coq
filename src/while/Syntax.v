Require Import List.

Require Import Basic.
Require Import Event.

Set Implicit Arguments.

Module Reg := Ident.
Module RegSet := IdentSet.
Module RegMap := IdentMap.
Module RegFun := IdentFun.

Module Value.
  Inductive t :=
  | reg (reg:Reg.t)
  | const (const:Const.t)
  .

  Definition regs_of (v:t): RegSet.t :=
    match v with
    | reg r => RegSet.singleton r
    | const _ => RegSet.empty
    end.

  Fixpoint regs_of_list (l:list t): RegSet.t :=
    match l with
    | nil => RegSet.empty
    | (reg r)::l => RegSet.add r (regs_of_list l)
    | (const _)::l => regs_of_list l
    end.

  Definition of_nat (n:nat): t := const n.
End Value.
Coercion Value.reg: Reg.t >-> Value.t.
Coercion Value.const: Const.t >-> Value.t.
Coercion Value.of_nat: nat >-> Value.t.

Module Op1.
  Inductive t :=
  | not
  .

  Definition eval (op:t) (op1:Const.t): Const.t :=
    match op with
    | not =>
      if Const.eq_dec op1 Const.zero
      then Const.one
      else Const.zero
    end.
End Op1.

Module Op2.
  Inductive t :=
  | add
  | sub
  | mul
  .

  Definition eval (op:t): forall (op1 op2:Const.t), Const.t :=
    match op with
    | add => Const.add
    | sub => Const.sub
    | mul => Const.mul
    end.
End Op2.

Module Instr.
  Inductive expr :=
  | expr_val (val:Value.t)
  | expr_op1 (op:Op1.t) (op:Value.t)
  | expr_op2 (op:Op2.t) (op1 op2:Value.t)
  .

  Definition regs_of_expr (r:expr): RegSet.t :=
    match r with
    | expr_val val => Value.regs_of val
    | expr_op1 _ op => Value.regs_of op
    | expr_op2 _ op1 op2 => RegSet.union (Value.regs_of op1) (Value.regs_of op2)
    end.

  Inductive rmw :=
  | fetch_add (addendum:Value.t)
  | cas (old new:Value.t)
  .

  Inductive t :=
  | assign (lhs:Reg.t) (rhs:expr)
  | load (lhs:Reg.t) (rhs:Loc.t) (ord:Ordering.t)
  | store (lhs:Loc.t) (rhs:Value.t) (ord:Ordering.t)
  | update (lhs:Reg.t) (loc:Loc.t) (rmw:rmw) (ord:Ordering.t)
  | fence (ord:Ordering.t)
  | syscall (lhs:Reg.t) (rhses:list Value.t)
  .

  Definition skip := fence Ordering.relaxed.

  Definition ordering_of (i:t): Ordering.t :=
    match i with
    | assign _ _ => Ordering.relaxed
    | load _ _ ord => ord
    | store _ _ ord => ord
    | update _ _ _ ord => ord
    | fence ord => ord
    | syscall _ _ => Ordering.relaxed
    end.

  Definition loc_of (i:t): option Loc.t :=
    match i with
    | assign _ _ => None
    | load _ loc _ => Some loc
    | store loc _ _ => Some loc
    | update _ loc _ _ => Some loc
    | fence _ => None
    | syscall _ _ => None
    end.

  Definition regs_of_rmw (rmw:rmw): RegSet.t :=
    match rmw with
    | fetch_add addendum => (Value.regs_of addendum)
    | cas old new => RegSet.union (Value.regs_of old) (Value.regs_of new)
    end.

  Definition regs_of (i:t): RegSet.t :=
    match i with
    | assign reg rhs => RegSet.add reg (regs_of_expr rhs)
    | load reg _ _ => RegSet.singleton reg
    | store _ val _ => Value.regs_of val
    | update reg _ rmw _ => RegSet.add reg (regs_of_rmw rmw)
    | fence _ => RegSet.empty
    | syscall lhs rhses => RegSet.add lhs (Value.regs_of_list rhses)
    end.
End Instr.
Coercion Instr.expr_val: Value.t >-> Instr.expr.

Module Stmt.
  Inductive t :=
  | instr (i:Instr.t)
  | ite (cond:Instr.expr) (c1 c2:list t)
  | dowhile (c:list t) (cond:Instr.expr)
  .
End Stmt.
Coercion Stmt.instr: Instr.t >-> Stmt.t.

Module SyntaxNotations.
  Export ListNotations.

  Delimit Scope string_scope with string.
  Open Scope string_scope.

  Notation "'%r' var" := (Reg.of_string var) (at level 41).
  Notation "'%l' var" := (Loc.of_string var) (at level 41).

  Notation "'rlx'" := (Ordering.relaxed) (at level 41).
  Notation "'rel'" := (Ordering.release) (at level 41).
  Notation "'acq'" := (Ordering.acquire) (at level 41).
  Notation "'ra'" := (Ordering.relacq) (at level 41).

  Notation "'NOT' e" := (Instr.expr_op1 Op1.not e) (at level 41).
  Notation "e1 'ADD' e2" := (Instr.expr_op2 Op2.add e1 e2) (at level 41).
  Notation "e1 'SUB' e2" := (Instr.expr_op2 Op2.sub e2 e2) (at level 41).
  Notation "e1 'MUL' e2" := (Instr.expr_op2 Op2.mul e2 e2) (at level 41).

  Notation "'SKIP'" := (Instr.skip) (at level 42).
  Notation "'LET' lhs '::=' rhs" := (Instr.assign lhs rhs) (at level 42).
  Notation "'LOAD' lhs '::=' rhs '@' ord" := (Instr.load lhs rhs ord) (at level 42).
  Notation "'STORE' lhs '::=' rhs '@' ord" := (Instr.store lhs rhs ord) (at level 42).
  Notation "'FETCH_ADD' lhs '::=' loc ',' addendum '@' ord" := (Instr.update lhs loc (Instr.fetch_add addendum) ord) (at level 42).
  Notation "'CAS' lhs '::=' loc ',' old ',' new '@' ord" := (Instr.update lhs loc (Instr.cas old new) ord) (at level 42).
  Notation "'FENCE' '@' ord" := (Instr.fence ord) (at level 42).
  Notation "'SYSCALL' lhs '::=' rhses" := (Instr.syscall lhs rhses) (at level 42).

  Notation "'IF' cond 'THEN' c1 'ELSE' c2" := (Stmt.ite cond c1 c2) (at level 43).
  Notation "'DO' c 'WHILE' cond" := (Stmt.dowhile c cond) (at level 43).

  Program Definition example1: list Stmt.t := [
    DO [
      SKIP;
      LOAD %r"r1" ::= %l"flag" @ acq;
      LET %r"r2" ::= NOT %r"r1"
    ] WHILE (%r"r2" ADD 0);
    LOAD %r"r3" ::= %l"x" @ rlx
  ].

  Program Definition example2: list Stmt.t := [
    DO [
      SKIP;
      LOAD %r"r1" ::= %l"flag" @ rlx;
      LET %r"r2" ::= NOT %r"r1"
    ] WHILE (%r"r2" MUL 1);
    FENCE @ acq;
    LOAD %r"r3" ::= %l"x" @ rlx;
    SYSCALL %r"r4" ::= [%r"r3"; 3; 4]
  ].

  Program Definition example3: list Stmt.t := [
    FETCH_ADD %r"r1" ::= %l"x", 1 @ rlx;
    CAS %r"r1" ::= %l"x", 1, 2 @ rlx
  ].
End SyntaxNotations.
