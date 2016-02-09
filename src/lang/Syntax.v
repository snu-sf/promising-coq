Require Import List.

Require Import Basic.
Require Import Event.

Module Reg.
  Include Ident.
End Reg.

Module Value.
  Inductive t :=
  | reg (reg:Reg.t)
  | const (const:Const.t)
  .

  Definition regs_of (v:t): Reg.Set_.t :=
    match v with
    | reg r => Reg.Set_.singleton r
    | const _ => Reg.Set_.empty
    end.

  Fixpoint regs_of_list (l:list t): Reg.Set_.t :=
    match l with
    | nil => Reg.Set_.empty
    | (reg r)::l => Reg.Set_.add r (regs_of_list l)
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
  Inductive rhs :=
  | rhs_val (val:Value.t)
  | rhs_op1 (op:Op1.t) (op:Value.t)
  | rhs_op2 (op:Op2.t) (op1 op2:Value.t)
  .

  Definition regs_of_rhs (r:rhs): Reg.Set_.t :=
    match r with
    | rhs_val val => Value.regs_of val
    | rhs_op1 _ op => Value.regs_of op
    | rhs_op2 _ op1 op2 => Reg.Set_.union (Value.regs_of op1) (Value.regs_of op2)
    end.

  Inductive t :=
  | load (lhs:Reg.t) (rhs:Loc.t) (ord:Ordering.t)
  | store (lhs:Loc.t) (rhs:Value.t) (ord:Ordering.t)
  | fetch_add (lhs:Reg.t) (loc:Loc.t) (addendum:Value.t) (ord:Ordering.t)
  | assign (lhs:Reg.t) (rhs:rhs)
  | fence (ord:Ordering.t)
  | syscall (lhs:Reg.t) (rhses:list Value.t)
  .

  Definition ordering_of (i:t): Ordering.t :=
    match i with
    | load _ _ ord => ord
    | store _ _ ord => ord
    | fetch_add _ _ _ ord => ord
    | assign _ _ => Ordering.relaxed
    | fence ord => ord
    | syscall _ _ => Ordering.relaxed
    end.

  Definition loc_of (i:t): option Loc.t :=
    match i with
    | load _ loc _ => Some loc
    | store loc _ _ => Some loc
    | fetch_add _ loc _ _ => Some loc
    | assign _ _ => None
    | fence _ => None
    | syscall _ _ => None
    end.

  Definition regs_of (i:t): Reg.Set_.t :=
    match i with
    | load reg _ _ => Reg.Set_.singleton reg
    | store _ val _ => Value.regs_of val
    | fetch_add reg _ val _ => Reg.Set_.add reg (Value.regs_of val)
    | assign reg rhs => Reg.Set_.add reg (regs_of_rhs rhs)
    | fence _ => Reg.Set_.empty
    | syscall lhs rhses => Reg.Set_.add lhs (Value.regs_of_list rhses)
    end.
End Instr.
Coercion Instr.rhs_val: Value.t >-> Instr.rhs.

Module Stmt.
  Inductive t :=
  | instr (i:Instr.t)
  | ite (cond:Value.t) (c1 c2:list t)
  | dowhile (c:list t) (cond:Value.t)
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

  Notation "'NOT' e" := (Instr.rhs_op1 Op1.not e) (at level 41).
  Notation "e1 'ADD' e2" := (Instr.rhs_op2 e1 Op2.add e2) (at level 41).
  Notation "e1 'SUB' e2" := (Instr.rhs_op2 e1 Op2.sub e2) (at level 41).
  Notation "e1 'MUL' e2" := (Instr.rhs_op2 e1 Op2.mul e2) (at level 41).

  Notation "'LOAD' lhs '<-' rhs '@' ord" := (Instr.load lhs rhs ord) (at level 42).
  Notation "'STORE' lhs '<-' rhs '@' ord" := (Instr.store lhs rhs ord) (at level 42).
  Notation "'FETCH_ADD' lhs '<-' loc ',' addendum '@' ord" := (Instr.fetch_add lhs loc addendum ord) (at level 42).
  Notation "lhs '::=' rhs" := (Instr.assign lhs rhs) (at level 42).
  Notation "'FENCE' '@' ord" := (Instr.fence ord) (at level 42).
  Notation "'SYSCALL' lhs '<-' rhses" := (Instr.syscall lhs rhses) (at level 42).

  Notation "'IF' cond 'THEN' c1 'ELSE' c2" := (Stmt.ite cond c1 c2) (at level 43).
  Notation "'DO' c 'WHILE' cond" := (Stmt.dowhile c cond) (at level 43).

  Program Definition example1: list Stmt.t := [
    DO [
      LOAD %r"r1" <- %l"flag" @ acq;
      %r"r2" ::= NOT %r"r1"
    ] WHILE %r"r2";
    LOAD %r"r3" <- %l"x" @ rlx
  ].

  Program Definition example2: list Stmt.t := [
    DO [
      LOAD %r"r1" <- %l"flag" @ rlx;
      %r"r2" ::= NOT %r"r1"
    ] WHILE %r"r2";
    FENCE @ acq;
    LOAD %r"r3" <- %l"x" @ rlx;
    SYSCALL %r"r4" <- [%r"r3"; 3; 4]
  ].
End SyntaxNotations.