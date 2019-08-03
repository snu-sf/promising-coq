Require Import RelationClasses.
Require Import List.

Require Import sflib.

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
  | skip
  | assign (lhs:Reg.t) (rhs:expr)
  | load (lhs:Reg.t) (rhs:Loc.t) (ord:Ordering.t)
  | store (lhs:Loc.t) (rhs:Value.t) (ord:Ordering.t)
  | update (lhs:Reg.t) (loc:Loc.t) (rmw:rmw) (ordr ordw:Ordering.t)
  | fence (ordr ordw:Ordering.t)
  | syscall (lhs:Reg.t) (rhses:list Value.t)
  .

  Definition regs_of_rmw (rmw:rmw): RegSet.t :=
    match rmw with
    | fetch_add addendum => (Value.regs_of addendum)
    | cas old new => RegSet.union (Value.regs_of old) (Value.regs_of new)
    end.

  Definition regs_of (i:t): RegSet.t :=
    match i with
    | skip => RegSet.empty
    | assign reg rhs => RegSet.add reg (regs_of_expr rhs)
    | load reg _ _ => RegSet.singleton reg
    | store _ val _ => Value.regs_of val
    | update reg _ rmw _ _ => RegSet.add reg (regs_of_rmw rmw)
    | fence _ _ => RegSet.empty
    | syscall lhs rhses => RegSet.add lhs (Value.regs_of_list rhses)
    end.

  Inductive ord: forall (i_src i_tgt:Instr.t), Prop :=
  | ord_skip:
      ord Instr.skip Instr.skip
  | ord_assign
      r e:
      ord (Instr.assign r e) (Instr.assign r e)
  | ord_load
      r l o1 o2 (O: Ordering.le o1 o2):
      ord (Instr.load r l o1) (Instr.load r l o2)
  | ord_store
      l v o1 o2 (O: Ordering.le o1 o2):
      ord (Instr.store l v o1) (Instr.store l v o2)
  | ord_update
      r l rmw or1 or2 ow1 ow2
      (OR: Ordering.le or1 or2)
      (OW: Ordering.le ow1 ow2):
      ord (Instr.update r l rmw or1 ow1) (Instr.update r l rmw or2 ow2)
  | ord_fence
      or1 or2 ow1 ow2
      (OR: Ordering.le or1 or2)
      (OW: Ordering.le ow1 ow2):
      ord (Instr.fence or1 ow1) (Instr.fence or2 ow2)
  | ord_syscall
      o i:
      ord (Instr.syscall o i) (Instr.syscall o i)
  .

  Global Program Instance instr_ord_Reflexive: Reflexive ord.
  Next Obligation. destruct x; econs; refl. Qed.

  Lemma ord_regs_of
        instr_src instr_tgt
        (ORD: ord instr_src instr_tgt):
    Instr.regs_of instr_src = Instr.regs_of instr_tgt.
  Proof. inv ORD; auto. Qed.
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

  Notation "'pln'" := (Ordering.plain) (at level 41).
  Notation "'rlx'" := (Ordering.relaxed) (at level 41).
  Notation "'ar'" := (Ordering.acqrel) (at level 41).
  Notation "'sc'" := (Ordering.seqcst) (at level 41).

  Notation "'NOT' e" := (Instr.expr_op1 Op1.not e) (at level 41).
  Notation "e1 'ADD' e2" := (Instr.expr_op2 Op2.add e1 e2) (at level 41).
  Notation "e1 'SUB' e2" := (Instr.expr_op2 Op2.sub e2 e2) (at level 41).
  Notation "e1 'MUL' e2" := (Instr.expr_op2 Op2.mul e2 e2) (at level 41).

  Notation "'SKIP'" := (Instr.skip) (at level 42).
  Notation "'LET' lhs '::=' rhs" := (Instr.assign lhs rhs) (at level 42).
  Notation "'LOAD' lhs '::=' rhs '@' ord" := (Instr.load lhs rhs ord) (at level 42).
  Notation "'STORE' lhs '::=' rhs '@' ord" := (Instr.store lhs rhs ord) (at level 42).
  Notation "'FETCH_ADD' lhs '::=' loc ',' addendum '@' ordr ',' ordw" := (Instr.update lhs loc (Instr.fetch_add addendum) ordr ordw) (at level 42).
  Notation "'CAS' lhs '::=' loc ',' old ',' new '@' ordr ',' ordw" := (Instr.update lhs loc (Instr.cas old new) ordr ordw) (at level 42).
  Notation "'FENCE' '@' ordr ',' ordw" := (Instr.fence ordr ordw) (at level 42).
  Notation "'SYSCALL' lhs '::=' rhses" := (Instr.syscall lhs rhses) (at level 42).

  Notation "'IF' cond 'THEN' c1 'ELSE' c2" := (Stmt.ite cond c1 c2) (at level 43).
  Notation "'DO' c 'WHILE' cond" := (Stmt.dowhile c cond) (at level 43).

  (* Program Definition example1: list Stmt.t := [ *)
  (*   DO [ *)
  (*     SKIP; *)
  (*     LOAD %r"r1" ::= %l"flag" @ ar; *)
  (*     LET %r"r2" ::= NOT %r"r1" *)
  (*   ] WHILE (%r"r2" ADD 0); *)
  (*   LOAD %r"r3" ::= %l"x" @ rlx *)
  (* ]. *)

  (* Program Definition example2: list Stmt.t := [ *)
  (*   DO [ *)
  (*     SKIP; *)
  (*     LOAD %r"r1" ::= %l"flag" @ rlx; *)
  (*     LET %r"r2" ::= NOT %r"r1" *)
  (*   ] WHILE (%r"r2" MUL 1); *)
  (*   FENCE @ ar, rlx; *)
  (*   LOAD %r"r3" ::= %l"x" @ rlx; *)
  (*   SYSCALL %r"r4" ::= [%r"r3"; 3; 4] *)
  (* ]. *)

  (* Program Definition example3: list Stmt.t := [ *)
  (*   FETCH_ADD %r"r1" ::= %l"x", 1 @ rlx, rlx; *)
  (*   CAS %r"r1" ::= %l"x", 1, 2 @ rlx, rlx *)
  (* ]. *)
End SyntaxNotations.
