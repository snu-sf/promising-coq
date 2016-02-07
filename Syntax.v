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
End Value.

Module Loc.
  Definition t := nat.
End Loc.

Module Op2.
  Inductive t :=
  | add
  | sub
  | mul
  .
End Op2.

Module Instr.
  Inductive t: Type :=
  | load (lhs:Reg.t) (rhs:Loc.t) (ord:Ordering.t)
  | store (lhs:Loc.t) (rhs:Value.t) (ord:Ordering.t)
  | fetch_add (lhs:Reg.t) (loc:Loc.t) (addendum:Value.t) (ord:Ordering.t)
  | op2 (lhs:Reg.t) (op:Op2.t) (op1 op2:Value.t)
  .

  Definition ordering_of (i:t): Ordering.t :=
    match i with
    | load _ _ ord => ord
    | store _ _ ord => ord
    | fetch_add _ _ _ ord => ord
    | op2 _ _ _ _ => Ordering.relaxed
    end.

  Definition loc_of (i:t): option Loc.t :=
    match i with
    | load _ loc _ => Some loc
    | store loc _ _ => Some loc
    | fetch_add _ loc _ _ => Some loc
    | op2 _ _ _ _ => None
    end.

  Definition regs_of (i:t): Reg.Set_.t :=
    match i with
    | load reg _ _ => Reg.Set_.singleton reg
    | store _ val _ => Value.regs_of val
    | fetch_add reg _ val _ => Reg.Set_.add reg (Value.regs_of val)
    | op2 reg _ val1 val2 =>
      Reg.Set_.add reg (Reg.Set_.union (Value.regs_of val1) (Value.regs_of val2))
    end.
End Instr.

Module Core.
  Inductive t: Type :=
  | instrs (is:list Instr.t)
  | seq (c1 c2:t)
  | ite (cond:Value.t) (c1 c2:t)
  | while (cond:Value.t) (c:t)
  .
End Core.
