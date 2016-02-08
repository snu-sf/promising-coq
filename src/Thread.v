Require Import Basic.
Require Import Event.

Set Implicit Arguments.

Module Language.
  Structure t := mk {
    state: Type;
    is_terminal: state -> Prop;
    step: forall (s1:state) (e:option Event.t) (s2:state), Prop;
  }.
End Language.

Module Thread.
  Structure t := mk {
    lang: Language.t;
    state: lang.(Language.state)
  }.

  Definition is_terminal (th:t): Prop :=
    th.(lang).(Language.is_terminal) th.(state).

  Inductive step: forall (t1:t) (e:option Event.t) (t2:t), Prop :=
  | step_intro
      lang s1 e s2
      (STEP: lang.(Language.step) s1 e s2):
      step (mk lang s1) e (mk lang s2).
End Thread.

Module Threads.
  Definition t := Ident.Map.t Thread.t.

  Inductive is_terminal (p:t): Prop :=
  | is_terminal_intro
      (TERMINAL:
         forall i th
           (S: Ident.Map.find i p = Some th),
           Thread.is_terminal th)
  .

  Inductive step: forall (p1:t) (i:Ident.t) (e:option Event.t) (p1:t), Prop :=
  | step_intro
      p1 i th1 e th2
      (TH1: Ident.Map.find i p1 = Some th1)
      (STEP: Thread.step th1 e th2):
      step p1 i e (Ident.Map.add i th2 p1)
  .
End Threads.
