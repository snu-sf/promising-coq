Require Import Basic.
Require Import Event.

Set Implicit Arguments.

Module Language.
  Structure t := mk {
    syntax: Type;
    state: Type;

    load: syntax -> state;
    is_terminal: state -> Prop;
    step: forall (s1:state) (e:option ThreadEvent.t) (s2:state), Prop;
  }.
End Language.

Module Thread.
  Structure syntax := mk_syntax {
    syntax_lang: Language.t;
    syntax_syntax: syntax_lang.(Language.syntax);
  }.

  Structure t := mk {
    lang: Language.t;
    state: lang.(Language.state)
  }.

  Definition load (s:syntax): t :=
    mk s.(syntax_lang) (s.(syntax_lang).(Language.load) s.(syntax_syntax)).

  Definition is_terminal (th:t): Prop :=
    th.(lang).(Language.is_terminal) th.(state).

  Inductive step: forall (t1:t) (e:option ThreadEvent.t) (t2:t), Prop :=
  | step_intro
      lang s1 e s2
      (STEP: lang.(Language.step) s1 e s2):
      step (mk lang s1) e (mk lang s2).
End Thread.

Module Program.
  Definition syntax := IdentMap.t Thread.syntax.

  Definition t := IdentMap.t Thread.t.

  Definition empty := IdentMap.empty Thread.t.

  Definition load (s:syntax): t :=
    IdentMap.map Thread.load s.

  Inductive is_terminal (p:t): Prop :=
  | is_terminal_intro
      (TERMINAL:
         forall i th (THREAD: IdentMap.find i p = Some th),
           Thread.is_terminal th)
  .

  Inductive step: forall (p1:t) (i:Ident.t) (e:option ThreadEvent.t) (p1:t), Prop :=
  | step_intro
      p1 th1 th2 i e
      (THREAD: IdentMap.find i p1 = Some th1)
      (STEP: Thread.step th1 e th2):
      step p1 i e (IdentMap.add i th2 p1)
  .
End Program.
