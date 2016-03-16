Require Import Basic.
Require Import Event.

Set Implicit Arguments.

Module Language.
  Structure t := mk {
    syntax: Type;
    state: Type;

    init: syntax -> state;
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

  Definition init (s:syntax): t :=
    mk s.(syntax_lang) (s.(syntax_lang).(Language.init) s.(syntax_syntax)).

  Definition is_terminal (th:t): Prop :=
    th.(lang).(Language.is_terminal) th.(state).

  Inductive step: forall (t1:t) (e:option ThreadEvent.t) (t2:t), Prop :=
  | step_intro
      lang s1 e s2
      (STEP: lang.(Language.step) s1 e s2):
      step (mk lang s1) e (mk lang s2).
End Thread.
