Require Import sflib.

Require Import Basic.
Require Import Thread.
Require Import Memory.
Require Import Configuration.

Set Implicit Arguments.

Module Program.
  Structure thread_t := thread_mk {
    lang: Language.t;
    text: lang.(Language.text);
  }.

  Definition t := IdentMap.t thread_t.

  Inductive load_thread: forall (text:thread_t) (th:Thread.t), Prop :=
  | load_thread_intro
      lang text s
      (LOAD: lang.(Language.load) text s):
      load_thread (thread_mk lang text) (Thread.mk lang s)
  .

  Inductive load_threads (text:t) (th:Threads.t): Prop :=
  | load_threads_intro
      (LOAD:
         forall i,
           <<NONE: IdentMap.find i text = None /\ IdentMap.find i th = None>> \/
           <<SOME: exists text' th',
                     <<TEXT: IdentMap.find i text = Some text'>> /\
                     <<THREAD: IdentMap.find i th = Some th'>> /\
                     <<LOAD: load_thread text' th'>>>>)
  .

  Inductive load: forall (text:t) (c:Configuration.t), Prop :=
  | load_intro
      text th (LOAD: load_threads text th):
      load text (Configuration.mk Clocks.init th Memory.empty nil)
  .
End Program.
