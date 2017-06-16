Require Import Lists.List Lists.ListSet Arith.

Definition D := nat.
Definition D_eq_dec := eq_nat_dec.

Inductive DFA :
  set D -> set D -> D -> set (D*D*D) -> set D -> Type :=
| aDFA : forall (Q:set D) (Sigma:set D) (q0:D) (delta:set (D*D*D)) (F:set D),
    set_In q0 Q ->
    (forall qi a qj,
        set_In (qi,a,qj) delta ->
        (set_In qi Q /\ set_In a Sigma /\ set_In qj Q)) ->
    (forall qi a qj qk,
        set_In (qi,a,qj) delta ->
        set_In (qi,a,qk) delta ->
        qj = qk) ->
    (forall qf,
        set_In qf F ->
        set_In qf Q) ->
    (forall qi s,
        set_In qi Q ->
        set_In s Sigma ->
        { qj | set_In (qi, s, qj) delta }) ->
    DFA Q Sigma q0 delta F.
Hint Constructors DFA.

Definition Binary := set_add D_eq_dec 0 (set_add D_eq_dec 1 (@empty_set D)).

Inductive DFA_step Q Sigma q0 delta F (d:DFA Q Sigma q0 delta F) : D -> D -> D -> Prop :=
| aDFA_step : forall qi a qj,
    set_In (qi, a, qj) delta ->
    DFA_step Q Sigma q0 delta F d qi a qj.
Hint Constructors DFA_step.

Theorem DFA_step_fun:
  forall Q Sigma q0 delta F (d:DFA Q Sigma q0 delta F),
  forall qi a qj qk,
    DFA_step Q Sigma q0 delta F d qi a qj ->
    DFA_step Q Sigma q0 delta F d qi a qk ->
    qj = qk.
Proof.
  intros. rename H into DSj. rename H0 into DSk.
  destruct DSj as [qi a qj INj].
  destruct DSk as [qi a qk INk].
  destruct d as [Q Sigma q0 delta F INq0 INdelta FUNdelta INF delta_dec].
  eapply FUNdelta.
  apply INj.
  apply INk.
Qed.

Theorem DFA_step_dec:
  forall Q Sigma q0 delta F (d:DFA Q Sigma q0 delta F),
  forall qi a,
    set_In qi Q ->
    set_In a Sigma ->
    { qj | DFA_step Q Sigma q0 delta F d qi a qj /\ set_In qj Q }.
Proof.
  intros. rename H into INqi. rename H0 into INa.
  destruct d as [Q Sigma q0 delta F INq0 INdelta FUNdelta INF delta_dec].
  destruct (delta_dec qi a INqi INa) as [qj INqj].
  exists qj.
  split; auto.
  apply INdelta in INqj.
  destruct INqj as [INqi2 INqj]; destruct INqj; auto.
Qed.

Inductive DFA_steps Q Sigma q0 delta F (d:DFA Q Sigma q0 delta F) : D -> list D -> D -> Prop :=
| aDFA_steps_mt : forall qi,
    DFA_steps Q Sigma q0 delta F d qi nil qi
| aDFA_steps_cons : forall qi a qj aa qk,
    DFA_step  Q Sigma q0 delta F d qi a qj ->
    DFA_steps Q Sigma q0 delta F d qj aa qk ->
    DFA_steps Q Sigma q0 delta F d qi (cons a aa) qk.
Hint Constructors DFA_steps.

Theorem DFA_steps_fun:
  forall Q Sigma q0 delta F (d:DFA Q Sigma q0 delta F),
  forall qi w qj qk,
    DFA_steps Q Sigma q0 delta F d qi w qj ->
    DFA_steps Q Sigma q0 delta F d qi w qk ->
    qj = qk.
Proof.
  intros Q Sigma q0 delta F d.
  intros qi w. generalize w qi. clear w qi.
  induction w as [|a aa]; intros qi qj qk DS1 DS2.
  - inversion DS1. subst.
    inversion DS2. subst.  
    auto.
  - inversion DS1. subst.
    inversion DS2. subst.
    rewrite (DFA_step_fun Q Sigma q0 delta F d qi a qj0 qj1 H2 H3) in *.
    apply (IHaa qj1); auto.
Qed.

Definition all_In (D:Set) (s:set D) (l:list D) :=
  forall (a:D), In a l -> set_In a s.
Hint Unfold all_In.

Lemma all_In_eq :
  forall D Sigma a aa,
    all_In D Sigma (a :: aa) ->
    set_In a Sigma.
Proof.
  intros D Sigma a aa AI.
  apply AI. apply in_eq.
Qed.
Hint Resolve all_In_eq.

Lemma all_In_cons :
  forall D Sigma a aa,
    all_In D Sigma (a :: aa) ->
    all_In D Sigma aa.
Proof.
  intros D Sigma a aa AI.
  intros x INx.
  apply AI. apply in_cons.
  auto.
Qed.
Hint Resolve all_In_cons.

Theorem DFA_steps_dec:
  forall Q Sigma q0 delta F (d:DFA Q Sigma q0 delta F),
  forall qi aa,
    set_In qi Q ->
    all_In D Sigma aa ->
    { qj | DFA_steps Q Sigma q0 delta F d qi aa qj /\ set_In qj Q }.
Proof.
  intros. generalize aa qi H H0.
  clear aa qi H H0.
  induction aa as [|a aa]; intros qi INqi INaa.
  exists qi. auto.
  destruct (DFA_step_dec Q Sigma q0 delta F d qi a) as [qj [DS INqj]]; auto.
  eauto.
  destruct d as [Q Sigma q0 delta F INq0 INdelta FUNdelta INF delta_dec].
  destruct (IHaa qj INqj) as [qk [DSS INqk]].
  eauto.
  exists qk.
  split; auto.
  econstructor.
  apply DS.
  apply DSS.
Qed.

Inductive DFA_member Q Sigma q0 delta F (d:DFA Q Sigma q0 delta F) : list D -> Prop :=
| aDFA_mem : forall w qa,
    set_In qa F ->
    DFA_steps Q Sigma q0 delta F d q0 w qa ->
    DFA_member Q Sigma q0 delta F d w.
Hint Constructors DFA_member.

Theorem DFA_member_dec:
  forall Q Sigma q0 delta F (d:DFA Q Sigma q0 delta F),
  forall w,
    all_In D Sigma w ->
    { DFA_member Q Sigma q0 delta F d w } + { ~ DFA_member Q Sigma q0 delta F d w }.
Proof.
  intros. rename H into Aw.
  destruct (DFA_steps_dec Q Sigma q0 delta F d q0 w) as [qa [DSS INqj]]; auto.
  destruct d as [Q Sigma q0 delta F INq0 INdelta FUNdelta INF delta_dec].
  auto.
  destruct (set_In_dec D_eq_dec qa F) as [INa | NINa].
  left. econstructor.
  apply INa. auto.
  right. intros DM.
  destruct DM as [w qa2 NINa2 DSS2].
  rewrite (DFA_steps_fun Q Sigma q0 delta F d q0 w qa qa2 DSS DSS2) in *.
  apply NINa. auto.
Qed.
