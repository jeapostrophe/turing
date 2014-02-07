Require Import List Omega.

Definition eq_dec A := forall (x y:A), { x = y } + { x <> y }.

Inductive Direction : Set :=
| DirL : Direction
| DirR : Direction.
Hint Constructors Direction.

Definition Tape (A:Type) : Type := ((list A) * (list A))%type.
Definition tape_input A (l:list A) : (Tape A) := (nil, l).
Definition tape_hd A (b:A) (t:Tape A) :=
  let (t_before, t_after) := t in
  match t_after with
    | nil =>
      b
    | a :: _ =>
      a
  end.

Definition bcons A (A_dec:eq_dec A) (b:A) (g:A) (l:list A) :=
  if A_dec b g then
    match l with
      | nil => nil
      | _ => cons g l
    end
  else
    cons g l.

Fixpoint blist A (A_dec:eq_dec A) (b:A) (l:list A) :=
  match l with
    | nil => 
      nil
    | cons g l =>
      let l' := blist A A_dec b l in
      bcons A A_dec b g l'
  end.

Definition tape_write A (A_dec:eq_dec A) (b:A) (g:A) (D:Direction) (t:Tape A) :=
  let Bcons := bcons A A_dec b in
  let Blist := blist A A_dec b in
  let (t_before, t_after) := t in
  let t_after' := 
      match t_after with
        | nil =>
          Bcons g nil
        | cons h t =>
          Bcons g t
      end
  in
  match D with
    | DirL =>
      match t_before with
        | nil =>
          ( nil, Bcons b t_after' )
        | cons t_b t_bs =>
          ( Blist t_bs, Bcons t_b t_after' )
      end
    | DirR =>
      match t_after' with
        | nil =>
          ( Bcons b t_before, nil )
        | cons t_a t_as =>
          ( Bcons t_a t_before, Blist t_as )
      end
  end.

Inductive ListNoBlankSuffix (A:Set) (b:A) : (list A) -> Prop :=
| LNBS_nil :
    ListNoBlankSuffix A b nil
| LNBS_cons_neq :
    forall l g,
      ListNoBlankSuffix A b l ->
      g <> b ->
      ListNoBlankSuffix A b (g::l)
| LNBS_cons_eq :
    forall l g,
      ListNoBlankSuffix A b (g::l) ->
      ListNoBlankSuffix A b (b::(g::l)).
Hint Constructors ListNoBlankSuffix.

Lemma bcons_nbs:
  forall A A_dec b g l,
    ListNoBlankSuffix A b l ->
    ListNoBlankSuffix A b (bcons A A_dec b g l).
Proof.
  intros A A_dec b g l LNBS. unfold bcons.
  destruct (A_dec b g) as [EQ|NEQ]. subst g.
  destruct l as [|g' l]; auto.
  auto.
Qed.
Hint Resolve bcons_nbs.

Lemma blist_nbs:
  forall A A_dec b l,
    ListNoBlankSuffix A b (blist A A_dec b l).
Proof.
  induction l as [|g l]; simpl; auto.
Qed.
Hint Resolve blist_nbs.

Definition TapeNoBlankSuffix (A:Set) (b:A) (t:Tape A) :=
  let (t_before, t_after) := t in
  ListNoBlankSuffix A b t_before /\ ListNoBlankSuffix A b t_after.

Theorem tape_write_nbs:
  forall A A_dec b g D t,
    TapeNoBlankSuffix A b t ->
    TapeNoBlankSuffix A b (tape_write A A_dec b g D t).
Proof.
  intros A A_dec b.
  intros g D t.

  destruct t as [tb ta].
  unfold TapeNoBlankSuffix.
  simpl.
  destruct D; destruct tb as [|tbh tbt]; destruct ta as [|tah tat];
  intros [LNBSb LNBSa].

  intuition.
  split; auto.
  apply bcons_nbs. apply bcons_nbs.
  inversion LNBSa; auto.
  intuition.
  intuition.
  apply bcons_nbs. apply bcons_nbs.
  inversion LNBSa; auto.
  
  destruct (bcons A A_dec b g nil) as [|bh bt]; auto.
  destruct (bcons A A_dec b g tat) as [|bh bt]; auto.
  destruct (bcons A A_dec b g nil) as [|bh bt]; auto.
  destruct (bcons A A_dec b g tat) as [|bh bt]; auto.
Qed.

Fixpoint subtract A A_dec (l:list A) (from:list A) :=
  match l with
    | nil =>
      from
    | cons a l =>
      remove A_dec a (subtract A A_dec l from)
  end.

Lemma In_remove :
  forall A A_dec l (a:A) b,
    In b (remove A_dec a l) ->
    In b l.
Proof.
  induction l as [|x l]; simpl; intros a b IN. auto.
  destruct (A_dec a x) as [EQ|NEQ].
  subst. eauto.
  simpl in IN.
  destruct IN as [EQ|IN]; eauto.
Qed.

Lemma subtract_In :
  forall A A_dec l from q,
    In q (subtract A A_dec l from) ->
    ~ In q l.
Proof.
  induction l as [|a l]; simpl.
  tauto.
  intros from q INr.
  intros [EQ | IN ].
  subst. eapply remove_In. apply INr.
  cut (In q (subtract A A_dec l from)).
  intros INs. eapply IHl. apply INs. apply IN.
  eapply In_remove. apply INr.
Qed.

Inductive QT : Set :=
|  ConsumeFirstNumber : QT
| ConsumeSecondNumber : QT
|    OverrideLastMark : QT
|       SeekBeginning : QT
|                HALT : QT.
Hint Constructors QT.

Definition QT_dec : forall (x y:QT), { x = y } + { x <> y }.
Proof. decide equality. Defined.

Definition Q :=
  (ConsumeFirstNumber
     :: ConsumeSecondNumber
     :: OverrideLastMark
     :: SeekBeginning
     :: HALT
     :: nil).
Lemma Q_ne : Q <> nil.
Proof. intros F. inversion F. Qed.

Inductive GT : Set :=
|  Mark : GT
|   Add : GT
| Blank : GT.
Hint Constructors GT.

Definition GT_dec : forall (x y:GT), { x = y } + { x <> y }.
Proof. decide equality. Defined.

Definition G := ( Mark :: Add :: Blank :: nil ).
Lemma G_ne : G <> nil.
Proof. intros F. inversion F. Qed.

Definition b := Blank.
Lemma b_in_G : In b G.
Proof. simpl. auto. Qed.

Definition TM_S := ( Mark :: Add :: nil ).
Lemma S_subset : incl TM_S (remove GT_dec b G).
Proof.
  simpl. unfold TM_S.
  apply incl_refl.
Qed.

Definition q0 := ConsumeFirstNumber.
Lemma q0_mem : In q0 Q.
Proof. simpl. auto. Qed.

Definition F := ( HALT :: nil ).
Lemma F_subset : incl F Q.
Proof. unfold F, Q. unfold incl. simpl. auto. Qed.
Definition Q_delta := (subtract QT QT_dec F Q).

Definition delta q g :=
  match (q, g) with
    | ( ConsumeFirstNumber,  Mark) => Some ( ConsumeFirstNumber,  Mark, DirR)
    | ( ConsumeFirstNumber,   Add) => Some (ConsumeSecondNumber,  Mark, DirR)
    | (ConsumeSecondNumber,  Mark) => Some (ConsumeSecondNumber,  Mark, DirR)
    | (ConsumeSecondNumber, Blank) => Some (   OverrideLastMark, Blank, DirL)
    | (   OverrideLastMark,  Mark) => Some (      SeekBeginning, Blank, DirL)
    | (      SeekBeginning,  Mark) => Some (      SeekBeginning,  Mark, DirL)
    | (      SeekBeginning, Blank) => Some (               HALT, Blank, DirR)
    | _ => None
  end.
Lemma delta_subset :
  forall q g q' g' d,
    delta q g = Some (q', g', d) ->
    ( In q Q_delta
      /\ In g G
      /\ In q' Q
      /\ In g' G ).
Proof.
  intros q g q' g' d. simpl. unfold delta.
  destruct q; destruct g; simpl; intros H; inversion_clear H; tauto.
Qed.

Inductive Step : QT -> (Tape GT) -> QT -> (Tape GT) -> Prop :=
| Step_delta :
    forall q q' g' d t,
      delta q (tape_hd GT b t) = Some (q', g', d) ->
      Step q t q' (tape_write GT GT_dec b g' d t).
Hint Constructors Step.

Theorem Step_step :
  forall q t,
    { qt' | Step q t (fst qt') (snd qt') } +
    { forall q' t',
        ~ Step q t q' t' }.
Proof.
  intros q t.
  remember (delta q (tape_hd GT b t)) as del.
  symmetry in Heqdel.
  destruct del as [[[q' g'] d]|].
  left. exists (q', (tape_write GT GT_dec b g' d t)). simpl. auto.
  right. intros q' t' Rqt.
  inversion Rqt.
  congruence.
Defined.

Lemma Step_F_done :
  forall q t q' t',
    In q F ->
    ~ Step q t q' t'.
Proof.
  intros q t q' t' IN Rqt.
  inversion Rqt. subst.
  rename H into EQdel.
  apply delta_subset in EQdel.
  destruct EQdel as [INq EQdel].
  unfold Q_delta in *.
  eapply subtract_In. apply INq. auto.
Qed.

Inductive Step_star : QT -> (Tape GT) -> nat -> QT -> (Tape GT) -> Prop :=
| Step_star_refl :
    forall q t,
      Step_star q t 0 q t
| Step_star_step :
    forall q t q' t' n q'' t'',
      Step q t q' t' ->
      Step_star q' t' n q'' t'' ->
      Step_star q t (S n) q'' t''.
Hint Constructors Step_star.

Theorem Step_star_trans:
    forall q t n q' t' m q'' t'',
      Step_star q t n q' t' ->
      Step_star q' t' m q'' t'' ->
      Step_star q t (n+m) q'' t''.
Proof.
  intros q t n q' t' m q'' t'' SSq.
  generalize m q'' t''. clear m q'' t''.
  induction SSq; intros m _q'' _t'' SSq'; simpl.
  auto.
  eapply Step_star_step.
  apply H.
  auto.
Qed.

Lemma blist_nin:
  forall A A_dec b l,
    ~ In b l ->
    blist A A_dec b l = l.
Proof.
  induction l as [|g l]; simpl; intros NIN.
  auto.
  unfold bcons. destruct (A_dec b0 g) as [EQ|NEQ].
  subst b0.
  assert False; tauto.
  rewrite IHl; tauto.
Qed.
Hint Resolve blist_nin.

Fixpoint build_list A n (a:A) :=
match n with
  | O =>
    nil
  | S n =>
    cons a (build_list A n a)
end.

Lemma build_list_nin:
  forall A x y,
    x <> y ->
    forall n,
      ~ In x (build_list A n y).
Proof.
  induction n as [|n]; simpl.
  auto.
  intros [F|F].
  symmetry in F. auto.
  auto.
Qed.
Hint Resolve build_list_nin.

Lemma blist_bl:
  forall A A_dec b g n,
    b <> g ->
    blist A A_dec b (build_list A n g) = (build_list A n g).
Proof.
  auto.
Qed.

Lemma blist_blaca:
  forall A A_dec b g g' n m,
    b <> g ->
    b <> g' ->
    blist A A_dec b ((build_list A n g) ++ g' :: (build_list A m g)) =
    ((build_list A n g) ++ g' :: (build_list A m g)).
Proof.
  intros A A_dec b g g' n m NEQg NEQg'.
  apply blist_nin.
  intros F.
  apply in_app_or in F.
  destruct F as [F|F].
  apply (build_list_nin A b g NEQg n F).
  simpl in F.
  destruct F as [F|F].
  auto.
  apply (build_list_nin A b g NEQg m F).
Qed.

Definition Pre (q:QT) : Tape GT -> (nat * nat) -> Prop :=
match q with
| ConsumeFirstNumber =>
  fun t nlr =>
    let (nl, nr) := nlr in
    let (t_before, t_after) := t in
    exists lb la,
      t_before = build_list GT lb Mark
      /\ t_after = build_list GT la Mark ++ (Add :: build_list GT nr Mark)
      /\ nl = (lb + la)
| ConsumeSecondNumber =>
  fun t nlr =>
    let (nl, nr) := nlr in
    let (t_before, t_after) := t in
    exists nb na,
      t_before = build_list GT nb Mark
      /\ t_after = build_list GT na Mark
      /\ S (nl + nr) = nb + na
| OverrideLastMark =>
  fun t nlr =>
    let (nl, nr) := nlr in
    let (t_before, t_after) := t in
     t_before = (build_list GT (nl + nr) Mark)
     /\ t_after = (Mark :: nil)
| SeekBeginning =>
  fun t nlr =>
    let (nl, nr) := nlr in
    let (t_before, t_after) := t in
    (exists l r,
       t_before = (build_list GT l Mark)
       /\ t_after = (build_list GT r Mark)
       /\ nl + nr = l + r
       /\ r >= 1)
    \/
    ( t_before = nil
      /\ t_after = bcons GT GT_dec b Blank (build_list GT (nl+nr) Mark) )
| HALT =>
  fun t nlr =>
    let (nl, nr) := nlr in
    let (t_before, t_after) := t in
       t_before = nil
    /\ t_after = (build_list GT (nl + nr) Mark)
end.

Theorem Step_Impl :
  forall q t q' t',
    Step q t q' t' ->
    forall a,
      (Pre q) t a ->
      (Pre q') t' a.
Proof.
  intros q t q' t' Rqt [nl nr] Pqt.
  inversion Rqt. subst.
  rename H into EQdel.
  remember (tape_hd GT b t) as g.
  unfold delta in EQdel.
  destruct q; destruct g; simpl in EQdel; inversion EQdel; subst;
  simpl in *; clear EQdel; unfold b in *.

  (* Case 1: ConsumeFirst -> ConsumeFirst *)
  destruct t as [t_before t_after].
  destruct Pqt as [lb [la [EQb [EQa EQn]]]].
  subst nl t_before t_after.
  simpl in *.
  destruct la as [|la]; simpl in *. inversion Heqg.
  exists (S lb). exists la. 
  simpl. intuition.
  rewrite blist_blaca; auto. congruence. congruence.

  (* Case 2: ConsumeFirst -> ConsumeSecond  *)
  destruct t as [t_before t_after].
  destruct Pqt as [lb [la [EQb [EQa EQn]]]].
  subst nl t_before t_after.
  simpl in *.
  destruct la as [|la]; simpl in *; try (inversion Heqg).
  exists (S lb). exists nr. simpl.
  intuition.

  rewrite blist_bl. auto. congruence.

  (* Case 3: ConsumeSecond -> ConsumeSecond *)
  destruct t as [t_before t_after].
  destruct Pqt as [nb [na [EQb [EQa EQn]]]].
  subst. simpl in *.
  destruct na as [|na]; simpl in *. inversion Heqg.
  exists (S nb). exists na.
  simpl. intuition.
  rewrite blist_bl. auto. congruence.

  (* Case 4: ConsumeSecond -> OverrideLast *)
  destruct t as [t_before t_after].  
  destruct Pqt as [nb [na [EQb [EQa EQn]]]].
  subst. simpl in *.
  destruct na as [|na]; simpl in *.
  destruct nb as [|nb]; simpl in *.
  omega.
  inversion EQn. rewrite H0.
  rewrite plus_0_r. intuition.
  rewrite blist_bl. auto. congruence.
  congruence.
  
  (* Case 5: OverrideLast -> SeekBeginning *)
  destruct t as [t_before t_after].
  destruct Pqt as [EQb EQa].
  subst t_before t_after. simpl in *. clear Heqg.
  remember (nl + nr) as a.
  destruct a as [|a]; unfold bcons; simpl in *.

  right. auto.

  left. exists a. exists 1. simpl.
  rewrite blist_bl; [|congruence]. intuition.

  (* Case 6: SeekBeginning -> SeekBeginning *)
  destruct t as [t_before t_after].
  destruct Pqt as [[l [r [EQb [EQa [EQn LEr]]]]]|[EQb EQa]];
    subst t_before t_after; unfold bcons;
    simpl in *.

  destruct r as [|r]; simpl in *. congruence.
  destruct l as [|l]; simpl in *.

  unfold bcons. simpl.
  right. rewrite EQn. simpl. intuition.

  left. exists l. exists (S (S r)). simpl. intuition.
  rewrite blist_bl; congruence.

  remember (nl + nr) as a.
  destruct a as [|a]; unfold bcons in *; simpl in *;
  inversion Heqg.

  (* Case 7: SeekBeginning -> HALT *)
  destruct t as [t_before t_after].  
  destruct Pqt as [[l [r [EQb [EQa [EQn LEr]]]]] | [EQb EQa]].

  rewrite EQn.
  subst t_before t_after.
  simpl in *.

  destruct r as [|r]; simpl in *.

  omega.
  inversion Heqg.

  subst t_before t_after.
  simpl in *.
  remember (nl + nr) as a.
  destruct a as [|a]; unfold bcons in *; simpl in *.
  auto.

  unfold bcons. simpl. rewrite blist_bl. auto. congruence.
Qed.

Lemma Step_star_impl:
  forall q t n q'' t'',
    Step_star q t n q'' t'' ->
    forall a,
      (Pre q) t a ->
      (Pre q'') t'' a.
Proof.
  intros q t n q'' t'' R_star_qt.
  induction R_star_qt.
  eauto.
  rename H into Rqt.
  intros a Pqt.
  eapply Step_Impl in Rqt; [|apply Pqt].
  eapply IHR_star_qt.
  apply Rqt.
Qed.

Theorem Correct :
  forall t a,
    (Pre q0) t a ->
    forall qf,
      In qf F ->
      forall n t',
        Step_star q0 t n qf t' ->
        (Pre qf) t' a.
Proof.
  intros t a Pq0 qf INqf n t' Rs_q0.
  eapply Step_star_impl. apply Rs_q0.
  apply Pq0.
Qed.

Corollary UnaryAddition_1st_to_last:
  forall t a,
    (Pre ConsumeFirstNumber) t a ->
    forall n t',
      Step_star ConsumeFirstNumber t n HALT t' ->
      (Pre HALT) t' a.
Proof.
  intros t a P n t' SS.
  eapply Correct.
  apply P.
  unfold F. simpl. auto.
  apply SS.
Qed.
  
Ltac once :=
  eapply Step_star_step; [ eapply Step_delta; simpl; reflexivity | simpl ].
Ltac run :=
  eexists; repeat once; apply Step_star_refl.

Definition Pre_impl_Next q q' :=
  forall a t,
    Pre q t a ->
    exists n t',
      Step_star q t n q' t'.
Hint Unfold Pre_impl_Next.

Lemma UnaryAddition_Halts_1:
  Pre_impl_Next ConsumeFirstNumber ConsumeSecondNumber.
Proof.
  intros [nl nr] t P.
  simpl in P. 
  destruct t as [t_before t_after].
  destruct P as [lb [la [EQb [EQa EQn]]]].
  subst. generalize lb nr. clear lb nr.
  induction la as [|la]; intros lb r; simpl.

  eexists. eexists. once. apply Step_star_refl.

  destruct (IHla (S lb) r) as [n [t' SS]].
  eexists. eexists. simpl in *. once. simpl. 
  unfold bcons. simpl. unfold b.
  rewrite blist_blaca; try congruence.
  apply SS.
Qed.

Lemma UnaryAddition_Halts_2:
  Pre_impl_Next ConsumeSecondNumber OverrideLastMark.
Proof.
  intros [nl nr] t P. simpl in P.
  destruct t as [t_before t_after].
  destruct P as [nb [na [EQb [EQa EQn]]]]. subst.

  generalize nl nr nb EQn. clear nl nr nb EQn.
  induction na as [|na]; simpl; intros nl nr nb EQn.

  eexists. eexists. once. apply Step_star_refl.

  destruct (IHna nl nr (S nb)) as [n [t' SS]].
  omega. simpl in SS.
  eexists. eexists. once. simpl.
  unfold bcons, b. simpl. 
  rewrite blist_bl; try congruence.
  apply SS.
Qed.

Lemma UnaryAddition_Halts_3:
  Pre_impl_Next OverrideLastMark SeekBeginning.
Proof.
  intros [nl nr] t P. simpl in P.
  destruct t as [t_before t_after].
  destruct P as [EQb EQa]. subst.
  eexists. eexists. once. apply Step_star_refl.
Qed.

Lemma UnaryAddition_Halts_4:
  Pre_impl_Next SeekBeginning HALT.
Proof.
  intros [nl nr] t P. simpl in P.
  destruct t as [t_before t_after].

  destruct P as [[l [r [EQb [EQa [EQn LE]]]]] | [EQb EQa]]; subst.

  destruct r as [|r]; try omega. clear LE. simpl.
  generalize nl nr r EQn. clear nl nr r EQn.
  induction l as [|l]; simpl; intros nl nr r EQn.

  destruct r as [|r]; simpl;
  eexists; eexists; once; simpl; once; simpl; apply Step_star_refl.

  destruct (IHl nl nr (S r)) as [n [t' SS]].
  omega.
  eexists. eexists. once. simpl. 
  unfold bcons, b. simpl.
  rewrite blist_bl; try congruence.
  apply SS.

  unfold bcons, b. simpl.
  remember (nl + nr) as a.
  destruct a as [|a]; simpl.

  eexists. eexists. once. apply Step_star_refl.
  eexists. eexists. once. apply Step_star_refl.
Qed.

Lemma UnaryAddition_Halts:
  forall a t,
    Pre ConsumeFirstNumber t a ->
    exists n t',
      Step_star ConsumeFirstNumber t n HALT t'.
Proof.
  intros a t P.

  Ltac UAH_step P n1 t1 SS1 l :=
    destruct (l _ _ P) as [n1 [t1 SS1]];
    apply (Step_star_impl _ _ _ _ _ SS1) in P.

  UAH_step P n1 t1 SS1 UnaryAddition_Halts_1.
  UAH_step P n2 t2 SS2 UnaryAddition_Halts_2.
  UAH_step P n3 t3 SS3 UnaryAddition_Halts_3.
  UAH_step P n4 t4 SS4 UnaryAddition_Halts_4.

  exists (n1 + (n2 + (n3 + n4))). exists t4.
  eapply Step_star_trans. apply SS1.
  eapply Step_star_trans. apply SS2.
  eapply Step_star_trans. apply SS3.
  apply SS4.
Qed.

Theorem UnaryAddition_Correct:
  forall n m,
    exists steps,
      Step_star 
        ConsumeFirstNumber 
        (tape_input GT ((build_list GT n Mark) ++ Add :: (build_list GT m Mark)))
        steps
        HALT
        (tape_input GT (build_list GT (n + m) Mark)).
Proof.
  intros n m.
  assert (Pre ConsumeFirstNumber (tape_input GT ((build_list GT n Mark) ++ Add :: (build_list GT m Mark))) (n, m)) as P.

  simpl. exists 0. exists n.
  intuition.

  destruct (UnaryAddition_Halts _ _ P) as [steps [t' SS]].
  eexists.
  replace (tape_input GT (build_list GT (n + m) Mark)) with t'.
  apply SS.
  apply UnaryAddition_1st_to_last with (a:=(n, m)) in SS.
  simpl in SS.
  destruct t' as [t_before t_after].
  destruct SS as [EQb EQa].
  subst. auto.
  auto.
Qed.

