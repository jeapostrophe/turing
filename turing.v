Require Import List Omega.

Inductive Direction : Set :=
| DirL : Direction
| DirR : Direction.
Hint Constructors Direction.

Definition Tape (A:Type) : Type := ((list A) * (list A))%type.
Definition tape_input A (l:list A) : (Tape A) := (nil, l).
Definition tape_list A (t:Tape A) : (list A) :=
  let (t_before, t_after) := t in
  (rev t_before) ++ t_after.
Definition tape_hd A (b:A) (t:Tape A) :=
  let (t_before, t_after) := t in
  match t_after with
    | nil =>
      b
    | a :: _ =>
      a
  end.
Definition tape_write A (b:A) (g:A) (D:Direction) (t:Tape A) :=
  let (t_before, t_after) := t in
  let t_after' := 
      match t_after with
        | nil =>
          cons g nil
        | cons h t =>
          cons g t
      end
  in
  match D with
    | DirL =>
      match t_before with
        | nil =>
          ( nil, cons b t_after' )
        | cons t_b t_bs =>
          ( t_bs, cons t_b t_after' )
      end
    | DirR =>
      match t_after' with
        | nil =>
          ( cons b t_before, nil )
        | cons t_a t_as =>
          ( cons t_a t_before, t_as )
      end
  end.

Example tape_write0: 
  (tape_write nat 0 1 DirL (tape_input nat nil)) = ( nil, 0 :: 1 :: nil ).
Proof. auto. Qed.

Example tape_write1: 
  (tape_write nat 0 1 DirR (tape_input nat nil)) = ( 1:: nil, nil ).
Proof. auto. Qed.

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
| ConsumeFirstNumber : QT
| ConsumeSecondNumber : QT
| OverrideLastMark : QT
| SeekBeginning : QT
| HALT : QT.
Hint Constructors QT.

Definition QT_dec : forall (x y:QT), { x = y } + { x <> y }.
Proof. decide equality. Qed.

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
| Mark : GT
| Add : GT
| Blank : GT.
Hint Constructors GT.

Definition GT_dec : forall (x y:GT), { x = y } + { x <> y }.
Proof. decide equality. Qed.

Definition G := ( Mark :: Add :: Blank :: nil ).
Lemma G_ne : G <> nil.
Proof. intros F. inversion F. Qed.

Definition b := Blank.
Lemma b_in_G : In b G.
Proof. simpl. auto. Qed.

Definition TM_S := ( Mark :: Add :: nil ).
Lemma S_subset : incl TM_S (remove GT_dec b G).
Proof.
  simpl. unfold b. unfold TM_S.
  Ltac dgd r :=
    destruct (GT_dec Blank r) as [BAD|GOOD]; [ inversion BAD | clear GOOD ].
  dgd Mark.
  dgd Add.
  destruct (GT_dec Blank Blank) as [GOOD|BAD]. apply incl_refl.
  tauto.
Qed.

Definition q0 := ConsumeFirstNumber.
Lemma q0_mem : In q0 Q.
Proof. simpl. auto. Qed.

Definition F := ( HALT :: nil ).
Lemma F_subset : incl F Q.
Proof. unfold F, Q. unfold incl. simpl. auto. Qed.
Definition Q_delta := (subtract QT QT_dec F Q).
Lemma Q_delta_eq :
  Q_delta =
  (ConsumeFirstNumber
     :: ConsumeSecondNumber
     :: OverrideLastMark
     :: SeekBeginning
     :: nil).
Proof.
  unfold Q_delta, Q, F. simpl.

  Ltac dqd r :=
    destruct (QT_dec HALT r) as [BAD|GOOD]; [ inversion BAD | clear GOOD ].
  dqd ConsumeFirstNumber.
  dqd ConsumeSecondNumber.
  dqd SeekBeginning.
  dqd OverrideLastMark.
  destruct (QT_dec HALT HALT) as [GOOD|BAD]; tauto.
Qed.

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
  intros q g q' g' d.
  rewrite Q_delta_eq. unfold delta.
  destruct q; destruct g; simpl; intros H; inversion_clear H; tauto.
Qed.

Inductive Step : QT -> (Tape GT) -> QT -> (Tape GT) -> Prop :=
| Step_delta :
    forall q q' g' d t,
      delta q (tape_hd GT b t) = Some (q', g', d) ->
      Step q t q' (tape_write GT b g' d t).
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
  left. exists (q', (tape_write GT b g' d t)). simpl. auto.
  right. intros q' t' Rqt.
  inversion Rqt.
  congruence.
Defined.

Eval compute in (Step_step ConsumeFirstNumber 
                           (tape_input GT (Mark :: Add :: Mark :: nil))).

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

Inductive Step_star : QT -> (Tape GT) -> QT -> (Tape GT) -> Prop :=
| Step_star_refl :
    forall q t,
      Step_star q t q t
| Step_star_step :
    forall q t q' t' q'' t'',
      Step q t q' t' ->
      Step_star q' t' q'' t'' ->
      Step_star q t q'' t''.
Hint Constructors Step_star.

Fixpoint split_at A (A_dec:forall (x y:A), { x = y } + { x <> y }) (x:A) (l:list A) :=
match l with
  | nil =>
    inr tt
  | cons y l =>
    if A_dec x y then
      inl (nil, l)
    else
      let r := split_at A A_dec x l in
      match r with
        | inr _ => r
        | inl ba =>
          let (b, a) := ba in
          inl ( y :: b, a )
      end
end.

Ltac gteq r :=
  destruct (GT_dec r r) as [GOOD|BAD]; [ clear GOOD | congruence ].
Ltac gtneq x y :=
  destruct (GT_dec x y) as [BAD|GOOD]; [ inversion BAD | clear GOOD ].
Ltac gt_all :=
  gteq Mark; gteq Add; gteq Blank;
  gtneq Mark Add; gtneq Mark Blank;
  gtneq Blank Add; gtneq Blank Mark;
  gtneq Add Blank; gtneq Add Mark.

Fixpoint build_list A n (a:A) :=
match n with
  | O =>
    nil
  | S n =>
    cons a (build_list A n a)
end.

Definition Pre (q:QT) : Tape GT -> nat -> Prop :=
match q with
| ConsumeFirstNumber =>
  fun t n =>
    let (t_before, t_after) := t in
    exists lb la r,
      t_before = build_list GT lb Mark
      /\ t_after = build_list GT la Mark ++ (Add :: build_list GT r Mark)
      /\ n = (lb + la) + r
      /\ n >= 2
| ConsumeSecondNumber =>
  fun t n =>
    tape_list GT t = (build_list GT (S n) Mark)
    /\ n >= 2
| OverrideLastMark =>
  fun t n =>
    let (t_before, t_after) := t in
     t_before = (build_list GT n Mark)
     /\ t_after = (Mark :: Blank :: nil)
     /\ n >= 2
| SeekBeginning =>
  fun t n =>
    let (t_before, t_after) := t in
    (exists l r,
      t_before = (build_list GT l Mark)
      /\ t_after = ((build_list GT r Mark) ++ Blank :: Blank :: nil)
      /\ n = l + r
      /\ r >= 1
      /\ n >= 2)
    \/
    ( t_before = nil
      /\ t_after = Blank :: ((build_list GT n Mark) ++ Blank :: Blank :: nil)
      /\ n >= 2)
| HALT =>
  fun t n =>
    let (t_before, t_after) := t in
       t_before = Blank :: nil
    /\ t_after = (build_list GT n Mark) ++ Blank :: Blank :: nil
    /\ n >= 2
end.

Lemma cons_build_list:
  forall A n x,
    x :: (build_list A n x) = (build_list A (S n) x).
Proof.
  induction n as [|n]; simpl; intros x.
  auto.
  rewrite IHn. auto.
Qed.

Lemma build_list_snoc:
  forall A n x,
    (build_list A n x) ++ (x :: nil) = (build_list A (S n) x).
Proof.
  induction n as [|n]; simpl; intros x.
  auto.
  rewrite IHn. auto.
Qed.

Lemma build_list_rev:
  forall A n x,
    rev (build_list A n x) = (build_list A n x).
Proof.
  induction n as [|n]; intros x.
  auto.
  simpl. rewrite IHn.
  apply build_list_snoc.
Qed.

Lemma build_list_app:
  forall A n m x,
    (build_list A n x) ++ (build_list A m x) = (build_list A (n + m) x).
Proof.
  induction n as [|n]; simpl; intros m x.
  auto.
  rewrite IHn. auto.
Qed.

Lemma rev_eq_eq:
  forall A (x:list A) y,
    rev x = rev y ->
    x = y.
Proof.
  induction x as [|x xs]; simpl.

  induction y as [|y ys]; simpl; intros EQ.
  auto.
  apply app_cons_not_nil in EQ.
  tauto.

  intros y EQ.
  destruct y as [|y ys]; simpl in *.
  symmetry in EQ.
  apply app_cons_not_nil in EQ.
  tauto.
  apply app_inj_tail in EQ.
  destruct EQ as [EQ0 EQ1].
  subst y.
  erewrite IHxs; auto.
Qed.

Lemma In_not_eq:
  forall A (a:A) x y,
    x = y ->
    In a x ->
    ~ In a y ->
    False.
Proof.
  induction x as [|x]; simpl; intros y EQ IN NIN.
  auto.
  subst y. 
  destruct IN as [EQ|IN].
  subst a.
  apply NIN. simpl. auto.
  eapply IHx.
  reflexivity.
  auto.
  intros F.
  apply NIN.
  simpl. auto.
Qed.

Lemma build_list_not_In:
  forall A n x y,
    x <> y ->
    ~ In x (build_list A n y).
Proof.
  induction n as [|n]; simpl; intros x y NEQ.
  tauto.
  intros [ EQ | IN ].
  subst y. tauto.
  eapply IHn. apply NEQ. apply IN.
Qed.

Theorem Step_Impl :
  forall q t q' t',
    Step q t q' t' ->
    forall a,
      (Pre q) t a ->
      (Pre q') t' a.
Proof.
  intros q t q' t' Rqt a Pqt.
  inversion Rqt. subst.
  rename H into EQdel.
  remember (tape_hd GT b t) as g.
  unfold delta in EQdel.
  destruct q; destruct g; simpl in EQdel; inversion EQdel; subst;
  simpl in *; clear EQdel.

  (* Case 1: ConsumeFirst -> ConsumeFirst *)
  destruct t as [t_before t_after].
  destruct Pqt as [lb [la [r [EQb [EQa [EQn Ln]]]]]].
  subst a t_before t_after.
  simpl in *.
  destruct la as [|la]; simpl in *. inversion Heqg.
  exists (S lb). exists la. exists r.
  simpl. intuition.

  (* Case 2: ConsumeFirst -> ConsumeSecond  *)
  destruct t as [t_before t_after].
  destruct Pqt as [lb [la [r [EQb [EQa [EQn Ln]]]]]].
  subst a t_before t_after.
  simpl in *.
  destruct la as [|la]; simpl in *; try (inversion Heqg).
  rewrite plus_0_r.
  rewrite build_list_rev.
  rewrite cons_build_list.
  rewrite build_list_snoc.
  rewrite build_list_app.
  intuition.

  (* Case 3: ConsumeSecond -> ConsumeSecond *)
  destruct t as [t_before t_after].
  destruct Pqt as [ EQt LEn ].
  destruct t_after as [|t_after_hd t_after_tl]; simpl in *; subst.
  inversion Heqg.
  rewrite <- EQt. rewrite <- app_assoc. auto.

  (* Case 4: ConsumeSecond -> OverrideLast *)
  destruct t as [t_before t_after].  
  destruct Pqt as [EQ LE]. 
  destruct t_after as [|t_after_hd t_after_tl]; simpl in *; subst.
  destruct t_before as [|t_before_hd t_before_tl]; simpl in *; subst.
  congruence.
  clear Heqg.
  rewrite app_nil_r in *.
  rewrite cons_build_list in EQ.
  replace (S a) with (a + 1) in EQ; try omega.
  rewrite <- build_list_app in EQ.
  simpl in EQ.
  apply app_inj_tail in EQ.
  destruct EQ as [EQ0 EQ1].
  rewrite EQ1.
  rewrite <- build_list_rev in EQ0.
  apply rev_eq_eq in EQ0. auto.

  clear LE. assert False; try tauto.
  apply (In_not_eq GT Blank _ _ EQ). 
  apply in_or_app. right. simpl. left. auto.
  simpl. intros [F|F]; try congruence.
  apply (build_list_not_In GT a Blank Mark); auto. congruence.
  
  (* Case 5: OverrideLast -> SeekBeginning *)
  destruct t as [t_before t_after].
  destruct Pqt as [EQb [EQa LE]].
  subst t_before t_after. simpl in *. clear Heqg.
  destruct a as [|a]; try omega.
  simpl in *. left. exists a. exists 1. simpl.
  intuition; omega.

  (* Case 6: SeekBeginning -> SeekBeginning *)
  destruct t as [t_before t_after].
  destruct Pqt as [[l [r [EQb [EQa [EQn [LEr LEn]]]]]] | [EQb [EQa LEn]]];
    subst t_before t_after;
    simpl in *.

  destruct r as [|r]; try omega.
  simpl in *.
  destruct l as [|l]; simpl in *.

  right. subst a. simpl. intuition.

  left. exists l. exists (S (S r)). simpl. intuition.

  inversion Heqg.

  (* Case 7: SeekBeginning -> HALT *)
  destruct t as [t_before t_after].  
  destruct Pqt as [[l [r [EQb [EQa [EQn [LEr LEn]]]]]] | [EQb [EQa LEn]]].
  subst a t_before t_after.
  destruct r as [|r]; try omega.
  simpl in *. inversion Heqg.

  subst t_before t_after.
  simpl in *.
  destruct a as [|a]; try omega.
  simpl in *.
  intuition.
Qed.

Lemma Step_star_impl:
  forall q t q'' t'',
    Step_star q t q'' t'' ->
    forall a,
      (Pre q) t a ->
      (Pre q'') t'' a.
Proof.
  intros q t q'' t'' R_star_qt.
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
      forall t',
        Step_star q0 t qf t' ->
        (Pre qf) t' a.
Proof.
  intros t a Pq0 qf INqf t' Rs_q0.
  eapply Step_star_impl. apply Rs_q0.
  apply Pq0.
Qed.

Corollary UnaryAddition_1st_to_last:
  forall t a t',
    (Pre ConsumeFirstNumber) t a ->
    Step_star ConsumeFirstNumber t HALT t' ->
    (Pre HALT) t' a.
Proof.
  intros t a t' P SS.
  eapply Correct.
  apply P.
  unfold F. simpl. auto.
  auto.
Qed.
  
Ltac once :=
  eapply Step_star_step; [ eapply Step_delta; simpl; reflexivity | simpl ].
Ltac run :=
  eexists; repeat once; apply Step_star_refl.

Example UnaryAddition_Runs_on_2Plus3:
 exists t',
   Step_star ConsumeFirstNumber 
             (tape_input GT (Mark :: Mark :: Add :: Mark :: Mark :: Mark :: nil))
             HALT
             t'. 
Proof. run. Qed.

Corollary UnaryAddition_Correct_on_2Plus3:
  forall t',
    Step_star ConsumeFirstNumber 
              (tape_input GT (Mark :: Mark :: Add :: Mark :: Mark :: Mark :: nil))
              HALT
              t'
    ->
    (Pre HALT) t' 5.
Proof.
  intros t'.
  eapply UnaryAddition_1st_to_last.
  simpl. 
  exists 0. exists 2. exists 3.
  simpl. intuition.
Qed.

Theorem UnaryAddition_Correct_on_NPlusM:
  forall n m t',
    n >= 1 ->
    m >= 1 ->
    Step_star ConsumeFirstNumber 
              (tape_input GT ((build_list GT n Mark)
                                ++ Add :: (build_list GT m Mark)))
              HALT
              t' ->
    (Pre HALT) t' (n + m).
Proof.
  intros n m t' LEn LEm SS.
  eapply UnaryAddition_1st_to_last; try apply SS.
  simpl.
  exists 0. exists n. exists m.
  intuition.
Qed.

(* XXX It would be nice to prove that this NPlusM input always halts,
but I don't think normal induction will work on Step_star. *)

Lemma UnaryAddition_Halts:
  forall n m,
    n >= 1 ->
    m >= 1 ->
    exists t',
      Step_star ConsumeFirstNumber 
                (tape_input GT 
                            ((build_list GT n Mark) 
                               ++ Add :: (build_list GT m Mark)))
                HALT
                t'.
Proof.
Admitted.

Theorem UnaryAddition_Correct:
  forall n m,
    n >= 1 ->
    m >= 1 ->
    Step_star 
      ConsumeFirstNumber 
      (tape_input GT ((build_list GT n Mark) ++ Add :: (build_list GT m Mark)))
      HALT
      (Blank :: nil, ((build_list GT (n + m) Mark) ++ Blank :: Blank :: nil)).
Proof.
  intros n m LEn LEm.
  destruct (UnaryAddition_Halts n m LEn LEm) as [t' SS].
  replace (Blank :: nil, build_list GT (n + m) Mark ++ Blank :: Blank :: nil) with t'.
  auto.
  apply UnaryAddition_1st_to_last with (a:=n + m) in SS.
  simpl in SS.
  destruct t' as [t_before t_after].
  destruct SS as [EQb [EQa LE]].
  subst. auto.

  simpl.
  exists 0. exists n. exists m.
  intuition.
Qed.

