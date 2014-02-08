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

Definition CFN_Tape lb la nr t_before t_after :=
  t_before = build_list GT lb Mark
  /\ t_after = build_list GT la Mark ++ (Add :: build_list GT nr Mark).

Definition Pre (q:QT) : Tape GT -> (nat * nat) -> Prop :=
match q with
| ConsumeFirstNumber =>
  fun t nlr =>
    let (nl, nr) := nlr in
    let (t_before, t_after) := t in
    CFN_Tape 0 nl nr t_before t_after
| ConsumeSecondNumber =>
  fun t nlr =>
    let (nl, nr) := nlr in
    let (t_before, t_after) := t in
    t_before = build_list GT (S nl) Mark
    /\ t_after = build_list GT nr Mark
| OverrideLastMark =>
  fun t nlr =>
    let (nl, nr) := nlr in
    let (t_before, t_after) := t in
    t_before = (build_list GT (nl + nr) Mark)
    /\ t_after = Mark :: nil
| SeekBeginning =>
  fun t nlr =>
    let (nl, nr) := nlr in
    let (t_before, t_after) := t in
    match (nl + nr) with
        | O =>
          t_before = nil /\ t_after = nil
        | S n =>
          t_before = (build_list GT n Mark)
          /\ t_after = Mark :: nil
    end
| HALT =>
  fun t nlr =>
    let (nl, nr) := nlr in
    let (t_before, t_after) := t in
    t_before = nil
    /\ t_after = (build_list GT (nl + nr) Mark)
end.

Definition Invariant (q:QT) : Tape GT -> (nat * nat) -> Prop :=
match q with
| ConsumeFirstNumber =>
  fun t nlr =>
    let (nl, nr) := nlr in
    let (t_before, t_after) := t in
    exists lb la,
      CFN_Tape lb la nr t_before t_after
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
    True
| SeekBeginning =>
  fun t nlr =>
    let (nl, nr) := nlr in
    let (t_before, t_after) := t in
    exists l r,
      t_before = (build_list GT l Mark)
      /\ t_after = (build_list GT r Mark)
      /\ nl + nr = l + r
| HALT =>
  fun t nlr =>
    True
end.

Definition Post (q:QT) : Tape GT -> (nat * nat) -> Prop :=
match q with
| ConsumeFirstNumber =>
  fun t nlr =>
    let (nl, nr) := nlr in
    let (t_before, t_after) := t in
    CFN_Tape nl 0 nr t_before t_after
| ConsumeSecondNumber =>
  fun t nlr =>
    let (nl, nr) := nlr in
    let (t_before, t_after) := t in
    t_before = build_list GT ((S nl) + nr) Mark
    /\ t_after = nil
| OverrideLastMark =>
  fun t nlr =>
    let (nl, nr) := nlr in
    let (t_before, t_after) := t in
    t_before = (build_list GT (nl + nr) Mark)
    /\ t_after = Mark :: nil
| SeekBeginning =>
  fun t nlr =>
    let (nl, nr) := nlr in
    let (t_before, t_after) := t in
    t_before = nil
    /\ t_after = bcons GT GT_dec b Blank (build_list GT (nl+nr) Mark)
| HALT =>
  fun t nlr =>
    let (nl, nr) := nlr in
    let (t_before, t_after) := t in
    t_before = nil
    /\ t_after = (build_list GT (nl + nr) Mark)
end.

Theorem Pre_impl_Invariant:
  forall q t a,
    Pre q t a ->
    Invariant q t a.
Proof.
  intros q [tb ta] [nl nr].
  destruct q; simpl; auto.

  intros P. exists 0. exists nl. intuition.

  intros [EQb EQa]. subst.
  exists (S nl). exists nr. intuition.

  remember (nl + nr) as n.
  destruct n as [|n];
    intros [EQb EQa]; subst.
  
  exists 0. exists 0. intuition.
  exists n. exists 1. intuition.
Qed.

Theorem Step_Post_impl_Pre :
  forall q t a,
    (Post q) t a ->
    forall q' t',
      q <> q' ->
      Step q t q' t' ->
      (Pre q') t' a.
Proof.
  intros q [tb ta] [nl nr] Pqt q' t' NEQ SS.
  inversion SS. subst. clear SS.
  rename H into EQdel.
  remember (tape_hd GT b (tb, ta)) as g.
  unfold delta in EQdel.
  destruct q; destruct g; simpl in EQdel; inversion EQdel; subst;
  simpl in *; clear EQdel; unfold b in *; try congruence.

  (* First -> Second *)
  destruct ta as [|tah tat]. congruence.
  destruct Pqt; subst. inversion_clear H0.
  unfold bcons. simpl. rewrite blist_bl; try congruence.
  auto.

  (* Second -> Override *)
  destruct Pqt; subst. 
  rewrite blist_bl; try congruence.
  unfold bcons. simpl. auto.

  (* Override -> Seek *)
  destruct Pqt; subst.
  remember (nl + nr) as n.
  destruct n as [|n]; simpl.
  auto.
  rewrite blist_bl; try congruence.
  auto.

  (* Seek -> HALT *)
  destruct Pqt; subst.
  remember (nl + nr) as n.
  destruct n as [|n]; simpl in *.
  auto.
  rewrite blist_bl; try congruence.
  auto.
Qed.

Theorem Step_Inv_impl_InvPost :
  forall q t a,
    (Invariant q) t a ->
    forall t',
      Step q t q t' ->
      ((Invariant q) t' a) \/ ((Post q) t' a).
Proof.
  intros q [tb ta] [nl nr] Pqt t' SS.
  inversion SS. subst. clear SS.
  rename H into EQdel.
  remember (tape_hd GT b (tb, ta)) as g.
  unfold delta in EQdel.
  destruct q; destruct g; simpl in EQdel; inversion EQdel; subst;
  simpl in *; clear EQdel; unfold b in *; try congruence.

  (* First -> First *)
  left. destruct Pqt as [lb [la [[EQb EQa] EQn]]]. subst.
  destruct la as [|la]; simpl in *.
  congruence.
  unfold bcons. simpl.
  rewrite blist_blaca; try congruence.
  exists (S lb). exists la. unfold CFN_Tape. intuition.

  (* Second -> Second *)
  left. destruct Pqt as [nb [na [EQb [EQa EQn]]]]. subst.
  destruct na as [|na]; simpl in *.
  congruence.
  rewrite blist_bl; try congruence.
  exists (S nb). exists na.
  intuition.

  (* Seek -> Seek *)
  destruct Pqt as [l [r [EQb [EQa EQn]]]]. subst.
  destruct r as [|r]; simpl in *.
  congruence.
  rewrite EQn. clear nl nr EQn. simpl.
  destruct l as [|l]; simpl in *.

  right. auto.

  left. exists l. exists (S (S r)).
  rewrite blist_bl; try congruence.
  intuition.
Qed.

Ltac once :=
  eapply Step_star_step; [ eapply Step_delta; simpl; reflexivity | simpl ].
Ltac run :=
  eexists; repeat once; apply Step_star_refl.

Definition delta_next q q' :=
  (exists g g' d, delta q g = Some (q', g', d) /\ q <> q').

(* XXX generalize this for machines with two nexts? *)

Theorem Step_Post_next :
  forall q t a,
    (Post q) t a ->
    forall q',
      delta_next q q' ->
      exists t',
        Step q t q' t'.
Proof.
  intros q [tb ta] [nl nr] Pqt q' [g [g' [d [EQd NEQ]]]].
  destruct q; destruct g; unfold delta in *; simpl in *;
  inversion EQd; subst; clear EQd; try congruence.

  destruct Pqt; subst.
  eexists. eapply Step_delta. simpl. reflexivity.

  destruct Pqt; subst.
  eexists. eapply Step_delta. simpl. reflexivity.

  destruct Pqt; subst.
  eexists. eapply Step_delta. simpl. reflexivity.

  destruct Pqt; subst.
  eexists. eapply Step_delta. unfold b.
  remember (nl + nr) as n.
  destruct n as [|n]; simpl.
  reflexivity.
  reflexivity.
Qed.

(* XXX: Figure out how to specify n on all these *)

Definition delta_loops q :=
  (exists g g' d, delta q g = Some (q, g', d)).

Theorem Step_star_Pre_Post :
  forall q t a,
    (Pre q) t a ->
    delta_loops q ->
    exists n t',
      Step_star q t n q t'
      /\ Post q t' a.
Proof.
  intros q [tb ta] [nl nr] Pqt [g [g' [d EQd]]].
  destruct q; destruct g; unfold delta in EQd; simpl in EQd;
  inversion EQd; subst; clear EQd; try congruence.

  (* First -> First *)
  apply Pre_impl_Invariant in Pqt.
  destruct Pqt as [lb [la [[EQb EQa] EQn]]]. subst.
  generalize nr lb. clear nr lb.
  induction la as [|la]; intros nr lb.
  
  eexists. eexists. split.
  apply Step_star_refl.
  simpl. unfold CFN_Tape. rewrite plus_0_r. simpl. auto.

  destruct (IHla nr (S lb)) as [n' [t' [SS P]]].
  eexists. eexists. split.
  once. unfold b. simpl. rewrite blist_blaca; try congruence.
  unfold bcons. simpl. simpl in SS. apply SS.
  replace (lb + S la) with (S lb + la).
  auto. omega.

  (* Second -> Second *)
  apply Pre_impl_Invariant in Pqt.
  destruct Pqt as [l [r [EQb [EQa EQn]]]]. subst.
  generalize nl nr l EQn. clear nl nr l EQn.
  induction r as [|r]; intros nl nr l EQn.

  eexists. eexists. split.
  apply Step_star_refl. rewrite plus_0_r in EQn. subst l.
  simpl. auto.

  destruct (IHr nl nr (S l)) as [n' [t' [SS P]]].
  omega.
  eexists. eexists. split.
  simpl. once. unfold b. simpl.
  rewrite blist_bl; try congruence.
  unfold bcons. simpl. apply SS.
  auto.

  (* Seek -> Seek *)
  assert (Invariant SeekBeginning (tb, ta) (nl, nr)) as Iqt.
  apply Pre_impl_Invariant. auto.
  destruct Iqt as [l [r [EQb [EQa EQn]]]].
  simpl in Pqt. subst. simpl.

  rewrite EQn in *. clear EQn nl nr.
  remember (l + r) as lr. rename Heqlr into EQlr.
  destruct lr as [|lr].

  exists 0. exists (nil, nil).
  replace l with 0; try omega.
  replace r with 0; try omega.
  auto.

  destruct r as [|r]; simpl in *.
  destruct Pqt. congruence.
  replace lr with (l + r) in *; try omega.
  clear lr EQlr Pqt.

  generalize r. clear r.
  induction l as [|l]; simpl; intros r.

  eexists. eexists. split.
  once. apply Step_star_refl. simpl. auto.

  destruct (IHl (S r)) as [n' [[tb' ta'] [SS [EQb' EQa']]]]. subst.
  eexists. eexists. split.
  once. simpl. unfold b in *.
  rewrite blist_bl; try congruence.
  unfold bcons in *. simpl in *.
  apply SS. simpl.
  replace (l + S r) with (S (l + r)); try omega.
  simpl. auto.
Qed.

Theorem Step_star_Pre_Post_neloop :
  forall q t a,
    (Pre q) t a ->
    ~ delta_loops q ->
    (Post q) t a.
Proof.
  intros q t [nl nr] P NDL.
  unfold delta_loops, Pre, Post, delta in *.
  destruct q; auto;
  assert False; try tauto;
  apply NDL.

  (* First *)
  exists Mark. eauto.

  (* Second *)
  exists Mark. eauto.

  (* Seek *)
  exists Mark. eauto.
Qed.

Theorem delta_loops_dec:
  forall q,
    { delta_loops q } + { ~ delta_loops q }.
Proof.
  intros q. unfold delta_loops, delta.
  destruct q; simpl.

  left. exists Mark. eauto.
  left. exists Mark. eauto.
  right. intros [g [g' [d EQ]]]. destruct g; congruence.
  left. exists Mark. eauto.
  right. intros [g [g' [d EQ]]]. destruct g; congruence.
Qed.

Theorem Step_star_Pre_next :
  forall q t a,
    (Pre q) t a ->
    forall q',
      delta_next q q' ->
      exists n t',
        Step_star q t n q' t'
        /\ (Pre q') t' a.
Proof.
  intros q [tb ta] [nl nr] Pqt q' [g [g' [d [EQd NEQ]]]].
  destruct q; destruct g; simpl in EQd; inversion EQd; subst; clear EQd;
  try congruence.

  (* First -> Second *)
  apply Pre_impl_Invariant in Pqt.
  destruct Pqt as [lb [la [[EQb EQa] EQn]]]. subst.
  generalize nr lb. clear nr lb.
  induction la as [|la]; simpl; intros nr lb.
  
  eexists. eexists. split. once. apply Step_star_refl.
  simpl. unfold bcons, b. simpl. rewrite plus_0_r.
  rewrite blist_bl; try congruence. auto.

  destruct (IHla nr (S lb)) as [n' [t' [SS P]]].
  eexists (S n'). exists t'.
  split. once. unfold b. simpl. rewrite blist_blaca; try congruence.
  simpl in SS. apply SS.
  simpl in P. destruct t' as [tb' ta'].
  replace (lb + S la) with (S (lb + la)); try omega.
  simpl. auto.

  (* Second -> Override *)
  apply Pre_impl_Invariant in Pqt.
  destruct Pqt as [l [r [EQb [EQa EQn]]]]. subst.
  generalize nl nr l EQn. clear nl nr l EQn.
  induction r as [|r]; simpl; intros nl nr l EQn.
  
  eexists. eexists. split. once. apply Step_star_refl.
  rewrite plus_0_r in EQn. subst l.
  simpl. unfold b, bcons. 
  rewrite blist_bl; try congruence.
  simpl. auto.

  destruct (IHr nl nr (S l)) as [n' [t' [SS P]]].
  omega.
  eexists (S n'). exists t'.
  split. once. unfold b. simpl. rewrite blist_bl; try congruence.
  simpl in SS. apply SS.
  destruct t' as [tb' ta']. simpl in P.
  auto.

  (* Override -> Seek *)
  destruct Pqt as [EQb EQa]. subst.
  eexists. eexists. split. once. apply Step_star_refl.
  simpl. unfold b, bcons. simpl.
  destruct (nl + nr); simpl. auto.
  rewrite blist_bl; try congruence. auto.

  (* Seek -> HALT *)
  apply Step_star_Pre_Post in Pqt.
  destruct Pqt as [n' [[tb' ta'] [SS Pqt']]].
  destruct Pqt'. subst.

  unfold b, bcons in *. simpl in SS.
  remember (nl + nr) as n.
  destruct n as [|n]; simpl in SS.

  eexists. eexists.
  split. eapply Step_star_trans.
  apply SS. once. apply Step_star_refl.
  simpl. rewrite <- Heqn.
  unfold bcons, b. simpl. auto.

  eexists. eexists.
  split. eapply Step_star_trans.
  apply SS. once. apply Step_star_refl.
  simpl. rewrite <- Heqn.
  unfold bcons, b. simpl. 
  rewrite blist_bl; try congruence. auto.

  unfold delta_loops.
  exists Mark. eexists. eexists.
  unfold delta. auto.
Qed.

Theorem Step_next_or_loop:
  forall q t q' t',
    Step q t q' t' ->
    ( q <> q' /\ delta_next q q')
    \/ (q = q' /\ delta_loops q).
Proof.
  intros q t q' t' S1.
  inversion S1. subst.
  rename H into EQd.
  unfold delta_next, delta_loops.
  destruct (QT_dec q q') as [EQ|NEQ].

  subst. right. eauto. 

  left. split. auto.
  exists (tape_hd GT b t). exists g'. exists d.
  auto.
Qed.

Inductive delta_trans : QT -> QT -> Prop :=
| dt_refl:
    forall q,
      delta_trans q q
| dt_next:
    forall q q' q'',
      delta_next q q' ->
      delta_trans q' q'' ->
      delta_trans q q''.
Hint Constructors delta_trans.

Ltac dt_step g :=
  eapply dt_next; 
  [ exists g; eexists; eexists; split; [reflexivity | congruence] |].


Theorem Step_star_Pre_trans :
  forall q t a,
    (Pre q) t a ->
    forall q'',
      delta_trans q q'' ->
      exists n t'',
        Step_star q t n q'' t''
        /\ (Pre q'') t'' a.
Proof.
  intros q t a P q'' DT.

  generalize t P. clear t P.
  induction DT; intros t P.
 
  exists 0. exists t. auto.

  rename H into DN1.

  destruct (Step_star_Pre_next q t a P q' DN1) as [n1 [t' [SS1 P']]].
  destruct DN1 as [g [g' [d [EQd NEQ]]]].

  edestruct IHDT as [n2 [t'' [SS2 P'']]].
  apply P'.

  exists (n1 + n2). exists t''.
  split. eapply Step_star_trans. apply SS1.
  apply SS2.
  auto.
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
  remember (tape_input GT ((build_list GT n Mark) ++ Add :: (build_list GT m Mark)))
    as t.
  assert (Pre ConsumeFirstNumber t (n, m)) as P.

  rewrite Heqt. simpl. unfold CFN_Tape. auto.

  edestruct 
    (Step_star_Pre_trans 
       ConsumeFirstNumber
       t
       (n, m)
       P
       HALT) as [steps [t'' [SS PRE]]].

  dt_step Add.
  dt_step Blank.
  dt_step Mark.
  dt_step Blank.
  apply dt_refl.

  exists steps.
  simpl in PRE.
  destruct t'' as [tb ta].
  unfold tape_input.
  destruct PRE; subst.
  apply SS.
Qed.

(* XXX *)

Lemma UnaryAddition_Time_1:  
  forall la lb nr,
    exists t',
      Step_star ConsumeFirstNumber 
                ((build_list GT lb Mark),
                 build_list GT la Mark ++ Add :: build_list GT nr Mark)
                (S la)
                ConsumeSecondNumber
                t'.
Proof.
  induction la as [|la]; intros lb nr; simpl in *.

  eexists. once. apply Step_star_refl.

  destruct (IHla (S lb) nr) as [t' SS].
  eexists. once. simpl in *. unfold bcons, b. simpl.
  rewrite blist_blaca; try congruence.
  apply SS.
Qed.

Lemma UnaryAddition_Time_2:  
  forall na nb,
    exists t',
      Step_star ConsumeSecondNumber 
                ((build_list GT nb Mark), build_list GT na Mark)
                (S na)
                OverrideLastMark
                t'.
Proof.
  induction na as [|na]; intros nb; simpl.

  eexists. once. apply Step_star_refl.

  destruct (IHna (S nb)) as [t' SS].
  eexists. once. unfold b. simpl. unfold bcons. simpl in *.
  rewrite blist_bl; try congruence.
  apply SS.
Qed.

Lemma UnaryAddition_Time_3:  
  forall nl nr,
    exists t',
      Step_star OverrideLastMark 
                ((build_list GT (nl + nr) Mark), (Mark :: nil))
                1
                SeekBeginning
                t'.
Proof.
  intros nl nr. eexists. once.
  apply Step_star_refl.
Qed.

Require Import Zerob.

Lemma UnaryAddition_Time_4a:
  forall l r,
    exists t',
      Step_star SeekBeginning 
                (build_list GT l Mark, build_list GT (S r) Mark)
                (S (S l))
                HALT
                t'.
Proof.
  induction l as [|l]; simpl; unfold bcons, b; simpl; intros r.

  eexists. once. once. apply Step_star_refl.

  destruct (IHl (S r)) as [t' SS].
  eexists. once. simpl. 
  unfold b.
  rewrite blist_bl; try congruence.
  unfold bcons. simpl. 
  apply SS.
Qed.

Lemma UnaryAddition_Time_4b:
  forall n,
    exists t',
      Step_star SeekBeginning 
                (nil, bcons GT GT_dec b Blank (build_list GT n Mark))
                1
                HALT
                t'.
Proof.
  destruct n as [|n]; simpl; unfold bcons, b; simpl.

  eexists. once. apply Step_star_refl.
  eexists. once. apply Step_star_refl.
Qed.

(* XXX This proof breaks because I can't differentiate the "first"
time the state changes from anywhere in the middle *)

Lemma UnaryAddition_Time:
  forall l r,
  exists t',
    Step_star ConsumeFirstNumber
              (tape_input GT ((build_list GT l Mark) ++ Add :: (build_list GT r Mark)))
              (2 * (l + r) + 3)
              HALT
              t'.
Proof.
  intros l r.

  remember (tape_input GT (build_list GT l Mark ++ Add :: build_list GT r Mark)) as t.
  destruct t as [tb ta].
  assert (Pre ConsumeFirstNumber (tb,ta) (l, r)) as P.

  simpl. exists 0. exists l. simpl in *. unfold tape_input in *.
  inversion Heqt. auto.
  unfold tape_input in *. inversion Heqt. subst. clear Heqt.

  edestruct (UnaryAddition_Time_1 l 0 r) as [[tb1 ta1] SS1].
  apply (Step_star_impl _ _ _ _ _ SS1) in P.

  remember P as P'. clear HeqP'.
  simpl in P'. destruct P' as [nb [na [EQb [EQa EQn]]]].
  subst.
  edestruct (UnaryAddition_Time_2 na nb) as [[tb2 ta2] SS2].
  apply (Step_star_impl _ _ _ _ _ SS2) in P.

  remember P as P'. clear HeqP'.
  simpl in P'. destruct P' as [EQb EQa].
  subst.
  edestruct (UnaryAddition_Time_3 l r) as [[tb3 ta3] SS3].
  apply (Step_star_impl _ _ _ _ _ SS3) in P.

  remember P as P'. clear HeqP'. clear P.
  simpl in P'. destruct P' as [[l3 [r3 [EQb [EQa [EQn3 LE]]]]] | [EQb EQa]];
  subst.

  destruct r3 as [|r3]. omega. clear LE.
  edestruct (UnaryAddition_Time_4a l3 r3) as [[tb4 ta4] SS4].
  exists (tb4, ta4).
  replace (2 * (l + r) + 3) with 
          ((S l) + ((S na) + (1 + (S (S l3))))).
  eapply Step_star_trans. apply SS1.
  eapply Step_star_trans. apply SS2.
  eapply Step_star_trans. apply SS3.
  apply SS4.

  clear SS1 SS2 SS3 SS4 tb4 ta4.
  rewrite EQn3 in EQn. clear EQn3.  
  
  Focus 2.
  edestruct (UnaryAddition_Time_4b (l + r)) as [[tb4 ta4] SS4].
  exists (tb4, ta4).
  replace (2 * (l + r) + 3) with 
          ((S l) + ((S na) + (1 + 1))).
  eapply Step_star_trans. apply SS1.
  eapply Step_star_trans. apply SS2.
  eapply Step_star_trans. apply SS3.
  apply SS4.

  clear SS1 SS2 SS3 SS4 tb4 ta4.  
Admitted.
