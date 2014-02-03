Require Import List.

Inductive Direction : Set :=
| L : Direction
| R : Direction.
Hint Constructors Direction.

Definition Tape (A:Type) : Type := ((list A) * (list A))%type.
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
  let t_after' := cons g t_after in
  match D with
      | L =>
        match t_before with
            | nil =>
              ( nil, cons b t_after' )
            | cons t_b t_bs =>
              ( t_bs, cons t_b t_after' )
        end
      | R =>
        match t_after' with
            | nil =>
              ( cons b t_before, nil )
            | cons t_a t_as =>
              ( cons t_a t_before, t_as )
        end
  end.

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

Module Type TM.
  Parameter QT : Type.
  Axiom QT_dec : forall (x y:QT), { x = y } + { x <> y }.
  Parameter Q : list QT. 
  Axiom Q_ne : Q <> nil.
  
  Parameter GT : Type.
  Axiom GT_dec : forall (x y:GT), { x = y } + { x <> y }.
  Parameter G : list GT.
  Axiom G_ne : G <> nil.

  Parameter b : GT.
  Axiom b_in_G : In b G.

  Parameter S : list GT.
  Axiom S_subset : incl S (remove GT_dec b G).
  
  Parameter q0 : QT.
  Axiom q0_mem : In q0 Q.

  Parameter F : list QT.
  Axiom F_subset : incl F Q.
  Definition Q_delta := (subtract QT QT_dec F Q).

  Parameter delta : QT -> GT -> option (QT * GT * Direction).
  Axiom delta_subset :
    forall q g q' g' d,
      delta q g = Some (q', g', d) ->
      ( In q Q_delta
        /\ In g G 
        /\ In q' Q
        /\ In g' G ).
End TM.

Module UnaryAddition : TM.
  Inductive QTi : Set :=
  | ConsumeFirstNumber : QTi
  | ConsumeSecondNumber : QTi
  | OverrideLastMark : QTi
  | SeekBeginning : QTi
  | HALT : QTi.
  Hint Constructors QTi.

  Definition QT := QTi.
  Hint Unfold QT.
  
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

  Inductive GTi : Set :=
  | Mark : GTi
  | Add : GTi
  | Blank : GTi.
  Hint Constructors GTi.
  
  Definition GT := GTi.
  Hint Unfold GT.

  Definition GT_dec : forall (x y:GT), { x = y } + { x <> y }.
  Proof. decide equality. Qed.

  Definition G := ( Mark :: Add :: Blank :: nil ).
  Lemma G_ne : G <> nil.
  Proof. intros F. inversion F. Qed.

  Definition b := Blank.
  Lemma b_in_G : In b G.
  Proof. simpl. auto. Qed.

  Definition S := ( Mark :: Add :: nil ).
  Lemma S_subset : incl S (remove GT_dec b G).
  Proof. 
    simpl. unfold b. unfold S.
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
      | (ConsumeFirstNumber, Mark) => Some (ConsumeFirstNumber, Mark, R)
      | (ConsumeFirstNumber, Add) => Some (ConsumeSecondNumber, Mark, R)
      | (ConsumeSecondNumber, Mark) => Some (ConsumeSecondNumber, Mark, R)
      | (ConsumeSecondNumber, Blank) => Some (OverrideLastMark, Blank, L)
      | (OverrideLastMark, Mark) => Some (SeekBeginning, Blank, L)
      | (SeekBeginning, Mark) => Some (SeekBeginning, Mark, L)
      | (SeekBeginning, Blank) => Some (HALT, Blank, R)
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
End UnaryAddition.

Module TM_R ( M : TM ).
  Import M.

  Inductive R : QT -> (Tape GT) -> QT -> (Tape GT) -> Prop :=
  | R_delta :
      forall q q' g' d t,
        delta q (tape_hd GT b t) = Some (q', g', d) ->
        R q t q' (tape_write GT b g' d t).
  Hint Constructors R.

  Theorem R_step :
    forall q t,
      { qt' | R q t (fst qt') (snd qt') } +
      { forall q' t',
          ~ R q t q' t' }.
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

  Lemma R_F_done :
    forall q t q' t',
      In q F ->
      ~ R q t q' t'.
  Proof.
    intros q t q' t' IN Rqt.
    inversion Rqt. subst.
    rename H into EQdel.
    apply delta_subset in EQdel.
    destruct EQdel as [INq EQdel].
    unfold Q_delta in *.
    eapply subtract_In. apply INq. auto.
  Qed.

  Inductive R_star : QT -> (Tape GT) -> QT -> (Tape GT) -> Prop :=
    | R_star_refl : 
        forall q t, 
          R_star q t q t
    | R_star_step :
        forall q t q' t' q'' t'',
          R q t q' t' ->
          R_star q' t' q'' t'' ->
          R_star q t q'' t''.
  Hint Constructors R_star.
End TM_R.

Module Type TM_Correctness ( M : TM ).
  Import M.
  Module M_R := TM_R ( M ).
  Import M_R.

  Parameter A : Type.
  Parameter Pre : QT -> (Tape GT) -> A -> Prop.

  Axiom R_Impl :
    forall q t q' t',
      R q t q' t' ->
      forall a,
        (Pre q)  t  a ->
        exists a',
          (Pre q') t' a'.
End TM_Correctness.

Module TM_Proof ( M : TM ) ( MC : TM_Correctness ( M ) ).
  Import M.
  Import MC.
  Import MC.M_R.
  
  Lemma R_star_impl:
    forall q t q'' t'',
      R_star q t q'' t'' ->
      forall a,
        (Pre q) t a ->
        exists a',
          (Pre q'') t'' a'.
  Proof.
    intros q t q'' t'' R_star_qt.
    induction R_star_qt.
    eauto.
    rename H into Rqt.
    intros a Pqt.
    eapply R_Impl in Rqt; [|apply Pqt].
    destruct Rqt as [a' Pq'].
    eauto.
  Qed.

  Theorem Correct :
    forall t,
      (exists a, (Pre q0) t a) ->
      forall qf,
        In qf F ->
        forall t',
          R_star q0 t qf t' ->
          exists a',
            (Pre qf) t' a'.
  Proof.
    intros t [a Pq0] qf INqf t' Rs_q0.
    eapply R_star_impl. apply Rs_q0.
    apply Pq0.
  Qed.
End TM_Proof.

Module UnaryAddition_Correctness : TM_Correctness ( UnaryAddition ).
  Import UnaryAddition.
  Module M_R := TM_R ( UnaryAddition ).
  Import M_R.

  Definition A := nat.

  Definition Pre (q:QT) (t:Tape GT) (a:A) := True.

  Theorem R_Impl :
    forall q t q' t',
      R q t q' t' ->
      forall a,
        (Pre q)  t  a ->
        exists a',
          (Pre q') t' a'.
  Proof.
    intros q t q' t' Rqt a Pqt.
    inversion Rqt. subst.
    rename H into EQdel.
    case q.

End UnaryAddition_Correctness.
