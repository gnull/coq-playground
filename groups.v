Require Export Coq.Logic.FunctionalExtensionality.

Axiom tertium_non_datur : forall (P : Prop), P \/ ~P.

Lemma FunctionUniq : forall {X : Type} (f : X -> X) (x x' : X),
  x = x' -> f x = f x'.
Proof.
  intros.
  rewrite H.
  apply equal_f.
  reflexivity.
Qed.

Theorem ex_falso_quodlibet : forall (P : Prop), False -> P.
Proof.
  intros.
  inversion H.
Qed.

Class Group (X : Type) (f : X -> X -> X) := {
  e : X;
  Assoc : forall (a b c : X), f a (f b c) = f (f a b) c;
  Inver : forall x e, exists x', f x' x = e;
  Ident : forall (x : X), f e x = x;
}.

Lemma group_injective_l : forall {X} {f} (g : Group X f) y x x',
  f y x = f y x' -> x = x'.
Proof.
  intros.
  destruct g eqn:G. clear G.
  destruct (tertium_non_datur (x = x')) as [T | T].
  - apply T.
  - apply ex_falso_quodlibet.
    apply T. destruct (Inver0 y e) as [y']. pose proof H0. apply Ident0 in H0.
    apply (FunctionUniq (f y')) in H.
    rewrite Assoc in H. rewrite H0 in H.
    rewrite Assoc in H. rewrite H0 in H.
    rewrite H2 in H. rewrite H2 in H.
    apply H.
Qed.

Lemma group_id_r : forall {X} {f} (g : Group X f), exists e, forall x, f x e = x.
Proof.
  intros.
  destruct g eqn:G.
  destruct Ident0 as [e].
  exists e.
  intros.
  destruct (Inver0 x e) as [x'].
  apply (group_injective_l g x').
  rewrite Assoc.
  rewrite H. rewrite e0. reflexivity.
  apply e0.
Qed.

Lemma group_inv_r : forall {X} {f} (g : Group X f) x e, exists x',
  (forall y, f e y = y) -> f x x' = e.
Proof.
  intros.
  pose proof g.
  destruct g.
  destruct (Inver x e) as [x'].
  exists x'.
  intros.
Admitted.

Lemma group_id_equal : forall {X} {f} (g : Group X f) e e',
  (forall x, f x e = x) -> (forall x, f e' x = x) -> e = e'.
Proof.
  intros.
  rewrite <- (H0 e).
  rewrite <- (H e').
  rewrite H. rewrite H.
  reflexivity.
Qed.

Lemma group_inv_equal : forall {X} {f} (g : Group X f) x x' x'' e,
  (forall y, f e y = y) -> f x x' = e -> f x'' x = e -> x' = x''.
Proof.
  intros.
  pose proof g.
  destruct H2.
  apply (group_injective_l g x).
  rewrite H0.
  apply (group_injective_l g x'').
  rewrite Assoc0. rewrite H1.
  rewrite H.
  destruct (group_id_r g) as [e'].
  assert (e' = e). { apply (group_id_equal g). apply H2. apply H. }
  rewrite <- H3. apply H2.
Qed.

Definition flip {X : Type} (f : X -> X -> X) (a : X) (b : X) : X :=
  f b a.

Theorem group_flip : forall {X} {f}, Group X f -> Group X (flip f).
Proof.
  intros.
  pose proof H.
  destruct H.
  split.
  - unfold flip. symmetry. apply Assoc0.
  - unfold flip. intros.
    destruct(Inver0 x e) as [x'].
    exists x'. intros. destruct Ident0 as [e'].
    assert (e = e'). { rewrite <- (H2 e). rewrite H1. reflexivity. }
    rewrite <- H3 in H2. clear H3. clear e'.
    pose proof H2.
    apply H in H2.
    destruct (group_inv_r H0 x e) as [x''].
    pose proof H3. apply H4 in H3.
    assert (x' = x''). { apply (group_inv_equal H0 x e).  }

intros. unfold flip. destruct Ident0 as [x'].
    exists x'. intros. 

Lemma group_injective_r : forall {X} {f} (g : Group X f) y x x',
  f y x = f y x' -> x = x'.
Proof.
  intros.
  assert (Group X (flip f)).
  - 

Section myGroup.

Variable X : Type.
Variable f : X -> X -> X.
Variable e : X.

Definition Group : Prop :=
     (forall (x y z: X), f z (f x y) = f (f z x) y)   (* Associativity        *)
  /\ (forall (x : X), f e x = x)                      (* Identity             *)
  /\ (forall (x : X), exists (x' : X), f x' x = e).   (* Existence of inverse *)

Lemma GroupInjectiveL : Group -> forall (y x x' : X), f y x = f y x' -> x = x'.
Proof.
  intros [Assc [Ident Inv]].
  intros.
  destruct (tertium_non_datur (x = x')).
  - apply H0.
  - apply ex_falso_quodlibet.
    apply H0. destruct (Inv y) as [y'].
    apply (FunctionUniq (f y')) in H.
    rewrite -> Assc in H.
    rewrite -> Assc in H.
    rewrite H1 in H.
    rewrite Ident in H.
    rewrite Ident in H.
    apply H.
Qed.

Lemma ExistsIdR : Group ->
  forall (x : X), f x e = x.
Proof.
  intros [Assc [Ident Inv]] x.
  destruct (Inv x) as [x'].
  apply (GroupInjectiveL (Assc /\ Ident /\ Inv) x').
  rewrite Assc. rewrite H.
  apply (Ident e).
Qed.

Lemma ExistsInverseR : Group ->
  forall (x : X), exists (x' : X), f x x' = e.
Proof.
  unfold Group.
  intros.
  decompose record H.
  destruct (H3 x).
  exists x0.
  apply (GroupInjectiveL H x0).
  rewrite H0. rewrite H1. rewrite H2.

  destruct (H3 x0).
  apply (GroupInjectiveL H x1).
  rewrite H0. rewrite H2.
  rewrite H0.
  reflexivity.
Qed.


End myGroup.

Definition Group {X : Type} (f : X -> X -> X) : Prop :=
     forall (x y z: X), f z (f x y) = f (f z x) y   (* Associativity *)
  /\ forall (x y: X), exists (x' : X), f x' x = y.  (* Existence of solutions *)

(* Miscellaneous group lemmas *)

(* Lemma InjectiveL {X : Type} (f : X -> X -> X) :
  Group f -> 
*)

Lemma ExistsNeutralL {X : Type} (f : X -> X -> X)

Lemma ExistsNeutralR {X : Type} (f : X -> X -> X) :
  Group f -> exists (e : X), forall (x : X), f x e = x.
Proof.
  intros.
  destruct H.
  destruct H0.
  unfold ExistsNeutralL in H0.
  destruct H0 as [e]. exists e.
  intros.
  assert (forall (x : X), f x e = f e x).
  { intros y. unfold Assoc in H.
    unfold ExistsInverseL in H1.
    destruct (H1 y e) as [y'].
  }
  rewrite <- (H0 x).