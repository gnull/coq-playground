Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

Class Setoid (A : Type) (equi : relation A) :=
  { setoid_eqiuvalence :> Equivalence equi }.

Generalizable All Variables.

Class Group `(Setoid A rel) (dot : A -> A -> A) (e : A) (inv : A -> A) :=
  { dot_assoc : forall x y z, rel (dot x (dot y z))
                                  (dot (dot x y) z)
  ; one_left : forall x, rel (dot e x) x
  ; inverse_left : forall x, rel (dot (inv x) x) e
}.

Require Import Bool Arith ZArith.
Require Import Ring.

(** The Z/nZ Setoid, that is the setoid of (mod n)-equivalence classes over Z.

  This is the way I define a finite setoid.
*)
Instance ZnZ (n : Z) : Setoid Z (fun x y => exists a, (x + a * n)%Z = y).
Proof.
  split. split.
  - unfold Reflexive. intros x.
    exists 0%Z. omega.
  - unfold Symmetric. intros x y H. destruct H as [a H].
    exists (0 - a)%Z. simpl. symmetry.
    rewrite <- Zopp_mult_distr_l. omega.
  - unfold Transitive. intros x y z H H'.
    destruct H as [a H]. destruct H' as [a' H'].
    exists (a + a')%Z. ring_simplify. omega.
Qed.

(** Any set is a Setoid over equality *)
Instance eq_setoid (A : Type) : Setoid A eq.
Proof.
  split. apply eq_equivalence.
Qed.

Definition setoid_homomorphism `(B  : Setoid A  rel )
                               `(B' : Setoid A' rel') (f : A -> A') : Prop
  := forall x y, (rel x y) <-> (rel' (f x) (f y)).

Definition finite_setoid `(B : Setoid A rel) : Prop
  := exists n f, setoid_homomorphism B (ZnZ n) f.

Theorem bool_finite : finite_setoid (eq_setoid bool).
Proof.
  unfold finite_setoid. exists 2%Z.
  remember (fun x : bool => if x then 1%Z else 0%Z) as f.
  exists f. rewrite Heqf. clear Heqf. clear f.
  split.
  - intros H. rewrite H. exists 0%Z. omega.
  - intros [a H]. destruct x; destruct y; simpl; auto; omega.
Qed.

(* TODO: Probably, I will need the excluded middle here. *)
Theorem nat_infinite : ~ finite_setoid (eq_setoid nat).
Proof.
  intros H. destruct H as [n [f H]].
  unfold setoid_homomorphism in H. Abort.








