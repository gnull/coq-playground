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

