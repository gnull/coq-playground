Require Coq.Vectors.Fin.
Require Coq.Logic.FunctionalExtensionality.

(* (number of veriables) (bdd size) *)
Inductive bdd : nat -> nat -> Type :=
| bdd_nil : forall n, bdd n 2
| bdd_cons : forall n m, Fin.t n -> Fin.t m -> Fin.t m -> bdd n m -> bdd n (S m).

Fixpoint fin_relax {n} (f : Fin.t n) : Fin.t (S n):=
match f with
| Fin.F1 => Fin.F1
| Fin.FS x => Fin.FS (fin_relax x)
end.

Definition bdd_eval {n m : nat} (skip : Fin.t m) (b : bdd n m) (e : Fin.t n -> bool) : bool.
induction b as [| n m x l r b].
- destruct skip. { exact true. } { exact false. }
- induction skip.
  + apply IHb.
    * destruct (e x). { exact l. } { exact r. }
    * exact e.
  + exact IHskip.
Defined.

Example bdd_true_sink : bdd_eval Fin.F1 (bdd_nil 0) (fun x => false) = true.
Proof. reflexivity. Qed.

Example bdd_false_sink : bdd_eval (Fin.FS Fin.F1) (bdd_nil 0) (fun x => false) = false.
Proof. reflexivity. Qed.

Example bdd_single_true : bdd_eval Fin.F1 (bdd_cons 1 2 Fin.F1 Fin.F1 (Fin.FS Fin.F1) (bdd_nil 1)) (fun x => false) = false.
Proof. reflexivity. Qed.

Example bdd_single_false : bdd_eval Fin.F1 (bdd_cons 1 2 Fin.F1 (Fin.FS Fin.F1) Fin.F1 (bdd_nil 1)) (fun x => false) = true.
Proof. reflexivity. Qed.

(* Boolean Predicate *)
Definition bool_pred (n : nat) : Type := (Fin.t n -> bool) -> bool.

(* Boolean Predicate resolved/computed by an OBDD *)
Definition bdd_pred {n m : nat} (b : bdd n (S m)) : bool_pred n :=
  fun e => bdd_eval Fin.F1 b e.
