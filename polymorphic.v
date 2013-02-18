Parameters A B C : Set.

Definition curry (f : A * B -> C) := fun a => fun b => f (a, b).
Definition uncurry (g : A -> B -> C) := fun p => g (fst p) (snd p).

Theorem better : forall f a b, uncurry (curry f) (a, b) = f (a, b).
Theorem converse : forall f a b, curry (uncurry f) a b = f a b.
Proof.
  intros.
  unfold curry, uncurry.
  simpl.
  reflexivity.
Qed.
Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H.
  inversion H as [|n'].
  inversion H1 as [|n''].
  assumption.
Qed.

 
Fixpoint true_upto_n__true_everywhere 
(* FILL IN HERE *)

Example true_upto_n_example :
    (true_upto_n__true_everywhere 3 (fun n => even n))
  = (even 3 -> even 2 -> even 1 -> forall m : nat, even m).
Proof. reflexivity.  Qed.
