Require Export Coq.Sets.Ensembles.
Require Export Coq.Sets.Finite_sets.
Require Export Coq.Sets.Powerset.
Record Matroid : Type := {
  U : Type;
  E : Ensemble U;
  I : Ensemble (Ensemble U);
  (* A1: E is a finite set over universe U *)
  finite : Finite U E;
  (* I1: The empty set is independent *)
  I1 : I (Empty_set U);
  (* I2: Subsets of independent sets are independent *)
  I2 : forall (A B : (Ensemble U)),
         I B /\ (Included U A B) -> I A;
  (* I3: If |A| < |B|, A can be extended to a larger independent set by adding an element from B *)
  I3 : forall (A B : (Ensemble U)),
       forall (m n : nat),
         (cardinal U A m ) /\
         (cardinal U B n) /\
         m < n ->
           exists x : U, B x /\ I (Add U A x)
}.
