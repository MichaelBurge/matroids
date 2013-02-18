Require Export Coq.Sets.Ensembles.
Require Export Coq.Sets.Finite_sets.
Require Export Coq.Sets.Powerset.

Section Matroids.
  Parameter U : Type.
  Parameter E : Ensemble U.      
  (* A1: E is a finite set over universe U *)
  Parameter finite : Finite U E.

  (* I1: The empty set is independent *)
  Definition I1 : Ensemble (Ensemble U) -> Prop :=
    fun I => I (Empty_set U).
    (* I2: Subsets of independent sets are independent *)
  Definition I2 : Ensemble (Ensemble U) -> Prop :=
      (fun I =>
         forall (A B : (Ensemble U)),
           I B /\ (Included U A B) -> I A).
  (* I3: If |A| < |B|, A can be extended to a larger independent set by adding an element from B *)
  Definition I3 : Ensemble (Ensemble U) -> Prop :=
    (fun I =>
       forall (A B : (Ensemble U)),
       forall (m n : nat),
         (cardinal U A m ) /\
         (cardinal U B n) /\
         m < n ->
           exists x : U, B x /\ I (Add U A x)).
  
  Record Matroid : Type := {
    I : Ensemble (Ensemble U);
    M_I1 : I1 I;
    M_I2 : I2 I;
    M_I3 : I3 I
}.

  Definition Circuits : Matroid -> Ensemble (Ensemble U) :=
    (fun M : Matroid =>
       (fun S : Ensemble U =>
          (~ I M S) /\
          (forall T : Ensemble U,
             Strict_Included U T S -> I M T))).

  (* C1: The empty set is not a circuit *)
  Definition C1 : Ensemble (Ensemble U) -> Prop :=
    (fun C => ~ C (Empty_set U)).
  (* C2: No distinct circuits are subsets *)
  Definition C2 : Ensemble (Ensemble U) -> Prop :=
    (fun C => 
       forall (A B : Ensemble U),
         (C A) /\
         (C B) /\
         Included U A B ->
           Same_set U A B).
  (* C3: Merging distinct circuits and removing a common element gives a superset of a circuit *)
  Definition C3 : Ensemble (Ensemble U) -> Prop :=
    (fun C =>
       forall (A B : Ensemble U),
       forall (e : U),
         (C A) /\
         (C B) /\
         (~ Same_set U A B) /\
         (In U (Intersection U A B) e) ->
         exists O : Ensemble U,
           Included U O (Setminus U (Union U A B) (Singleton U e))).

  Record Matroid_Circuit : Type := {
    C : Ensemble (Ensemble U);
    M_C1 : C1 C;
    M_C2 : C2 C;
    M_C3 : C3 C
}.

