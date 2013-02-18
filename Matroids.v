Require Export Coq.Sets.Ensembles.
Require Export Coq.Sets.Finite_sets.
Require Export Coq.Sets.Powerset.

Section Matroids.
  Parameter U : Type.
  Parameter E : Ensemble U.      
  (* A1: E is a finite set over universe U *)
  Parameter finite : Finite U E.

  Record Matroid : Type := {
    I : Ensemble (Ensemble U);
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

Definition Circuits : Matroid -> Ensemble (Ensemble U) :=
  (fun M : Matroid =>
     (fun S : Ensemble U =>
       (~ I M S) /\
       (forall T : Ensemble U,
         Strict_Included U T S -> I M T))).



  Record Matroid_Circuit : Type := {
    C : Ensemble (Ensemble U);
    (* C1: The empty set is not a circuit *)
    C1 : ~ C (Empty_set U);
    (* C2: No distinct circuits are subsets *)
    C2 : forall (A B : Ensemble U),
           (C A) /\
           (C B) /\
           Included U A B ->
             Same_set U A B;
    (* C3: Merging distinct circuits and removing a common element gives a superset of a circuit *)
    C3 : forall (A B : Ensemble U),
         forall (e : U),
           (~ Same_set U A B) /\
           (In U (Intersection U A B) e) ->
             exists O : Ensemble U,
               Included U O (Setminus U (Union U A B) (Singleton U e))
             
    
}.

