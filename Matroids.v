Require Export Coq.Logic.Classical.
Require Export Coq.Sets.Constructive_sets.
Require Export Coq.Sets.Ensembles.
Require Export Coq.Sets.Finite_sets.
Require Export Coq.Sets.Powerset.
Require Export Coq.Setoids.Setoid.
Section Matroids.
  Parameter U : Type.
  Parameter E : Ensemble U.      
  (* A1: E is a finite set over universe U *)
  Parameter finite : Finite U E.

  (* I1: The empty set is independent *)
  Definition I1 (I : Ensemble (Ensemble U)) :=
    I (Empty_set U).
    (* I2: Subsets of independent sets are independent *)
  Definition I2 (I : Ensemble (Ensemble U)) :=
    forall (A B : (Ensemble U)),
      I B /\ (Included U A B) -> I A.
  (* I3: If |A| < |B|, A can be extended to a larger independent set by adding an element from B *)
  Definition I3 (I : Ensemble (Ensemble U)) := 
    forall (A B : (Ensemble U)),
    forall (m n : nat),
      (cardinal U A m ) /\
      (cardinal U B n) /\
      m < n ->
        exists x : U, B x /\ I (Add U A x).
  
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
         exists C3 : Ensemble U,
           (C C3) /\
           Included U C3 (Setminus U (Union U A B) (Singleton U e))).
  Lemma Circuits_Satisfy_C1 : forall M : Matroid, C1 (Circuits M).
  Proof.
    unfold C1.
    intros.
    intro.
    unfold Circuits in H.
    destruct H.
    contradict H.
    apply M_I1.
  Qed.
  Lemma Circuits_Satisfy_C2 : forall M : Matroid, C2 (Circuits M).
  Proof.
    unfold C2.
    intros.
    destruct H as [A_circ [B_circ A_sub_B]].
    assert (G: A = B \/ A <> B). apply classic.
    destruct G.
    apply (Extension U); assumption.
    unfold Circuits in A_circ.
    unfold Circuits in B_circ.
    unfold Strict_Included in A_circ.
    unfold Strict_Included in B_circ.
    destruct A_circ as [A_not_I A_prop_subs_I].
    destruct B_circ as [B_not_I B_prop_subs_I].
    assert (G: Included U A B /\ A <> B -> I M A).
    apply B_prop_subs_I.
    contradict A_not_I.
    auto.
  Qed.
  Lemma Sets_Included_In_Themselves :
    forall A : Ensemble U,
      Included U A A.
  Proof.
    intros.
    assert (A = A). tauto.
    apply Extension in H.
    unfold Same_set in H.
    destruct H.
    assumption.
  Qed.
  Lemma Circuits_Satisfy_C3 : forall M : Matroid, C3 (Circuits M).
  Proof.
    unfold C3.
    intros.
    (* target should contain a circuit *)
    set (target := Setminus U (Union U A B) (Singleton U e)).
    destruct H as [A_circ [B_circ [A_neq_B e_in_intersect]]].
    apply NNPP.
    intro.
    
    assert (G: forall C3 : Ensemble U,
                 ~(Circuits M C3 /\
                   Included U C3 target)).
    apply not_ex_all_not. apply H. clear H.
    assert (I M target).
    assert (H: ~ (Circuits M target /\ Included U target target)).
    apply G.
    apply not_and_or in H.
    assert (Included U target target).
    split H.
    
    unfold Included.
    
    assert (H: forall C3 : Ensemble U,
                 (~ Circuits M C3) \/
                 (Included U C3 (Setminus U (Union U A B) (Singleton U e)))).
    intro. apply not_or_and.
    destruct (G A).
    split.
    assumption.

    contradict A_neq_B.
    
    let g := (exists (O : Ensemble U),
               (Circuits M O) /\
               (Included U O (Setminus U (Union U A B) (Singleton U e))))
    in assert (G: g \/ ~g). apply classic.

    contradict.
   Theorem Circuits_Satisfy_C_Axioms : forall M : Matroid,
    let cs := Circuits M
    in (C1 cs /\ C2 cs /\ C3 cs).

  Proof.
    intro.
    intro.
    split.
    (* C2 *)
    split.
    unfold C2.
    intros.
    destruct H.
    destruct H0.
    unfold Same_set.
    split.
    assumption.
    assert 
  Qed.
  Record Matroid_Circuit : Type := {
    C : Ensemble (Ensemble U);
    M_C1 : C1 C;
    M_C2 : C2 C;
    M_C3 : C3 C
}.

