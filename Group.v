Section Group.
  Variable G : Set.
  Variable op : G -> G -> G.
  Variable e : G.
  Notation "x * y" := (op x y).
  (* Axioms for the Group *)
  Definition Identity (g : G) := forall x:G, x * g = x /\ g * x = x.
  Axiom G1: Identity e.
  Axiom G2: forall x y z:G, (x * y) * z = x * (y * z).
  Axiom G3: forall x:G, exists y:G, x * y = e.
  Theorem IdentityUniqueness : forall (x : G) (y : G), (Identity x /\ Identity y) -> (x = y).
    Proof.
      intros.
      destruct H.
      assert (x = x * y).
      unfold Identity in H0.
      destruct (H0 x).
      symmetry.
      assumption.
      assert (x * y = y).
      unfold Identity in H.
      destruct (H y).
      assumption.
      transitivity (x * y).
      assumption.
      assumption.
  Qed.
Print IdentityUniqueness.
End Group