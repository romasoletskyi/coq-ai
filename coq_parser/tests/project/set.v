(*  A compilation of:
        Coq.Sets.Ensembles
        Coq.Relations.Relation_Definitions
        https://github.com/coq-community/topology *)

(*  Ensemble of type U is something which answers whether
    x : U is in it by giving a Prop *)
Section Ensembles.
    Variable U : Type.
    Definition Ensemble := U -> Prop.
    
    Definition In (A : Ensemble) (x: U) := A x.

    (* singleton example *)
    Inductive singleton (x : U) : Ensemble :=
        element: In (singleton x) x.

    Inductive all : Ensemble := 
        elements (x : U) : In all x.

    Lemma all_contains : forall x, In all x.
    Proof.
        apply elements.
    Qed.

    Lemma singleton_contains : forall (x : U), In (singleton x) x.
    Proof.
        intro x. apply element.
    Qed.

End Ensembles.

Check In.
Arguments In {U}.

Section Relations.
    Variable A : Type.
    Definition relation := A -> A -> Prop.
    Variable R : relation.

    (* Record is just a tuple of elements *)
    Record order : Prop := makeOrder {
        ord_refl : forall (x : A), R x x;
        ord_trans : forall (x y z : A), R x y -> R y z -> R x z;
        ord_antisymm : forall (x y : A), R x y -> R y x -> x = y;
    }.
End Relations.

Check order.
Arguments order {A}.

Inductive le : nat -> nat -> Prop :=
    | le_n (n : nat) : le n n
    | le_S (n m : nat) : le n m -> le n (S m).

Lemma le_trans : forall m n o, le m n -> le n o -> le m o.
Proof.
    intros m n o F G. induction G.
    - apply F. 
    - apply le_S. apply IHG. apply F.
Qed.

Lemma n_le_m__Sn_le_Sm : forall n m,
    le n m -> le (S n) (S m).
Proof.
    intros n m H. induction H.
    - apply le_n.
    - apply le_S. apply IHle.
Qed. 
  
Lemma Sn_le_Sm__n_le_m : forall n m,
    le (S n) (S m) -> le n m.
Proof.
    intros n m H. inversion H.
    - apply le_n.
    - apply (le_trans n (S n) m).
      + apply le_S. apply le_n.
      + apply H2.
Qed. 

Definition nat_order : order le.
apply makeOrder.
- apply le_n. 
- intros x y z H G. induction G.
  + apply H.
  + apply le_S. apply IHG. apply H.
- intro x. induction x; intros.
  + destruct y. 
    * reflexivity.
    * inversion H0.
  + destruct y.
    * inversion H.
    Admitted.

Section ZL.
    Variable T : Type.
    Variable R : relation T.
    Hypothesis ord : order R.

    (* we add several simple notations *)
    Notation "x ≤ y" := (R x y) (at level 70).  
    Notation "x ∈ s" := (In s x) (at level 75).  

    (* chain is a totally ordered subset *)
    Definition chain (s : Ensemble T) : Prop := 
        forall (x y : T), x ∈ s -> y ∈ s -> (x ≤ y \/ y ≤ x).

    (* maximal element is an element which is not smaller than any other one *)
    Definition maximal (x : T) : Prop :=
        forall (y : T), x ≤ y -> x = y.

    (* every chain has an upper bound *)
    Hypothesis upper_bound : forall (s : Ensemble T), chain s ->
        exists x : T, forall y : T, y ∈ s -> y ≤ x.
    
    Theorem zorns_lemma : exists x : T, maximal x.
        Admitted.
End ZL.
    