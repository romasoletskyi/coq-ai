Lemma plus_n_Sm : forall n m : nat,
  n + (S m) = S (n + m).
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed. 

Theorem plus_n_0 : forall n : nat,
  n + 0 = n.
Proof.
  intro n. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.  
  intros n m. induction n as [|n' IHn'].
  - rewrite plus_n_0. reflexivity.
  - rewrite plus_n_Sm. rewrite <- IHn'. reflexivity.
Qed.
