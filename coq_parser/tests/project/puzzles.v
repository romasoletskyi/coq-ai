Require Import List.
Require Import Lia.
Import ListNotations.

Section OtelloPuzzle.
(*You are in a completely dark room. I dump a bag of 1017 Othello chips on the floor. 
These chips are black on one side and white on the other. 
You can feel around for the chips, but you cannot see which side is up because it is dark. 
I tell you that exactly 23 have the black side up. 
I ask you to divide the chips into two piles (every chip must be in one [and only one] of the piles) 
such that the two piles have the same number of chips with the black side up 
(they may have different numbers of chips with the white side up). How do you do it? *)

(* Define a chip as having two sides, White and Black. *)
Inductive side := White | Black.

(* A chip's state is represented by which side is currently facing up. *)
Definition chip := side.

(* A pile is simply a list of chips. *)
Definition pile := list chip.

(* A function to count the number of chips with the black side up in a pile. *)
Fixpoint count_black (p: pile) : nat :=
  match p with
  | [] => 0
  | Black :: t => S (count_black t)
  | White :: t => count_black t
  end.

(* A function to flip a chip. *)
Definition flip_chip (c: chip) : chip :=
  match c with
  | White => Black
  | Black => White
  end.

(* A function to flip all chips in a pile. *)
Definition flip_pile (p: pile) : pile :=
  map flip_chip p.

(* A predicate to check if two piles have the same number of black-up chips. *)
Definition same_black_up (p1 p2: pile) : Prop :=
  count_black p1 = count_black p2.

(* Now, we need to prove that for any given pile `p` with a total of 1017 chips and 
   exactly 23 black side up, there exists a division into two piles `p1` and `p2` such
   that flipping one pile results in the two piles having the same number of black chips facing up. *)
   
(* We'll need to prove this helper theorem first:
   For any pile `p`, flipping it will result in the number of black chips being equal
   to the total number of chips minus the number of black chips that were originally facing up. *)   

(* This lemma proves that in any pile of chips, 
the count of black chips is always less than or equal to the total count of chips. *)
Lemma count_not_larger (p : pile) : count_black p <= length p.
Proof.
  induction p as [|c p' IHp'].
  - apply le_n.
  - destruct c; simpl; [apply le_S | apply le_n_S]; apply IHp'.
Qed.

(* This lemma asserts that subtracting zero from any number returns the number itself, 
which is a basic arithmetic fact. *)
Lemma sub_n_0 : forall n : nat, n - 0 = n.
Proof.
  intro n. induction n as [|n' IHn']; reflexivity.
Qed.

(* The following lemma is crucial for the next proof; 
it relates the subtraction of successors in the context of natural numbers. *)
Lemma sub_n_Sm : forall n m : nat, S m <= n -> S (n - S m) = n - m.
Proof.
  intro n. induction n as [|n' IHn']; intros m H.
  - inversion H.
  - simpl. destruct m as [|m'].
    + rewrite sub_n_0. reflexivity.
    + apply IHn'. apply le_S_n. apply H.
Qed.

(* The main theorem uses the above lemmas to prove that flipping a pile of chips 
results in an inverse count of black chips to the original. *)
Theorem flip_pile_black_count (p: pile) : count_black (flip_pile p) = length p - count_black p.
Proof.
  induction p as [|c p' IHp'].
  - reflexivity.
  - destruct c; simpl; rewrite IHp'.
    + destruct (count_black p') eqn:E.
      * rewrite sub_n_0. reflexivity.
      * apply sub_n_Sm. rewrite <- E. apply count_not_larger.
    + reflexivity.
Qed.

(* `firstn_app_skipn` ensures that any list `p` can be reconstructed by 
concatenating the first `n` elements of `p` with the remaining elements of `p` 
after skipping the first `n`. *)
Lemma firstn_app_skipn: forall (n: nat) (p: pile), p = (firstn n p) ++ (skipn n p).
Proof.
  intros n. induction n as [|n' IHn']; intros p.
  - reflexivity.
  - simpl. destruct p.
    + reflexivity.
    + rewrite <- app_comm_cons. rewrite <- IHn'. reflexivity.
Qed. 

(* `count_black_division` proves that the count of black chips 
in the concatenation of two piles is the sum of the counts of black chips in each pile separately. *)
Lemma count_black_division: forall (p1 p2: pile), 
  count_black (p1 ++ p2) = count_black p1 + count_black p2.
Proof.
  intros p1 p2. induction p1.
  - reflexivity.
  - simpl; rewrite IHp1; destruct a; simpl; reflexivity.
Qed.

(* `equal_black_after_division` is the main theorem that solves the puzzle by showing 
there is a way to divide a given pile into two with an equal count of black-up chips. 
It builds on the previous lemmas to establish the division strategy and prove its correctness. *)
Theorem equal_black_after_division: forall p: pile, length p = 1017 -> count_black p = 23 ->
  let p1 := firstn 23 p in
  let p2 := skipn 23 p in
  same_black_up (flip_pile p1) p2.
Proof.
  intros p Hlen Hblack.
  unfold same_black_up.
  rewrite flip_pile_black_count with (p:=firstn 23 p).
  remember (firstn 23 p) as p1.
  assert (Hlen_p1: length p1 = 23). 
  { subst p1; rewrite firstn_length. rewrite Hlen. reflexivity. }
  assert (Hlen_p2: length (skipn 23 p) = 994).
  { rewrite skipn_length; lia. }
  assert (H: count_black p1 + count_black (skipn 23 p) = length p1).
  { rewrite Heqp1 at 1. rewrite Hlen_p1. rewrite <- Hblack at 3.
    rewrite (firstn_app_skipn 23 p) at 3. symmetry. apply count_black_division. }
  lia.
Qed.

End OtelloPuzzle.

Section SocksProblem.
(*Twenty-four red socks and 24 blue socks are lying in
a drawer in a dark room. What is the minimum number of
socks I must take out of the drawer which will guarantee
that I have at least two socks of the same color?*)

(* We define a simple enumeration to represent sock colors. *)
Inductive sock_color : Type :=
  | red : sock_color
  | blue : sock_color.

Definition sock_color_eq_dec (x y : sock_color) : {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

(* We can now state the problem as a theorem. *)
(* The theorem states that if we take three socks from a drawer that contains only red and blue socks,
   then we are guaranteed to have at least two socks of the same color. *)

Theorem guarantee_same_color_pair: forall (drawer: list sock_color),
  length drawer >= 3 -> exists s1 s2: sock_color, 
    s1 = s2 /\ In s1 drawer /\ In s2 drawer.
Proof.
  intros drawer H. 
  destruct drawer as [| color1 rest].
  - simpl in H. inversion H. (* Case of empty list, contradicting the hypothesis *)
  - destruct rest as [| color2 rest].
    + simpl in H. inversion H.  inversion H1. (* Case of only one sock, contradicting the hypothesis *)
    + destruct rest as [| color3 rest].
      * simpl in H. inversion H. inversion H1. inversion H3. (* Case of only two socks, contradicting the hypothesis *)
      * destruct (sock_color_eq_dec color1 color2).
        -- exists color1, color2. simpl. auto.
        -- destruct (sock_color_eq_dec color1 color3).
           ++ exists color1, color3. simpl. auto.
           ++ exists color2, color3. split.
           { destruct color2; destruct color3; destruct color1; try contradiction; reflexivity. }
           { simpl. auto. }
Qed.

End SocksProblem.
