(* Proof by Induction *)

(** We can prove that [0] is a neutral
    element for [+] on the _left_
    using just [reflexivity]. *)

Example add_0_l : forall n : nat,
    0 + n = n.

Proof. reflexivity. Qed.

Theorem add_0_r_secondtry : forall n : nat,
    n + 0 = n.
Proof.
    intros n.
    destruct n as [| n'] eqn:E.
    - reflexivity.
    - simpl.
Abort.


(*induction*)

Theorem add_0_r : forall n : nat, n + 0 = n.
Proof.
    intros n.
    induction n as [| n' IHn']. (* induction tactic *)
    - reflexivity.
    - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem minus_n_n : forall n,
    n - n = 0.
Proof.
    intros n.
    induction n as [| n' IHn'].
    - reflexivity.
    - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_a_Sb: forall a b : nat,
    S (a + b) = a + S b.
Proof.
    intros a b.
    induction a as [| a' IHa'].
    - reflexivity.
    - simpl. rewrite IHa'. reflexivity.
Qed.

Theorem add_comm : forall a b : nat,
    a + b = b + a.
Proof.
    intros a b.
    induction a as [| a' IHa'].
    - simpl. rewrite add_0_r. reflexivity.
    - simpl. rewrite -> IHa'. rewrite -> plus_a_Sb. reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat,
    (n + 0 + 0) * m = n * m.
Proof.
    intros n m.
    assert (H: n + 0 + 0 = n).
        { Set Printing Parentheses. rewrite add_comm. simpl. rewrite add_comm. simpl. reflexivity. Unset Printing Parentheses. }
    rewrite H. reflexivity.
Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
    intros n m p q.
    assert (H:  n + m = m + n ).
    {rewrite add_comm. reflexivity. }
    rewrite H. reflexivity.
Qed.




