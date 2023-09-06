(* Proof by Induction *)

(** We can prove that [0] is a neutral
    element for [+] on the _left_
    using just [reflexivity]. *)

Example add_0_l : forall n : nat,
    0 + n = n.

Proof. reflexivity. Qed.

Theorem add_0_r_secondary : forall n : nat,
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


