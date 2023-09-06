Inductive natprod : Type :=
    | pair (n1 n2 : nat).

Check (pair 3 5) : natprod.

Definition fst (p : natprod) : nat := 
    match p with
    | pair x _ => x
    end.

Definition snd (p : natprod) : nat := 
    match p with
    | pair _ y => y 
    end.
    
Compute (fst (pair 3 5)). (*returns 3*)

Notation "( x , y )" := (pair x y).

Compute (fst (3,5)). (*also returns 3*)

Definition fst2 (p : natprod) : nat := 
    match p with
    | (x,_) => x
    end.

Definition snd2 (p : natprod) : nat := 
    match p with
    | (_,y) => y
    end.

Compute (fst2 (3,5)).

Definition swap_pair (p: natprod) : natprod :=
    match p with
    | (x,y) => (y,x)
    end.

Compute (swap_pair (3,5)). (*returns (5,3)*)

Theorem surjective_pairing' : forall (n m : nat),
    (n,m) = (fst (n,m), snd (n,m)).
Proof.
    simpl.
    reflexivity.
Qed.

Theorem surjective_pairing_stuck : forall (p : natprod),
    p = (fst p, snd p).
Proof.
    intros p. 
    destruct p as [n m].
    simpl.
    reflexivity.
Qed.

