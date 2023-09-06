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

(* ######################################## *)
(** * Lists of numbers *)
Inductive natlist : Type :=
    | nil
    | cons (n : nat) (l : natlist).

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
                        (at level 60, right associativity).

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist2 := 1 :: (2 :: (3 :: nil)).
Definition mylist3 := 1 :: 2 :: 3 :: [].
Definition mylist4 := [1;2;3].


Fixpoint repeat (n count : nat) : natlist :=
    match count with
    | 0 => nil
    | S count' => n :: (repeat n count')
    end.

Compute repeat 3 5.

Fixpoint length (lst : natlist) : nat :=
    match lst with
    | [] => 0
    | h :: t => S (length t)
    end.

Compute length (repeat 3 5).

Fixpoint app (l1 l2 : natlist) : natlist :=
    match l1 with
    | [] => l2
    | h :: t => h :: (app t l2)
    end.

Compute app [3;4;5] [6;7;8]. (*return [3;4;5;6;7;8]*)
Compute app [3] [4;5;6]. (*returns [3;4;5;6]*)

Notation "x ++ y" := (app x y)
                    (right associativity, at level 60).

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. simpl. reflexivity. Qed.

Example test_app2: [] ++ [4;5] = [4;5].
Proof. simpl. reflexivity. Qed.

Example test_app3: [1;2;3] ++ [] = [1;2;3].
Proof. simpl. reflexivity. Qed.

Definition hd (default : nat) (l : natlist) : nat :=
    match l with
    | [] => default
    | h :: t => h
    end.

Compute hd 4 [].






