(*
 * Some basic functions and definitions
 *)

(* Booleans *)

(* True if all arguments are true *)
Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1, b2, b3 with
    | true, true, true => true
    | _, _, _ => false
  end.

(* Natural Numbers *)

(* True if n is equal to m *)
Fixpoint beq_nat (n m : nat) : bool :=
  match n with
    | O => match m with
             | O => true
             | S m' => false
           end
    | S n' => match m with
                | O => false
                | S m' => beq_nat n' m'
              end
  end.

(* True if n is less than or equal to m *)
Fixpoint ble_nat (n m : nat) : bool :=
  match n with
    | O => true
    | S n' =>
        match m with
          | O => false
          | S m' => ble_nat n' m'
        end
  end.

(* True if n is less than m *)
Definition blt_nat (n m : nat) : bool :=
  match ble_nat n m with
    | false => false
    | true => negb (ble_nat m n)
  end.

(*
 * Lists, their notations and some useful functions on them
 *)

Require Import List.
Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

(* Determines if all elements of the list satisfy the predicate *)
Fixpoint all {A:Type} (f:A -> bool) (l:list A) : bool :=
  match l with
    | [] => true
    | x :: xs => if f x then all f xs else false
  end.

(* Determines if any element of the list satisfies the predicate *)
Fixpoint any {A:Type} (f:A -> bool) (l:list A) : bool :=
  match l with
    | [] => false
    | x :: xs => if f x then true else any f xs
  end.

(* Splits a list before the first element that fulfills the test  *)
Fixpoint break {A:Type} (f: A -> bool) (l:list A) : (list A * list A) :=
  match l with
    | nil => (nil, nil)
    | x::xs => if f x then (nil, l) 
               else let (a, b) := (break f xs) in (x::a, b)
  end.

(* Combines two lists by prepending the elements of one list
   to each sublist of the other list *)
Fixpoint combine_prepend {A:Type} (l:list A) (l':list (list A)) : list (list A) :=
  match l, l' with
    | x::xs, y::ys => (x :: y) :: (combine_prepend xs ys)
    | _, _ => nil
  end.

(* As per http://coq.inria.fr/V8.1/stdlib/Coq.Lists.List.html *)
Fixpoint filter {A:Type} (f:A -> bool) (l:list A) : list A := 
  match l with 
    | nil => nil
    | x :: l => if f x then x::(filter f l) else filter f l
  end.

(* Groups a list into chunks of size n *)
Fixpoint group_by {A:Type} (n:nat) (l:list A) : list (list A) :=
  match l with
    | [] => []
    | x :: xs => match group_by n xs with
      | [] => [[x]]
      | y :: ys =>
        if beq_nat (length y) n then [x] :: (y :: ys)
        else (x :: y) :: ys
    end
  end.

(* Returns the length of the list *)
Fixpoint list_size {A:Type} (l:list A) : nat :=
  match l with
    | nil => 0
    | x::xs => S (list_size xs)
  end.

(* Returns the minimum of the list and 0 for the empty list *)
Fixpoint minimum (l:list nat) : nat :=
  match l with
    | [] => 0
    | [x] => x
    | x::xs => let m := minimum xs in if blt_nat m x then m else x
  end.

(* Test whether a list is empty *)
Definition null {A:Type} (l:list A) : bool :=
  match l with
    | [] => true
    | _ => false
  end.

(* True if the list only contains one element *)
Definition single {A:Type} (l:list A) : bool :=
  match l with
    | [x] => true
    | _ => false
  end.

(* Merges a list of lists into a single list *)
Fixpoint ungroup {A:Type} (l:list (list A)) : list A :=
  match l with
    | [] => []
    | xs :: xss => xs ++ ungroup xss
  end.