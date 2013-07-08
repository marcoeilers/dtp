(*
 *
 * A Simple Sudoku Solver in Coq using Vectors
 *
 *)

(* Vectors and their notation *)
Require Import Vector.
Import VectorNotations.
Open Scope vector_scope.

(* Define lists manually because they won't work with vectors in the same file *)
Inductive list (X:Type) : Type :=
  | nil :  list X
  | cons : X -> list X -> list X.
Implicit Arguments nil [[X]].
Implicit Arguments cons [[X]].

Module Sudoku.

(* Constants as in the regular version *)
Definition boxsize : nat := 3.
Definition boardsize : nat := 9.
Inductive cellval : Type :=
  One | Two | Three | Four | Five | Six | Seven | Eight | Nine | Blank.
Definition cellval_eq (a b : cellval) : bool :=
  match a, b with
    | One, One => true
    | Two, Two => true
    | Three, Three => true
    | Four, Four => true
    | Five, Five => true
    | Six, Six => true
    | Seven, Seven => true
    | Eight, Eight => true
    | Nine, Nine => true
    | Blank, Blank => true
    | _, _ => false
  end.
Definition cellvals : Vector.t cellval boardsize := 
  One :: Two :: Three :: Four :: Five :: Six :: Seven :: Eight :: Nine :: [].
Definition blank (a:cellval) : bool :=
  match a with | Blank => true | _ => false end.

(* Board definition with specific length vectors *)
Definition col := Vector.t cellval boardsize.
Definition row := Vector.t cellval boardsize.
Definition board := Vector.t row boardsize.

(* Example board and its transpose *)
Definition example_board : board :=
  (One ::  Two:: Three:: Four:: Five:: Six:: Seven:: Eight:: Nine :: []) ::
  (One:: Two:: Three:: Four:: Five:: Six:: Seven:: Eight:: Nine :: [])::
  (One:: Two:: Three:: Four:: Five:: Six:: Seven:: Eight:: Nine :: [])::
  (One:: Two:: Three:: Four:: Five:: Six:: Seven:: Eight:: Nine :: [])::
  (One:: Two:: Three:: Four:: Five:: Six:: Seven:: Eight:: Nine :: [])::
  (One:: Two:: Three:: Four:: Five:: Six:: Seven:: Eight:: Nine :: [])::
  (One:: Two:: Three:: Four:: Five:: Six:: Seven:: Eight:: Nine :: [])::
  (One:: Two:: Three:: Four:: Five:: Six:: Seven:: Eight:: Nine :: [])::
  (One:: Two:: Three:: Four:: Five:: Six:: Seven:: Eight:: Nine :: []):: [].
Definition example_board_transpose : board :=
  (One :: One :: One :: One :: One :: One :: One :: One :: One :: []) ::
  (Two :: Two :: Two :: Two :: Two :: Two :: Two :: Two :: Two :: []) ::
  (Three :: Three :: Three :: Three :: Three :: Three :: Three :: Three :: Three :: []) ::
  (Four :: Four :: Four :: Four :: Four :: Four :: Four :: Four :: Four ::  []) ::
  (Five :: Five :: Five :: Five :: Five :: Five :: Five :: Five :: Five :: []) ::
  (Six :: Six :: Six :: Six :: Six :: Six :: Six :: Six :: Six :: []) ::
  (Seven :: Seven :: Seven :: Seven :: Seven :: Seven :: Seven :: Seven :: Seven :: []) ::
  (Eight :: Eight :: Eight :: Eight :: Eight :: Eight :: Eight :: Eight :: Eight :: []) ::
  (Nine :: Nine :: Nine :: Nine :: Nine :: Nine :: Nine :: Nine :: Nine :: []) :: [].

(*
 * Operations on boards
 *)

(* Get the rows of a board -- identity since a board is a list of rows *)
Definition rows {A:Type} {n : nat } {m : nat} (b:Vector.t (Vector.t A m) n) : Vector.t (Vector.t A m) n := b.

(* Check rows by example *)
Example test_rows_id_1 : rows example_board = example_board.
Proof. reflexivity. Qed.
Example test_rows_id_2 : rows (rows example_board) = example_board.
Proof. reflexivity. Qed.

(* Combine two vectors of the same length using some function *)
Definition zipWith (A B C : Type) (n : nat) (l1 : Vector.t A n) (l2 : Vector.t B n) (f: A -> B -> C) : Vector.t C n :=
  Vector.rect2 (fun n _ _ => Vector.t C n) (Vector.nil C) (fun _ _ _ H a b => (f a b) :: H) l1 l2.

(* Specific version that prepends the i-th element of the first vector
   to the i-th vector in the second vector *)
Fixpoint combine_prepend {A:Type} {n m : nat} (l:Vector.t A n) (l': Vector.t (Vector.t A m) n) : Vector.t (Vector.t A (S m)) n :=
  zipWith A (Vector.t A m) (Vector.t A (S m)) n l l' (fun x xs => x::xs).

(* Get the columns of a board *)
Fixpoint cols {A:Type} {n m : nat} (l: Vector.t (Vector.t A m) n) : Vector.t (Vector.t A n) m :=
  match l with
    | Vector.nil => Vector.const [] m
    | xs :: xss => combine_prepend xs (cols xss)
  end.

(* Check cols by example *)
Example test_cols_transpose : cols example_board = example_board_transpose.
Proof. reflexivity. Qed. 
Example test_cold_id : cols (cols example_board) = example_board.
Proof. reflexivity. Qed. 

Theorem cols_id : forall (b : board), 
  cols (cols b) = b.
Proof.
  intros b.
  unfold board in b.
    unfold row in b.
    simpl in b.
    induction b.
    reflexivity.
    induction h.
    symmetry.
    rewrite <- IHb.
    (* stuck *)
Admitted.

(* member for vectors *)
Fixpoint member  {n : nat} (v : cellval) (vs : Vector.t cellval n) : bool :=
  match vs with
  | Vector.nil => false
  | x :: xs => if cellval_eq v x then true else member v xs
  end.

(* some functions on custom lists because we have not imported them *)
Fixpoint lapp {A : Type} (l1 l2 : list A) : list A :=
  match l1 with
  | nil => l2
  | (cons x xs) => (cons x (lapp xs l2))
  end.

Fixpoint lconcat {A : Type} (l : list (list A)) : list A :=
  match l with
  | nil => nil
  | cons x xs => lapp x (lconcat xs)
  end.

Fixpoint lmap {A B: Type} (f : A -> B) (l : list A) : list B :=
  match l with
  | nil => nil
  | cons x xs => cons (f x) (lmap f xs)
  end.

Fixpoint lfilter {A : Type} (f : A -> bool) (l : list A) : list A :=
  match l with
  | nil => nil
  | cons x xs => if (f x) then (cons x (lfilter f xs)) else (lfilter f xs)
  end.

(* List Cartesian product for vectors *)
Fixpoint cp {A : Type} {n : nat} (v : Vector.t (list A) n) : list (Vector.t A n) :=
  match v with 
  | [] => cons (Vector.nil A) nil
  | xs :: xss => lconcat (lmap (fun x => lmap (fun ys => x :: ys) (cp xss)) xs)
  end.

(* Matrix Cartesian product for vectors *)
Definition mcp {A : Type} {n m : nat} (cs : Vector.t (Vector.t (list A) m) n) : list (Vector.t (Vector.t A m) n) :=
  cp (Vector.map cp cs).

(* all for vectors *)
Fixpoint allVec {A : Type} {n : nat} (f : A -> bool) (v : Vector.t A n) : bool :=
  match v with
  | [] => true
  | x :: xs => if (f x) then (allVec f xs) else false
  end.

(* We need to prove this for the bigger proof (from the paper) *)
Theorem help : forall (A : Type) (n : nat) (p : A -> bool) (b : Vector.t (list A) n),
  lfilter (fun x => allVec p x) (cp b) = cp (Vector.map (fun x => lfilter p x) b).
Proof with simpl.
  intros.
  induction b.
    simpl. reflexivity.
    simpl.
    (* stuck *)
Admitted.