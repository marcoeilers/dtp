(*
 *
 * A Simple Sudoku Solver in Coq
 *
 *)

(* Some basic definitions and functions on booleans, nats and lists *)
(* Require Export Misc. *)




(* Require Import CpdtTactics. *)


Require Import Vector.
Import VectorNotations.



Notation "[]" := [] : vector_scope.
Notation "h :: t" := (h :: t) (at level 60, right associativity)
  : vector_scope.
Notation " [ x ] " := (x :: []) : vector_scope.
Notation " [ x , .. , y ] " := (cons _ x _ .. (cons _ y _ (nil _)) ..) : vector_scope
.

Open Scope vector_scope.


Module Sudoku.

(* Constants *)
Definition boxsize : nat := 3.
Definition boardsize : nat := boxsize * boxsize.

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
Check Vector.cons.
Check Vector.nil.
Definition test : Vector.t cellval 1 :=  One :: [].
Definition cellvals : Vector.t cellval boardsize := 
  One :: Two :: Three :: Four :: Five :: Six :: Seven :: Eight :: Nine :: [].

Definition blank (a:cellval) : bool :=
  match a with | Blank => true | _ => false end.

(* Board definition *)
Check Vector.t.

Definition col := Vector.t cellval boardsize.
Definition row := Vector.t cellval boardsize.
Definition board := Vector.t row boardsize.



(* Example board and its transpose *)
Definition example_board : board :=
   ( One ::  Two:: Three:: Four:: Five:: Six:: Seven:: Eight:: Nine :: []) ::
    ( One:: Two:: Three:: Four:: Five:: Six:: Seven:: Eight:: Nine :: [])::
    ( One:: Two:: Three:: Four:: Five:: Six:: Seven:: Eight:: Nine :: [])::
    ( One:: Two:: Three:: Four:: Five:: Six:: Seven:: Eight:: Nine :: [])::
    ( One:: Two:: Three:: Four:: Five:: Six:: Seven:: Eight:: Nine :: [])::
    ( One:: Two:: Three:: Four:: Five:: Six:: Seven:: Eight:: Nine :: [])::
    ( One:: Two:: Three:: Four:: Five:: Six:: Seven:: Eight:: Nine :: [])::
    ( One:: Two:: Three:: Four:: Five:: Six:: Seven:: Eight:: Nine :: [])::
    ( One:: Two:: Three:: Four:: Five:: Six:: Seven:: Eight:: Nine :: [])::  [].

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

Definition zipWith (A B C : Type) (n : nat) (l1 : Vector.t A n) (l2 : Vector.t B n) (f: A -> B -> C) : Vector.t C n :=
  Vector.rect2 (fun n _ _ => Vector.t C n) (Vector.nil C) (fun _ _ _ H a b => (f a b) :: H) l1 l2.


Fixpoint combine_prepend {A:Type} {n m : nat} (l:Vector.t A n) (l': Vector.t (Vector.t A m) n) : Vector.t (Vector.t A (S m)) n :=
  zipWith A (Vector.t A m) (Vector.t A (S m)) n l l' (fun x xs => x::xs).
   

(* Get the columns of a board *)
Fixpoint cols {A:Type} {n m : nat} (l: Vector.t (Vector.t A m) n) : Vector.t (Vector.t A n) m :=
  match l with
    | Vector.nil => Vector.const [] m
 (*   | xs :: [] => Vector.map (fun x:A => x :: []) xs *)
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
Admitted.

(*
Definition group {A:Type} (l:list A) := group_by boxsize l.


Definition boxes {A:Type} (b:list (list A)) : list (list A) :=
  map ungroup (ungroup (map cols (group (map group b)))).


Example test_boxes_id : boxes (boxes example_board) = example_board.
Proof. reflexivity. Qed.

*)

