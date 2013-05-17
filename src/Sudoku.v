(*
 * A Simple Sudoku Solver in Coq
 *)

(* Some useful functions on nats etc. *)
Require Export Basics.

(* Lists and their notations *)
Require Import List.
Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

(* Groups a list into chunks of size n *)
Fixpoint group_by {A:Type} (n:nat) (l:list A) : list (list A) :=
  match l with
    | [] => []
    | x :: xs => match group_by n xs with
      | [] => [[x]]
      | y :: ys => if beq_nat (length y) n then [x] :: (y :: ys) else (x :: y) :: ys
    end
  end.

(* Merges a list of lists into a single list *)
Fixpoint ungroup {A:Type} (l:list (list A)) : list A :=
  match l with
    | [] => []
    | xs :: xss => xs ++ ungroup xss
  end.

(* Combines two lists by prepending the elements of one list
   to each sublist of the other list *)
Fixpoint combine_prepend {A:Type} (l : list A) (l' : list (list A)) : list (list A) :=
  match l, l' with
    | x::xs, y::ys => (x :: y) :: (combine_prepend xs ys)
    | _, _ => nil
  end.

(* Ascii characters for cell values *)
Require Import Ascii.

Module Sudoku.

(* To be able to use ascii characters like "3", "." etc. *)
Local Open Scope char_scope.

(* Constants *)
Definition boardsize : nat := 9.
Definition boxsize : nat := 3.
Definition cellval := ascii.
Definition cellvals : list cellval :=
  [ "1", "2", "3", "4", "5", "6", "7", "8", "9" ].
Definition blank (a:cellval) : bool :=
  match a with | "." => true | _ => false end.

(* Board definition *)
Definition col := list cellval.
Definition row := list cellval.
Definition board := list row.

(* Example board and its transpose *)
Definition example_board : board :=
  [ [ "1", "2", "3", "4", "5", "6", "7", "8", "9" ],
    [ "1", "2", "3", "4", "5", "6", "7", "8", "9" ],
    [ "1", "2", "3", "4", "5", "6", "7", "8", "9" ],
    [ "1", "2", "3", "4", "5", "6", "7", "8", "9" ],
    [ "1", "2", "3", "4", "5", "6", "7", "8", "9" ],
    [ "1", "2", "3", "4", "5", "6", "7", "8", "9" ],
    [ "1", "2", "3", "4", "5", "6", "7", "8", "9" ],
    [ "1", "2", "3", "4", "5", "6", "7", "8", "9" ],
    [ "1", "2", "3", "4", "5", "6", "7", "8", "9" ] ].
Definition example_board_transpose : board :=
  [ [ "1", "1", "1", "1", "1", "1", "1", "1", "1" ],
    [ "2", "2", "2", "2", "2", "2", "2", "2", "2" ],
    [ "3", "3", "3", "3", "3", "3", "3", "3", "3" ],
    [ "4", "4", "4", "4", "4", "4", "4", "4", "4" ],
    [ "5", "5", "5", "5", "5", "5", "5", "5", "5" ],
    [ "6", "6", "6", "6", "6", "6", "6", "6", "6" ],
    [ "7", "7", "7", "7", "7", "7", "7", "7", "7" ],
    [ "8", "8", "8", "8", "8", "8", "8", "8", "8" ],
    [ "9", "9", "9", "9", "9", "9", "9", "9", "9" ] ].

(*
 * Operations on boards
 *)

(* Get the rows of a board -- identity since a board is a list of rows *)
Definition rows (b:board) : list row := b.

(* Check rows by example *)
Example test_rows_id_1 : rows example_board = example_board.
Proof. reflexivity. Qed.
Example test_rows_id_2 : rows (rows example_board) = example_board.
Proof. reflexivity. Qed.

(* Get the columns of a board *)
Fixpoint cols {A:Type} (l:list (list A)) : list (list A) :=
  match l with
    | [] => []
    | [xs] => map (fun x : A => [x]) xs
    | xs :: xss => combine_prepend xs (cols xss)
  end.

(* Check cols by example *)
Example test_cols_transpose : cols example_board = example_board_transpose.
Proof. reflexivity. Qed.
Example test_cold_id : cols (cols example_board) = example_board.
Proof. reflexivity. Qed.

(* Used for the extraction of boxes from a board *)
Fixpoint group {A:Type} (l:list A) := group_by boxsize l.

(* Get the boxes of a board *)
Fixpoint boxes (b:board) : (list (list cellval)) :=
  map ungroup (ungroup (map cols (group (map group b)))).

(* Check boxes identity *)
Example test_boxes_id : boxes (boxes example_board) = example_board.
Proof. reflexivity. Qed.

Local Close Scope char_scope.

End Sudoku.