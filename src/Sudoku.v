(*
 * A Simple Sudoku Solver in Coq
 *)

(* Lists and their notations *)
Require Import List.
Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

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
  [ [ "1", "2", "3" ],
    [ "4", "5", "6" ],
    [ "7", "8", "9" ] ].
Definition example_board_transpose : board :=
  [ [ "1", "4", "7" ],
    [ "2", "5", "8" ],
    [ "3", "6", "9" ] ].

(*
 * Operations on boards
 *)

(* Get the rows of a board -- identity since a board is a list of rows *)
Definition rows (b:board) : list row := b.

(* Check rows by example *)
Example test_rows_id : rows example_board = example_board.
Proof. reflexivity. Qed.

(* Used during extraction of columns of a board *)
Fixpoint build_cols (row : row) (partial_cols : list col) : list col :=
  match row, partial_cols with
    | x::tl, y::tl' => (x :: y) :: (build_cols tl tl')
    | _, _ => nil
  end.

(* Get the columns of a board *)
Fixpoint cols (b:board) : list col :=
  match b with
    | [] => []
    | [xs] => map (fun x : cellval => [x]) xs
    | xs :: xss => build_cols xs (cols xss)
  end.

(* Check cols by example *)
Example test_cols_transpose : cols example_board = example_board_transpose.
Proof. reflexivity. Qed.

Local Close Scope char_scope.

End Sudoku.