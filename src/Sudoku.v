(*
 *
 * A Simple Sudoku Solver in Coq
 *
 *)

(* Some basic definitions and functions on booleans, nats and lists *)
Require Export Misc.

(* List is not exported from Misc *)
Require Import List.

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
Definition blankval := ".".
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

(* A solvable board *)
Definition solvable_board : board :=
  [ [ "2", ".", ".", ".", ".", "1", ".", "3", "8"],
    [ ".", ".", ".", ".", ".", ".", ".", ".", "5"],
    [ ".", "7", ".", ".", ".", "6", ".", ".", "."],
    [ ".", ".", ".", ".", ".", ".", ".", "1", "3"],
    [ ".", "9", "8", "1", ".", ".", "2", "5", "7"],
    [ "3", "1", ".", ".", ".", ".", "8", ".", "."],
    [ "9", ".", ".", "8", ".", ".", ".", "2", "."],
    [ ".", "5", ".", ".", "6", "9", "7", "8", "4"],
    [ "4", ".", ".", "2", "5", ".", ".", ".", "."] ].

(* All characters defined *)
Local Close Scope char_scope.

(*
 * Operations on boards
 *)

(* Get the rows of a board -- identity since a board is a list of rows *)
Definition rows {A:Type} (b:list (list A)) : list (list A) := b.

(* Check rows by example *)
Example test_rows_id_1 : rows example_board = example_board.
Proof. reflexivity. Qed.
Example test_rows_id_2 : rows (rows example_board) = example_board.
Proof. reflexivity. Qed.

(* Get the columns of a board *)
Fixpoint cols {A:Type} (l:list (list A)) : list (list A) :=
  match l with
    | [] => []
    | [xs] => map (fun x:A => [x]) xs
    | xs :: xss => combine_prepend xs (cols xss)
  end.

(* Check cols by example *)
Example test_cols_transpose : cols example_board = example_board_transpose.
Proof. reflexivity. Qed.
Example test_cold_id : cols (cols example_board) = example_board.
Proof. reflexivity. Qed.

(* Used for the extraction of boxes from a board *)
Definition group {A:Type} (l:list A) := group_by boxsize l.

(* Get the boxes of a board *)
Definition boxes {A:Type} (b:list (list A)) : list (list A) :=
  map ungroup (ungroup (map cols (group (map group b)))).

(* Check boxes identity *)
Example test_boxes_id : boxes (boxes example_board) = example_board.
Proof. reflexivity. Qed.

(*
 * The actual solver
 *)

(* Equality interface for ascii characters *)
Definition Interface_eq x y := if ascii_dec x y then true else false.

(* True if a is a member of l *)
Fixpoint member (a:cellval) (l:list cellval) : bool :=
  match l with
    | [] => false
    | x :: xs => if Interface_eq x a then true else member a xs
  end.

(* A matrix of choices, basically a board with a list of possible values
   for each cell *)
Definition matrix_choices := list (list (list cellval)).

(* For a blank cell gives all possible cellvals, otherwise gives the cell *)
Definition choose (c:cellval) : list cellval :=
  if blank c then cellvals else [c].

(* Generates (possibly invalid) choices for a board *)
Definition choices (b:board) : matrix_choices :=
  map (map choose) b.

(* Gives the cell values that are already certain (i.e. they are the only choice) *)
Definition fixed (l:list (list cellval)) : list cellval :=
  ungroup (filter single l).

(* Removes a list of fixed entries from the list of choices, used below
   fs : fixed entries, cs : choices *)
Definition delete (fs:list cellval) (cs:list cellval) : list cellval :=
  filter (fun x:cellval => negb (member x fs)) cs.
  
(* Removes a list of fixed entries from the list of choices, used below
   fs : fixed entries, cs : choices *)
Definition remove (fs:list cellval) (cs:list cellval) : list cellval :=
  if single cs then cs else delete fs cs.

(* Removes fixed entries from the list of choices *)
Definition reduce (l:list (list cellval)) : list (list cellval) :=
  map (remove (fixed l)) l.

(* Removes fixed entries from matrix choices given a selector function *)
Definition prune_by (f:matrix_choices -> matrix_choices) :
  matrix_choices -> matrix_choices :=
  fun cs:matrix_choices => f (map reduce (f cs)).

(* Removes fixed entries from matrix choices *)
Definition prune (choices:matrix_choices) : matrix_choices :=
  prune_by boxes (prune_by cols (prune_by rows choices)).

(* True if any cell has an empty list of choices *)
Definition void (cm:matrix_choices) : bool :=
  any (any null) cm.

(* True if there are no duplicates in l *)
Fixpoint nodups (l:list cellval) : bool :=
  match l with
    | [] => true
    | x :: xs => if member x xs then false else nodups xs
  end.

(* True if there are no duplicates in the matrix of choices *)
Definition safe (cm:matrix_choices) : bool :=
  andb3
    (all (fun xs:list (list cellval) => nodups (fixed xs)) (rows cm))
    (all (fun xs:list (list cellval) => nodups (fixed xs)) (cols cm))
    (all (fun xs:list (list cellval) => nodups (fixed xs)) (boxes cm)).

(* True if the matrix of choices contains an empty cell or duplicates *)
Definition blocked (cm:matrix_choices) : bool :=
  orb (void cm) (negb (safe cm)).

(* Returns the minimum number of choices for all cells that have
   more than one choice  *)
Definition minchoice (cm:matrix_choices) : nat :=
  minimum (filter (fun n:nat => blt_nat 1 n) (ungroup (map (map list_size) cm))).

(* True if the length of cs is equal to m *)
Definition best {A:Type} (m:nat) (cs:list A) : bool :=
  beq_nat m (list_size cs).

(* Generates all possible choices for a cell with a minimal number of choices *)
Definition expand (cm:matrix_choices) : list matrix_choices :=
  let n := minchoice cm in
  let (rows1, rows2') := (break (fun y => any (fun x => best n x) y) cm) in
  match rows2' with
    | nil => nil (* should never happen *)
    | row::rows2 => 
        let (row1, row2') := break (fun x => best n x ) row in
        match row2' with
          | nil => nil (* should never happen *)
          | cs::row2 => map (fun c => rows1 ++ [row1 ++ [c]::row2] ++ rows2) cs
        end
  end.

(* Prunes a list of matrix choices until every cell has only one value
   or the matrix of choices is invalid *)
Fixpoint search (n: nat) (cm:matrix_choices) : list matrix_choices :=
  match n with
    | 0 => [] (* should never happen *)
    | S n' =>
      if blocked cm then []
      else if all (all single) cm then [cm]
      else ungroup (map (fun x:matrix_choices => search n' (prune x)) (expand cm))
  end.

(* Solves a Sudoku *)
Definition sudoku (b:board) : list board :=
  map (map (map (hd blankval))) (search 1000 (prune (choices b))).

Eval compute in sudoku solvable_board.

End Sudoku.

(*
  - recursion?
    - well founded proof by hand
    - co-inductive types *
    - predicates, call graphs
    - axioms
  - should never happen sections
    - program fixpoint with bangs ! for branches that never happen
    - Xmonad, refine and pass around proof arguments
  - what to prove
    - sound and complete, if there is a solution then the naive/optimized one will find it
    - validness of solutions
    - prune never throws away good solutions
    - implement brute force approach, reason about that and draw analogies
*)