(*
 *
 * A Simple Sudoku Solver in Coq
 *
 *)

(* Some basic definitions and functions on booleans, nats and lists *)
Require Export Misc.

(* List is not exported from Misc *)
Require Import List.

Module Sudoku.

(* Constants *)
Definition boardsize : nat := 9.
Definition boxsize : nat := 3.
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
Definition cellvals : list cellval :=
  [ One, Two, Three, Four, Five, Six, Seven, Eight, Nine ].
Definition blank (a:cellval) : bool :=
  match a with | Blank => true | _ => false end.

(* Board definition *)
Definition col := list cellval.
Definition row := list cellval.
Definition board := list row.

(* Example board and its transpose *)
Definition example_board : board :=
  [ [ One, Two, Three, Four, Five, Six, Seven, Eight, Nine ],
    [ One, Two, Three, Four, Five, Six, Seven, Eight, Nine ],
    [ One, Two, Three, Four, Five, Six, Seven, Eight, Nine ],
    [ One, Two, Three, Four, Five, Six, Seven, Eight, Nine ],
    [ One, Two, Three, Four, Five, Six, Seven, Eight, Nine ],
    [ One, Two, Three, Four, Five, Six, Seven, Eight, Nine ],
    [ One, Two, Three, Four, Five, Six, Seven, Eight, Nine ],
    [ One, Two, Three, Four, Five, Six, Seven, Eight, Nine ],
    [ One, Two, Three, Four, Five, Six, Seven, Eight, Nine ] ].
Definition example_board_transpose : board :=
  [ [ One, One, One, One, One, One, One, One, One ],
    [ Two, Two, Two, Two, Two, Two, Two, Two, Two ],
    [ Three, Three, Three, Three, Three, Three, Three, Three, Three ],
    [ Four, Four, Four, Four, Four, Four, Four, Four, Four ],
    [ Five, Five, Five, Five, Five, Five, Five, Five, Five ],
    [ Six, Six, Six, Six, Six, Six, Six, Six, Six ],
    [ Seven, Seven, Seven, Seven, Seven, Seven, Seven, Seven, Seven ],
    [ Eight, Eight, Eight, Eight, Eight, Eight, Eight, Eight, Eight ],
    [ Nine, Nine, Nine, Nine, Nine, Nine, Nine, Nine, Nine ] ].

(* A solvable board as well as its almost solved and completely solved variants *)
Definition solvable_board : board :=
  [ [ Two, Blank, Blank, Blank, Blank, One, Blank, Three, Eight],
    [ Blank, Blank, Blank, Blank, Blank, Blank, Blank, Blank, Five],
    [ Blank, Seven, Blank, Blank, Blank, Six, Blank, Blank, Blank],
    [ Blank, Blank, Blank, Blank, Blank, Blank, Blank, One, Three],
    [ Blank, Nine, Eight, One, Blank, Blank, Two, Five, Seven],
    [ Three, One, Blank, Blank, Blank, Blank, Eight, Blank, Blank],
    [ Nine, Blank, Blank, Eight, Blank, Blank, Blank, Two, Blank],
    [ Blank, Five, Blank, Blank, Six, Nine, Seven, Eight, Four],
    [ Four, Blank, Blank, Two, Five, Blank, Blank, Blank, Blank] ].
Definition almost_solved_board : board := 
  [ [ Two, Four, Nine, Five, Seven, One, Six, Three, Eight ],
    [ Eight, Blank, One, Four, Three, Two, Nine, Seven, Five ],
    [ Five, Seven, Blank, Nine, Eight, Six, One, Four, Two ],
    [ Seven, Two, Five, Blank, Nine, Eight, Four, One, Three ],
    [ Six, Nine, Eight, One, Blank, Three, Two, Five, Seven ],
    [ Three, One, Four, Seven, Two, Five, Eight, Six, Nine ],
    [ Nine, Three, Seven, Eight, One, Four, Five, Two, Six ],
    [ One, Five, Two, Three, Six, Nine, Seven, Eight, Four ],
    [ Four, Eight, Six, Two, Five, Seven, Three, Nine, One ] ].
Definition solved_board : board :=
  [ [ Two, Four, Nine, Five, Seven, One, Six, Three, Eight ],
    [ Eight, Six, One, Four, Three, Two, Nine, Seven, Five ],
    [ Five, Seven, Three, Nine, Eight, Six, One, Four, Two ],
    [ Seven, Two, Five, Six, Nine, Eight, Four, One, Three ],
    [ Six, Nine, Eight, One, Four, Three, Two, Five, Seven ],
    [ Three, One, Four, Seven, Two, Five, Eight, Six, Nine ],
    [ Nine, Three, Seven, Eight, One, Four, Five, Two, Six ],
    [ One, Five, Two, Three, Six, Nine, Seven, Eight, Four ],
    [ Four, Eight, Six, Two, Five, Seven, Three, Nine, One ] ].

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
 * Naive Sudoku Implementation
 *)

(* A matrix of choices, basically a board with a list of possible values
   for each cell *)
Definition matrix_choices := list (list (list cellval)).

(* For a blank cell gives all possible cellvals, otherwise gives the cell *)
Definition choose (c:cellval) : list cellval :=
  if blank c then cellvals else [c].

(* Generates (possibly invalid) choices for a board *)
Definition choices (b:board) : matrix_choices :=
  map (map choose) b.

(* True if a is a member of l *)
Fixpoint member (a:cellval) (l:list cellval) : bool :=
  match l with
    | [] => false
    | x :: xs => if cellval_eq x a then true else member a xs
  end.

(* True if there are no duplicates in l *)
Fixpoint nodups (l:list cellval) : bool :=
  match l with
    | [] => true
    | x :: xs => if member x xs then false else nodups xs
  end.

(* True if the board is correctly solved *)
Definition correct (b:board) : bool :=
  andb3 (all nodups (rows b)) (all nodups (cols b)) (all nodups (boxes b)).

Definition sudoku_naive (b:board) : list board :=
  filter correct (mcp (choices b)).

(* The following gives a Segmentation Fault:
   Eval compute in sudoku_naive solvable_board.
 *)
Eval compute in sudoku_naive almost_solved_board.

(*
 * Not so naive but still very naive Sudoku Implementation
 *)

(* Removes a list of fixed entries from the list of choices, used below
   fs : fixed entries, cs : choices *)
Definition delete (fs:list cellval) (cs:list cellval) : list cellval :=
  filter (fun x:cellval => negb (member x fs)) cs.
  
(* Removes a list of fixed entries from the list of choices, used below
   fs : fixed entries, cs : choices *)
Definition remove (fs:list cellval) (cs:list cellval) : list cellval :=
  if single cs then cs else delete fs cs.

(* Gives the cell values that are already certain (i.e. they are the only choice) *)
Definition fixed (l:list (list cellval)) : list cellval :=
  ungroup (filter single l).

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

Definition sudoku_naive_2 (b:board) : list board :=
  filter correct (mcp (prune (choices b))).

(* The following gives a Segmentation Fault:
   Eval compute in sudoku_naive solvable_board.
 *)
Eval compute in sudoku_naive_2 almost_solved_board.

(*
 * The actual solver
 *)

(* True if any cell has an empty list of choices *)
Definition void (cm:matrix_choices) : bool :=
  any (any null) cm.

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
  map (map (map (hd Blank))) (search 1000 (prune (choices b))).

Eval compute in sudoku solvable_board.

(* Alternative approach to search *)
Require Import Program.

(* Counts the choices in a matrix*)
Program Definition count_choices (cm : matrix_choices) : nat :=
  fold_left
    (fun sum x : nat => if ble_nat x 1 then sum else sum + x)
    (ungroup (map (map list_size) cm))
    0.

(* Search based on the reduction of matrix choices *)
Program Fixpoint search' (cm:matrix_choices) {measure (count_choices cm)} :
  list matrix_choices :=
  if dec (blocked cm) then []
  else if dec (all (all single) cm) then [cm]
  else ungroup (map (fun x:matrix_choices => search' (prune x)) (expand cm)).

  Next Obligation.
    (* Relation between cm and x is totally missing *)
  Admitted.

Definition sudoku' (b:board) : list board :=
  map (map (map (hd Blank))) (search' (prune (choices b))).

Eval compute in sudoku' solvable_board.

(*
 * Reasoning about sudoku
 *)

(* Involution property of the operations on boards *)

Lemma rows_id : forall (b:board),
  rows (rows b) = b.
Proof. reflexivity. Qed.

Lemma cols_id : forall (b:board),
  cols (cols b) = b.
Proof.
  (* in Sudoku.agda for N = 3 *)
Admitted.

Lemma boxes_id : forall (b:board),
  boxes (boxes b) = b.
Proof.
  (* in Sudoku.agda for N = 3 *)
Admitted.

(* Trivial correctness properties of the naive approaches *)

Theorem naive_all_correct : forall (b:board),
  all correct (sudoku_naive b) = true.
Proof.
  intros. unfold sudoku_naive. induction (mcp (choices b)).
    reflexivity.
    simpl. remember (correct a) as cora; destruct cora.
      unfold all. rewrite <- Heqcora. apply IHl.
      apply IHl.
Qed.

Theorem naive_2_all_correct : forall (b:board),
  all correct (sudoku_naive_2 b) = true.
Proof.
  intros. unfold sudoku_naive_2. induction (mcp (prune (choices b))).
    reflexivity.
    simpl. remember (correct a) as cora; destruct cora.
      unfold all. rewrite <- Heqcora. apply IHl.
      apply IHl.
Qed.

End Sudoku.