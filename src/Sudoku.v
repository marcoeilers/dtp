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

(* Determines if any element of the list satisfies the predicate *)
Fixpoint any {A:Type} (f:A -> bool) (l:list A) : bool :=
  match l with
    | [] => false
    | x :: xs => if f x then true else any f xs
  end.

(* Test whether a list is empty *)
Definition null {A:Type} (l:list A) : bool :=
  match l with
    | [] => true
    | _ => false
  end.

(* Determines if all elements of the list satisfy the predicate *)
Fixpoint all {A:Type} (f:A -> bool) (l:list A) : bool :=
  match l with
    | [] => true
    | x :: xs => if f x then all f xs else false
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

Definition test_board : board :=
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

Definition Interface_eq x y := if ascii_dec x y then true else false.

Fixpoint member (a:cellval) (l:list cellval) : bool :=
  match l with
    | [] => false
    | x :: xs => if Interface_eq x a then true else member a xs
  end.

Definition matrix_choices := list (list (list cellval)).

Definition choose (c:cellval) : list cellval :=
  if blank c then cellvals else [c].

Definition choices (b:board) : matrix_choices :=
  map (map choose) b.

Definition single {A:Type} (l:list A) : bool :=
  match l with | [x] => true | _ => false end.

Definition fixed (l:list (list cellval)) : list cellval :=
  ungroup (filter single l).

(* fs : fixed entries, cs : choices
   removes a list of fixed entries from the list of choices, used below *)
Definition delete (fs:list cellval) (cs:list cellval) : list cellval :=
  filter (fun x:cellval => member x fs) cs.
  
(* fs : fixed entries, cs : choices
   removes a list of fixed entries from the list of choices *)
Definition remove (fs:list cellval) (cs:list cellval) : list cellval :=
  if single cs then cs else delete fs cs.

Definition reduce (l:list (list cellval)) : list (list cellval) :=
  map (remove (fixed l)) l.

Definition prune_by (f:matrix_choices -> matrix_choices) : matrix_choices -> matrix_choices :=
  fun cs:matrix_choices => f (map reduce (f cs)).

Definition prune (choices:matrix_choices) : matrix_choices :=
  prune_by boxes (prune_by cols (prune_by rows choices)).

Definition void (cm:matrix_choices) : bool :=
  any (any null) cm.

Fixpoint nodups (l:list cellval) : bool :=
  match l with
    | [] => true
    | x :: xs => if member x xs then false else nodups xs
  end.

Definition safe (cm:matrix_choices) : bool :=
  andb3
    (all (fun xs:list (list cellval) => nodups (fixed xs)) (rows cm))
    (all (fun xs:list (list cellval) => nodups (fixed xs)) (cols cm))
    (all (fun xs:list (list cellval) => nodups (fixed xs)) (boxes cm)).

Definition blocked (cm:matrix_choices) : bool :=
  andb (void cm) (negb (safe cm)).

Fixpoint minimum (l:list nat) (m:nat) : nat :=
  match l with
  | nil => m
  | x::xs => if blt_nat x m then minimum xs x else minimum xs m
  end.

Fixpoint list_size {A:Type} (l:list A) : nat :=
  match l with
  | nil => 0
  | x::xs => S (list_size xs)
  end.

Definition minchoice (cm:matrix_choices) : nat :=
  minimum (filter (fun n:nat => blt_nat 1 n) (ungroup (map (map list_size) cm))) 0.

Definition best {A:Type} (m:nat) (cs:list A) : bool :=
  beq_nat m (list_size cs).

Fixpoint break {A:Type} (f: A -> bool) (l:list A) : (list A * list A) :=
  match l with
  | nil => (nil, nil)
  | x::xs => if f x then (nil, l) 
                    else let (a,b) := (break f xs) in (x::a, b)
  end.

Eval simpl in break (fun x => beq_nat 3 x) [1,2,3,4,5].

Definition expand (cm:matrix_choices) : list matrix_choices :=
  let n := minchoice cm in
  let (rows1,rows2') := (break (fun y => any (fun x => best n x) y) cm) in
  match rows2' with
    | nil => nil (* should never happen *)
    | row::rows2 => 
        let (row1, row2') := break (fun x => best n x ) row in
        match row2' with
          | nil => nil (* should never happen *)
          | cs::row2 => map (fun c => rows1 ++ [row1 ++ [c]::row2] ++ rows2) cs
        end
  end.

(* TODO illformed recursion over cm *)
Fixpoint search (n: nat) (cm:matrix_choices) : list matrix_choices :=
  match n with
  | 0 => [cm]
  | S n' =>
  if blocked cm then []
  else if all (all single) cm then [cm]
  else ungroup (map (fun x:matrix_choices => search n' (prune x)) (expand cm))
  end.

Definition sudoku (b:board) : list board :=
  map (map (fun l => hd [] l)) (search 1000 (prune (choices b))).




End Sudoku.