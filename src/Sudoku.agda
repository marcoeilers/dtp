module Sudoku where
open import Data.Bool
open import Data.Nat
open import Data.Vec
import Data.Product as P
import Data.List as L


Nat = ℕ

eq_nat : Nat -> Nat -> Bool
eq_nat zero zero = true
eq_nat zero (suc n) = false
eq_nat (suc n) zero = false
eq_nat (suc n) (suc n') = eq_nat n n'


pure : {n : Nat} {a : Set} -> a -> Vec a n
pure {zero} = λ x → []
pure {suc y} = λ x →  x ∷ (pure {y} x)

_<*>_ : {a b : Set} {n : Nat} -> Vec (a -> b) n -> Vec a n -> Vec b n
[] <*> [] = []
(f ∷ fs) <*> (x ∷ xs) = (f x) ∷ (fs <*> xs)

vmap : {a b : Set} {n : Nat} -> (a -> b) -> Vec a n -> Vec b n
vmap f [] = []
vmap f (x ∷ xs) = (f x) ∷ (vmap f xs)

pow : Nat -> Nat -> Nat
pow n zero = 1
pow n (suc n') = n * pow n n'


boxsize = 3

boardsize = boxsize * boxsize

CellVal = Nat

cellVals : Vec CellVal boardsize
cellVals = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ []

blank : CellVal -> Bool
blank 0 = true
blank _ = false

Col = Vec CellVal boardsize
Row = Vec CellVal boardsize
Board = Vec Row boardsize

rows : {a : Set} {n m : Nat} -> Vec (Vec a n) m -> Vec (Vec a n) m
rows b = b

cols : {a : Set} {n m : Nat} -> Vec (Vec a n) m -> Vec (Vec a m) n
cols [] = pure []
cols (xs ∷ []) = vmap (λ x -> x ∷ []) xs
cols (xs ∷ xss) = vmap _∷_ xs  <*> (cols xss)


mygroup : {a : Set} -> Vec a boardsize -> Vec (Vec a boxsize) boxsize
mygroup l = P.Σ.proj₁ (group boxsize boxsize l)



boxs : {a : Set} -> Vec (Vec a boardsize) boardsize -> Vec (Vec a boardsize) boardsize
boxs b = Data.Vec.map Data.Vec.concat (Data.Vec.concat (Data.Vec.map cols (mygroup (Data.Vec.map mygroup b))))

testboard =
  (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ [] ) ∷
  (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ [] ) ∷
  (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ [] ) ∷
  (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ [] ) ∷
  (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ [] ) ∷
  (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ [] ) ∷
  (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ [] ) ∷
  (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ [] ) ∷
  (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ [] ) ∷ []

member : {n : Nat} -> CellVal -> Vec CellVal n -> Bool
member a [] = false
member a (x ∷ xs) = if eq_nat a x then true else member a xs

MatrixChoices = Vec (Vec (L.List CellVal) boardsize) boardsize

choose :  CellVal -> L.List CellVal 
choose zero = toList cellVals
choose (suc n') = L._∷_ (suc n') L.[]

choices : Board -> MatrixChoices
choices b = map (map choose) b

nodups : {n : Nat} -> Vec CellVal n -> Bool
nodups [] = true
nodups (x ∷ xs) = if member x xs then false else nodups xs

allVec : {a : Set} {n : Nat} -> Vec a n -> (a -> Bool) -> Bool
allVec [] f = true
allVec (x ∷ xs) f = if f x then allVec xs f else false 

correct : Board -> Bool
correct b = allVec (rows b) nodups ∧ allVec (cols b) nodups ∧ allVec (boxs b) nodups

cp : {a : Set} {n m : Nat} -> Vec (Vec a n) m -> Vec (Vec a m) (pow n m)
cp [] = pure []
cp (xs ∷ xss) = concat (map (λ x -> map (λ ys -> x ∷ ys) (cp xss)) xs)

cp' : {a : Set} {n : Nat} -> Vec (L.List a) n -> L.List (Vec a n)
cp' [] = L._∷_ [] L.[]
cp' (xs ∷ xss) = L.concat (L.map (λ x -> L.map (λ ys -> x ∷ ys) (cp' xss)) xs)

mcp : {a : Set} {n m : Nat} -> Vec (Vec (L.List a) m) n -> L.List (Vec (Vec a m) n)
mcp cs = cp' (map cp' cs)

sudokuNaive : Board -> L.List Board
sudokuNaive b = L.filter correct (mcp (choices b))

single : L.List CellVal -> Bool
single l = eq_nat (L.length l) 0

fixed : {n : Nat} -> Vec (L.List CellVal) n -> L.List CellVal
fixed v = let l = toList v
           in L.concat (L.filter single l)

lmember : L.List CellVal -> CellVal -> Bool
lmember L.[] v = false
lmember (L._∷_ x xs) v = if eq_nat x v then true else lmember xs v

delete : L.List CellVal -> L.List CellVal -> L.List CellVal
delete fs cs = L.filter (λ x -> not (lmember fs x)) cs

remove : L.List CellVal -> L.List CellVal -> L.List CellVal
remove fs cs = if single cs then cs else delete fs cs

reduce : {n : Nat} -> Vec (L.List CellVal) n -> Vec (L.List CellVal) n
reduce l = map (remove (fixed l)) l

pruneBy : (MatrixChoices -> MatrixChoices) -> MatrixChoices -> MatrixChoices
pruneBy f = λ cs -> f (map reduce (f cs))

prune : MatrixChoices -> MatrixChoices
prune cs = pruneBy boxs (pruneBy cols (pruneBy rows cs))

sudokuNaive2 : Board -> L.List Board
sudokuNaive2 b = L.filter correct (mcp (prune (choices b)))






