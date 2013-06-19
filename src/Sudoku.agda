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




