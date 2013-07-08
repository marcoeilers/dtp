module Sudoku where

data _==_ {X : Set}(x : X) : X -> Set where 
  Refl : x == x


open import Data.Bool
open import Data.Nat
open import Data.Vec
import Data.Product as P
import Data.List as L

Nat = ℕ

cong : {a b : Set} -> {x y : a} -> (f : a -> b) -> x == y -> (f x) == (f y)
cong f Refl = Refl

trans : {a : Set} {b c d : a} -> b == c -> c == d -> b == d
trans Refl Refl = Refl

sym : {a : Set} {b c : a} -> b == c -> c == b
sym Refl = Refl

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
cols (xs ∷ xss) = vmap _∷_ xs  <*> (cols xss)


groupBox : {a : Set} -> Vec a boardsize -> Vec (Vec a boxsize) boxsize
groupBox l = P.Σ.proj₁ (group boxsize boxsize l)

boxs : {a : Set} -> Vec (Vec a boardsize) boardsize -> Vec (Vec a boardsize) boardsize
boxs b = Data.Vec.map Data.Vec.concat (Data.Vec.concat (Data.Vec.map cols (groupBox (Data.Vec.map groupBox b))))

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

allVec : {a : Set} {n : Nat} -> (a -> Bool) -> Vec a n -> Bool
allVec f [] = true
allVec f (x ∷ xs) = if f x then allVec f xs else false 

correct : Board -> Bool
correct b = allVec nodups (rows b)  ∧ allVec nodups (cols b)  ∧ allVec nodups (boxs b)

cp : {a : Set} {n : Nat} -> Vec (L.List a) n -> L.List (Vec a n)
cp [] = L._∷_ [] L.[]
cp (xs ∷ xss) = L.concat (L.map (λ x -> L.map (λ ys -> x ∷ ys) (cp xss)) xs)

mcp : {a : Set} {n m : Nat} -> Vec (Vec (L.List a) m) n -> L.List (Vec (Vec a m) n)
mcp cs = cp (map cp cs)

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

fType : {a : Set} -> Set
fType {a} = (Vec (Vec a boardsize) boardsize -> Vec (Vec a boardsize) boardsize)
bType = Vec (Vec (L.List CellVal) boardsize) boardsize
ListBoard = L.List Board
VecVecABsBs : {a : Set} -> Set
VecVecABsBs {a} = Vec (Vec a boardsize) boardsize
VecVecListABsBs : {a : Set} -> Set
VecVecListABsBs {a} = Vec (Vec (L.List a) boardsize) boardsize
idType : {a : Set} -> (fType {a}) -> Set
idType {a} f = ((b'' : VecVecABsBs) -> f (f b'') == b'')
polyFType = (a : Set) -> fType {a}
mapMcpType : polyFType -> Set
mapMcpType f = ((b'' : VecVecABsBs) -> L.map (f CellVal) (mcp b'') == mcp ((f (L.List CellVal)) b''))

rowsId : {a : Set} -> (b : Vec (Vec a boardsize) boardsize) -> rows (rows b) == b
rowsId b = Refl

colsId : {a : Set} -> (b : Vec (Vec a boardsize) boardsize) -> cols (cols b) == b
colsId ((xr1c1 ∷ xr1c2 ∷ xr1c3 ∷ xr1c4 ∷ xr1c5 ∷ xr1c6 ∷ xr1c7 ∷ xr1c8 ∷ xr1c9 ∷ []) ∷
 (xr2c1 ∷ xr2c2 ∷ xr2c3 ∷ xr2c4 ∷ xr2c5 ∷ xr2c6 ∷ xr2c7 ∷ xr2c8 ∷ xr2c9 ∷ []) ∷
 (xr3c1 ∷ xr3c2 ∷ xr3c3 ∷ xr3c4 ∷ xr3c5 ∷ xr3c6 ∷ xr3c7 ∷ xr3c8 ∷ xr3c9 ∷ []) ∷
 (xr4c1 ∷ xr4c2 ∷ xr4c3 ∷ xr4c4 ∷ xr4c5 ∷ xr4c6 ∷ xr4c7 ∷ xr4c8 ∷ xr4c9 ∷ []) ∷
 (xr5c1 ∷ xr5c2 ∷ xr5c3 ∷ xr5c4 ∷ xr5c5 ∷ xr5c6 ∷ xr5c7 ∷ xr5c8 ∷ xr5c9 ∷ []) ∷
 (xr6c1 ∷ xr6c2 ∷ xr6c3 ∷ xr6c4 ∷ xr6c5 ∷ xr6c6 ∷ xr6c7 ∷ xr6c8 ∷ xr6c9 ∷ []) ∷
 (xr7c1 ∷ xr7c2 ∷ xr7c3 ∷ xr7c4 ∷ xr7c5 ∷ xr7c6 ∷ xr7c7 ∷ xr7c8 ∷ xr7c9 ∷ []) ∷
 (xr8c1 ∷ xr8c2 ∷ xr8c3 ∷ xr8c4 ∷ xr8c5 ∷ xr8c6 ∷ xr8c7 ∷ xr8c8 ∷ xr8c9 ∷ []) ∷
 (xr9c1 ∷ xr9c2 ∷ xr9c3 ∷ xr9c4 ∷ xr9c5 ∷ xr9c6 ∷ xr9c7 ∷ xr9c8 ∷ xr9c9 ∷ []) ∷ []) = Refl



boxsId : {a : Set} -> (b : Vec (Vec a boardsize) boardsize) -> boxs (boxs b) == b
boxsId ((xr1c1 ∷ xr1c2 ∷ xr1c3 ∷ xr1c4 ∷ xr1c5 ∷ xr1c6 ∷ xr1c7 ∷ xr1c8 ∷ xr1c9 ∷ []) ∷
 (xr2c1 ∷ xr2c2 ∷ xr2c3 ∷ xr2c4 ∷ xr2c5 ∷ xr2c6 ∷ xr2c7 ∷ xr2c8 ∷ xr2c9 ∷ []) ∷
 (xr3c1 ∷ xr3c2 ∷ xr3c3 ∷ xr3c4 ∷ xr3c5 ∷ xr3c6 ∷ xr3c7 ∷ xr3c8 ∷ xr3c9 ∷ []) ∷
 (xr4c1 ∷ xr4c2 ∷ xr4c3 ∷ xr4c4 ∷ xr4c5 ∷ xr4c6 ∷ xr4c7 ∷ xr4c8 ∷ xr4c9 ∷ []) ∷
 (xr5c1 ∷ xr5c2 ∷ xr5c3 ∷ xr5c4 ∷ xr5c5 ∷ xr5c6 ∷ xr5c7 ∷ xr5c8 ∷ xr5c9 ∷ []) ∷
 (xr6c1 ∷ xr6c2 ∷ xr6c3 ∷ xr6c4 ∷ xr6c5 ∷ xr6c6 ∷ xr6c7 ∷ xr6c8 ∷ xr6c9 ∷ []) ∷
 (xr7c1 ∷ xr7c2 ∷ xr7c3 ∷ xr7c4 ∷ xr7c5 ∷ xr7c6 ∷ xr7c7 ∷ xr7c8 ∷ xr7c9 ∷ []) ∷
 (xr8c1 ∷ xr8c2 ∷ xr8c3 ∷ xr8c4 ∷ xr8c5 ∷ xr8c6 ∷ xr8c7 ∷ xr8c8 ∷ xr8c9 ∷ []) ∷
 (xr9c1 ∷ xr9c2 ∷ xr9c3 ∷ xr9c4 ∷ xr9c5 ∷ xr9c6 ∷ xr9c7 ∷ xr9c8 ∷ xr9c9 ∷ []) ∷ []) = Refl


rowsMapfilterAllCp : (b' : ListBoard) -> L.map rows b' == b'
rowsMapfilterAllCp L.[] = Refl
rowsMapfilterAllCp (L._∷_ x xs) = cong (L._∷_ x) (rowsMapfilterAllCp xs)

rowsMapMcp : (b : VecVecABsBs) -> L.map rows (mcp b) == mcp (rows b)
rowsMapMcp b with  L.map rows (mcp b) | rowsMapfilterAllCp (mcp b) 
rowsMapMcp b | .(mcp b) | Refl = Refl

colsMapMcp : {a : Set} -> (b : VecVecABsBs) -> L.map (cols {a}) (mcp b) == mcp (cols b)
colsMapMcp b = {!!}

boxsMapMcp : {a : Set} -> (b : VecVecABsBs) -> L.map (boxs {a}) (mcp b) == mcp (boxs b)
boxsMapMcp b = {!!}

filterMapFilterMap' : (x : Board) -> (f : fType) -> (b' : ListBoard) -> (p : Board -> Bool) -> idType f -> 
       L._∷_ x (L.map f (L.filter p (L.map f b'))) == L._∷_ (f (f x)) (L.map f (L.filter p (L.map f b'))) 
filterMapFilterMap' x f b' p id with (f (f x)) | id x
filterMapFilterMap' x f b' p id | .x | Refl = Refl

filterMapFilterMap : (f : fType) -> (b' : ListBoard) -> (p : Board -> Bool) -> idType f -> 
      L.filter (λ x -> p (f x)) b' == L.map f (L.filter p (L.map f b'))
filterMapFilterMap f L.[] p id = Refl
filterMapFilterMap f (L._∷_ x xs) p id with p (f x)
filterMapFilterMap f (L._∷_ x xs) p id | bool with (f (f x)) | id x 
filterMapFilterMap f (L._∷_ x xs) p id | true | .x | Refl  = trans (cong (L._∷_ x) (filterMapFilterMap f xs p id)) (filterMapFilterMap' x f xs p id)
filterMapFilterMap f (L._∷_ x xs) p id | false | .x | Refl = filterMapFilterMap f xs p id

mapFilterFilterMap' : (f : fType) -> (b' : ListBoard) -> idType f ->
        L.map f (L.map f b') == b'
mapFilterFilterMap' f L.[] id = Refl
mapFilterFilterMap' f (L._∷_ x xs) id with (f (f x)) | id x 
mapFilterFilterMap' f (L._∷_ x xs) id | .x | Refl = cong (L._∷_ x) (mapFilterFilterMap' f xs id)

mapFilterFilterMap : (f : fType) -> (b' : ListBoard) -> (p : Board -> Bool) -> idType f ->
       L.map f (L.filter p b') == L.filter (λ x -> p (f x)) (L.map f b')
mapFilterFilterMap f b' p id with (L.filter (λ x -> p (f x)) (L.map f b')) | filterMapFilterMap f (L.map f b') p id 
mapFilterFilterMap f b' p id | ._ | Refl with (L.map f (L.map f b')) | mapFilterFilterMap' f b' id 
mapFilterFilterMap f b' p id | ._ | Refl | .b' | Refl = Refl


step1 : (f : fType) -> idType f -> (b : bType) -> 
        L.filter (λ x -> allVec nodups (f x)) (mcp b) == L.map f (L.filter (allVec nodups) (L.map f (mcp b)))
step1 f id b = filterMapFilterMap f (mcp b) (allVec nodups) id

step2' : (f : polyFType) -> mapMcpType f -> (b : bType) ->
         L.map (f CellVal) (L.filter (allVec nodups) (L.map (f CellVal) (mcp b))) == 
         L.map (f CellVal) (L.filter (allVec nodups) (mcp ((f (L.List CellVal)) b)))
step2' f id b with (L.map (f CellVal) (mcp b)) | (id b) 
step2' f id b | ._ | Refl = Refl

step2 : (f : polyFType) -> (b : bType) -> idType (f _) -> mapMcpType f ->
        L.filter (λ x -> allVec nodups ((f _) x)) (mcp b) == 
        L.map (f _) (L.filter (allVec nodups) (mcp ((f _) b)))
step2 f b id id' = trans (step1 (f _) id b) (step2' f id' b)

step3' : (f : polyFType) -> (b : bType) -> 
         L.map (f _) (L.filter (allVec nodups) (mcp ((f _) b))) == 
         L.map (f _) (L.filter (allVec nodups) (cp (map cp ((f _) b))))
step3' f b = Refl

step3 : (f : polyFType) -> (b : bType) -> idType (f _) -> mapMcpType f ->
        L.filter (λ x -> allVec nodups ((f _) x)) (mcp b) == 
        L.map (f _) (L.filter (allVec nodups) (cp (map cp ((f _) b))))
step3 f b id mapMcp = trans (step2 f b id mapMcp) (step3' f b)

-- cannot prove this. any implicit assumptions?
filterAllCp : {a : Set} {n : Nat} -> (p : a -> Bool) -> (b : Vec (L.List a) n) -> 
       L.filter (allVec p) (cp b) == cp (map (L.filter p) b)
filterAllCp p [] = Refl
filterAllCp p (x ∷ xs) = {!!}

step4'' : {n m : Nat} -> (b : Vec (Vec (L.List CellVal) n) m) -> 
      map (L.filter nodups) (map cp b) == map (λ x -> L.filter nodups (cp x)) b
step4'' [] = Refl
step4'' (x ∷ xs) with L.filter nodups (cp x)
step4'' (x ∷ xs) | fcpx = cong (_∷_ fcpx) (step4'' xs)


step4' : (f : polyFType) -> (b : bType) -> 
         L.map (f _) (L.filter (allVec nodups) (cp (map cp ((f _) b)))) ==         
         L.map (f _) (cp (map (λ x -> L.filter nodups (cp x)) ((f _) b)))
step4' f b with (L.filter (allVec nodups) (cp (map cp ((f _) b)))) | (filterAllCp nodups (map cp ((f _) b)))
step4' f b | .(cp (map (L.filter nodups) (map cp ((f _) b)))) | Refl with (map (L.filter nodups) (map cp ((f _) b))) | step4'' (f _ b)
step4' f b | .(cp (map (L.filter nodups) (map cp ((f _) b)))) | Refl | .(map (λ x -> L.filter nodups (cp x)) (f _ b)) | Refl  = Refl

step4 : (f : polyFType) -> (b : bType) -> idType (f _) -> mapMcpType f ->
        L.filter (λ x -> allVec nodups ((f _) x)) (mcp b) == 
        L.map (f _) (cp (map (λ x -> L.filter nodups (cp x)) ((f _) b)))
step4 f b id mapMcp = trans (step3 f b id mapMcp) (step4' f b)

-- If we manage to prove this, we're awesome. Otherwise I think it would be okay to just assume this.
reduceProp : {n : Nat} -> (v : Vec (L.List CellVal) n) -> 
             L.filter nodups (cp v) == L.filter nodups (cp (reduce v))
reduceProp [] = Refl
reduceProp (x ∷ xs) = {!!}

reduceProp' : {n m : Nat} -> (b : Vec (Vec (L.List CellVal) m) n) ->
              map (λ x -> L.filter nodups (cp x)) b ==
              map (λ x -> L.filter nodups (cp (reduce x))) b
reduceProp' [] = Refl
reduceProp' (x ∷ xs) with (L.filter nodups (cp x)) | (reduceProp x)
reduceProp' (x ∷ xs) | ._ | Refl = cong (_∷_ (L.filter nodups (cp (reduce x)))) (reduceProp' xs)

-- How to prove this? Kind of weird because we have to replace within a lambda expression
step5' : (f : polyFType) -> (b : bType) -> 
         L.map (f _) (cp (map (λ x -> L.filter nodups (cp x)) ((f _) b))) ==
         L.map (f _) (cp (map (λ x -> L.filter nodups (cp (reduce x))) ((f _) b)))
step5' f b with (map (λ x -> L.filter nodups (cp x)) ((f _) b)) | reduceProp' ((f _) b) 
step5' f b | ._ | Refl = Refl

step5 : (f : polyFType) -> (b : bType) -> idType (f _) -> mapMcpType f ->
        L.filter (λ x -> allVec nodups ((f _) x)) (mcp b) == 
        L.map (f _) (cp (map (λ x -> L.filter nodups (cp (reduce x))) ((f _) b)))
step5 f b id mapMcp = trans (step4 f b id mapMcp) (step5' f b)

step6'' : {n m : Nat} -> (b : Vec (Vec (L.List CellVal) n) m) -> 
      map (L.filter nodups) (map (λ x -> cp (reduce x)) b) == map (λ x -> L.filter nodups (cp (reduce x))) b
step6'' [] = Refl
step6'' (x ∷ xs) with L.filter nodups (cp (reduce x)) 
step6'' (x ∷ xs) | fcprx = cong (_∷_ fcprx) (step6'' xs) 

step6' : (f : polyFType) -> (b : bType) -> 
         L.map (f _) (cp (map (λ x -> L.filter nodups (cp (reduce x))) ((f _) b))) ==
         L.map (f _) (L.filter (allVec nodups) (cp (map (λ x -> cp (reduce x)) ((f _) b))))
step6' f b with (L.filter (allVec nodups) (cp (map (λ x -> cp (reduce x)) ((f _) b)))) | filterAllCp nodups (map (λ x -> cp (reduce x)) ((f _) b)) 
step6' f b | ._ | Refl with (map (λ x -> L.filter nodups (cp (reduce x))) ((f _) b)) | step6'' (f _ b) 
step6' f b | ._ | Refl | ._ | Refl = Refl

step6 : (f : polyFType) -> (b : bType) -> idType (f _) -> mapMcpType f ->
        L.filter (λ x -> allVec nodups ((f _) x)) (mcp b) == 
        L.map (f _) (L.filter (allVec nodups) (cp (map (λ x -> cp (reduce x)) ((f _) b))))
step6 f b id mapMcp = trans (step5 f b id mapMcp) (step6' f b)

step7''' : {m n : Nat} -> (f : polyFType) -> (b : Vec (Vec (L.List CellVal) m) n) -> 
         (map cp (map reduce b)) == map (λ x -> cp (reduce x)) b
step7''' f [] = Refl
step7''' f (x ∷ xs) = cong (_∷_ (cp (reduce x))) (step7''' f xs)

step7'' : (f : polyFType) -> (b : bType) -> 
        mcp (map reduce ((f _) b)) == cp (map (λ x -> cp (reduce x)) (f _ b))
step7'' f b = cong (cp) (step7''' f (f _ b))

step7' : (f : polyFType) -> (b : bType) -> idType (f _) -> 
         L.map (f _) (L.filter (allVec nodups) (cp (map (λ x -> cp (reduce x)) ((f _) b)))) ==
         L.filter (λ x -> allVec nodups ((f _) x)) (L.map (f _) (mcp (map reduce ((f _) b))))
step7' f b id with (L.map (f _) (L.filter (allVec nodups) (cp (map (λ x -> cp (reduce x)) ((f _) b)))))  | mapFilterFilterMap (f _) (cp (map (λ x -> cp (reduce x)) ((f _) b))) (allVec nodups) id 
step7' f b id | ._ | Refl with (mcp (map reduce ((f _) b))) | step7'' f b 
step7' f b id | ._ | Refl | ._ | Refl = Refl

step7 : (f : polyFType) -> (b : bType) -> idType (f _) -> mapMcpType f ->
        L.filter (λ x -> allVec nodups ((f _) x)) (mcp b) == 
        L.filter (λ x -> allVec nodups ((f _) x)) (L.map (f _) (mcp (map reduce ((f _) b))))
step7 f b id mapMcp = trans (step6 f b id mapMcp) (step7' f b id)

step8' : (f : polyFType) -> (b : bType) -> mapMcpType f ->
         L.filter (λ x -> allVec nodups ((f _) x)) (L.map (f _) (mcp (map reduce ((f _) b)))) ==
         L.filter (λ x -> allVec nodups ((f _) x)) (mcp ((f _) (map reduce ((f _) b))))
step8' f b mapMcp with (L.map (f _) (mcp (map reduce ((f _) b)))) | (mapMcp (map reduce ((f _) b))) 
step8' f b mapMcp | ._ | Refl = Refl

step8 : (f : polyFType) -> (b : bType) -> idType (f _) -> mapMcpType f ->
        L.filter (λ x -> allVec nodups ((f _) x)) (mcp b) == 
        L.filter (λ x -> allVec nodups ((f _) x)) (mcp ((f _) (map reduce ((f _) b))))
step8 f b id mapMcp = trans (step7 f b id mapMcp) (step8' f b mapMcp)

step9' : (f : polyFType) -> (b : bType) -> 
         L.filter (λ x -> allVec nodups ((f _) x)) (mcp ((f _) (map reduce ((f _) b)))) ==
         L.filter (λ x -> allVec nodups ((f _) x)) (mcp (pruneBy (f _) b))
step9' f b = Refl

step9 : (f : polyFType) -> (b : bType) -> idType (f _) -> mapMcpType f ->
        L.filter (λ x -> allVec nodups ((f _) x)) (mcp b) == 
        L.filter (λ x -> allVec nodups ((f _) x)) (mcp (pruneBy (f _) b))
step9 f b id mapMcp = trans (step8 f b id mapMcp) (step9' f b)

pruneCorrectRows : (b : VecVecABsBs) ->
            L.filter (λ x -> allVec nodups (rows x)) (mcp b) == 
            L.filter (λ x -> allVec nodups (rows x)) (mcp (pruneBy rows b))
pruneCorrectRows b = step9 (λ x -> rows {x}) b rowsId rowsMapMcp

pruneCorrectCols : (b : VecVecABsBs) ->
            L.filter (λ x -> allVec nodups (cols x)) (mcp b) == 
            L.filter (λ x -> allVec nodups (cols x)) (mcp (pruneBy cols b))
pruneCorrectCols b = step9 (λ x -> cols {x}) b colsId colsMapMcp

pruneCorrectBoxs : (b : VecVecABsBs) ->
            L.filter (λ x -> allVec nodups (boxs x)) (mcp b) == 
            L.filter (λ x -> allVec nodups (boxs x)) (mcp (pruneBy boxs b))
pruneCorrectBoxs b = step9 (λ x -> boxs {x}) b boxsId boxsMapMcp

-- now put it all together

-- proved in Coq, so we can just admit this here
filterConjunction : (a : Set) -> (b : L.List a) -> (p1 p2 p3 : a -> Bool) ->
                    L.filter p1 (L.filter p2 (L.filter p3 b)) == L.filter (λ x -> p3 x ∧ p2 x ∧ p1 x) b
filterConjunction a b p1 p2 p3 = {!!}  

    
filterCorrect : (b : L.List Board) -> 
                L.filter correct b == L.filter (λ x -> allVec nodups (boxs x)) (L.filter (λ x -> allVec nodups (cols x)) (L.filter (λ x -> allVec nodups (rows x)) b))
filterCorrect b with  L.filter correct b | filterConjunction Board b (λ x -> allVec nodups (boxs x)) (λ x -> allVec nodups (cols x)) (λ x -> allVec nodups (rows x)) 
filterCorrect b | ._  | Refl  = Refl     

-- proved in Coq, so we can just admit this here
filterSwap : (a : Set) ->  (b : L.List a) -> (p1 p2 : a -> Bool) ->
  L.filter p1 (L.filter p2 b) == L.filter p2 (L.filter p1 b)
filterSwap a b p1 p2 = {!!}

--correct : Board -> Bool
--correct b = allVec nodups (rows b)  ∧ allVec nodups (cols b)  ∧ allVec nodups (boxs b)

filterCorrectMcp : (b : VecVecListABsBs) -> 
                   L.filter correct (mcp b) == 
                   L.filter (λ x -> allVec nodups (boxs x)) (L.filter (λ x -> allVec nodups (cols x)) (L.filter (λ x -> allVec nodups (rows x)) (mcp b)))
filterCorrectMcp b = filterCorrect (mcp b)

addPruneRows : (b : VecVecListABsBs) -> 
               L.filter (λ x -> allVec nodups (boxs x)) (L.filter (λ x -> allVec nodups (cols x)) (L.filter (λ x -> allVec nodups (rows x)) (mcp b))) ==
               L.filter (λ x -> allVec nodups (boxs x)) (L.filter (λ x -> allVec nodups (cols x)) (L.filter (λ x -> allVec nodups (rows x)) (mcp (pruneBy rows b))))
addPruneRows b = cong (λ y -> L.filter (λ x -> allVec nodups (boxs x)) (L.filter (λ x -> allVec nodups (cols x)) y)) (pruneCorrectRows b)

rearrange1 : (b : VecVecListABsBs) -> 
             L.filter (λ x -> allVec nodups (boxs x)) (L.filter (λ x -> allVec nodups (cols x)) (L.filter (λ x -> allVec nodups (rows x)) (mcp (pruneBy rows b)))) ==
             L.filter (λ x -> allVec nodups (boxs x)) (L.filter (λ x -> allVec nodups (rows x)) (L.filter (λ x -> allVec nodups (cols x)) (mcp (pruneBy rows b))))
rearrange1 b = cong (λ y -> L.filter (λ x -> allVec nodups (boxs x)) y) (filterSwap _ (mcp (pruneBy rows b)) (λ x -> allVec nodups (cols x)) (λ x -> allVec nodups (rows x)))

addPruneCols : (b : VecVecListABsBs) -> 
               L.filter (λ x -> allVec nodups (boxs x)) (L.filter (λ x -> allVec nodups (rows x)) (L.filter (λ x -> allVec nodups (cols x)) (mcp (pruneBy rows b)))) ==
               L.filter (λ x -> allVec nodups (boxs x)) (L.filter (λ x -> allVec nodups (rows x)) (L.filter (λ x -> allVec nodups (cols x)) (mcp (pruneBy cols (pruneBy rows b)))))
addPruneCols b = cong (λ y -> L.filter (λ x -> allVec nodups (boxs x)) (L.filter (λ x -> allVec nodups (rows x)) y)) (pruneCorrectCols (pruneBy rows b))

rearrange2 : (b : VecVecListABsBs) -> 
             L.filter (λ x -> allVec nodups (boxs x)) (L.filter (λ x -> allVec nodups (rows x)) (L.filter (λ x -> allVec nodups (cols x)) (mcp (pruneBy cols (pruneBy rows b))))) ==
             L.filter (λ x -> allVec nodups (rows x)) (L.filter (λ x -> allVec nodups (cols x)) (L.filter (λ x -> allVec nodups (boxs x)) (mcp (pruneBy cols (pruneBy rows b)))))
rearrange2 b = trans (filterSwap _ (L.filter (λ x -> allVec nodups (cols x)) (mcp (pruneBy cols (pruneBy rows b)))) (λ x -> allVec nodups (boxs x)) (λ x -> allVec nodups (rows x))) (cong (λ y -> L.filter (λ x -> allVec nodups (rows x)) y) (filterSwap _ (mcp (pruneBy cols (pruneBy rows b))) (λ x -> allVec nodups (boxs x)) (λ x -> allVec nodups (cols x))))

addPruneBoxs : (b : VecVecListABsBs) -> 
               L.filter (λ x -> allVec nodups (rows x)) (L.filter (λ x -> allVec nodups (cols x)) (L.filter (λ x -> allVec nodups (boxs x)) (mcp (pruneBy cols (pruneBy rows b))))) ==
               L.filter (λ x -> allVec nodups (rows x)) (L.filter (λ x -> allVec nodups (cols x)) (L.filter (λ x -> allVec nodups (boxs x)) (mcp (pruneBy boxs (pruneBy cols (pruneBy rows b))))))
addPruneBoxs b = cong (λ y -> L.filter (λ x -> allVec nodups (rows x)) (L.filter (λ x -> allVec nodups (cols x)) y)) (pruneCorrectBoxs (pruneBy cols (pruneBy rows b)))

rearrange3 : (b : VecVecListABsBs) -> 
             L.filter (λ x -> allVec nodups (rows x)) (L.filter (λ x -> allVec nodups (cols x)) (L.filter (λ x -> allVec nodups (boxs x)) (mcp (pruneBy boxs (pruneBy cols (pruneBy rows b)))))) ==
             L.filter (λ x -> allVec nodups (boxs x)) (L.filter (λ x -> allVec nodups (cols x)) (L.filter (λ x -> allVec nodups (rows x)) (mcp (pruneBy boxs (pruneBy cols (pruneBy rows b))))))
rearrange3 b = trans (cong (λ y -> L.filter (λ x -> allVec nodups (rows x)) y) (filterSwap _ (mcp (pruneBy boxs (pruneBy cols (pruneBy rows b)))) (λ x -> allVec nodups (cols x)) (λ x -> allVec nodups (boxs x)))) 
               (trans (filterSwap _ (L.filter (λ x -> allVec nodups (cols x)) (mcp (pruneBy boxs (pruneBy cols (pruneBy rows b))))) (λ x -> allVec nodups (rows x)) (λ x -> allVec nodups (boxs x))) 
               (cong (λ y -> L.filter (λ x -> allVec nodups (boxs x)) y) (filterSwap _ (mcp (pruneBy boxs (pruneBy cols (pruneBy rows b)))) (λ x -> allVec nodups (rows x)) (λ x -> allVec nodups (cols x))))) 

final : (b : VecVecListABsBs) -> 
        L.filter (λ x -> allVec nodups (boxs x)) (L.filter (λ x -> allVec nodups (cols x)) (L.filter (λ x -> allVec nodups (rows x)) (mcp (pruneBy boxs (pruneBy cols (pruneBy rows b)))))) ==
        L.filter correct (mcp (prune b))
final b = sym (filterCorrect (mcp (pruneBy boxs (pruneBy cols (pruneBy rows b)))))

equivalence' : (b : VecVecListABsBs) -> 
                L.filter correct (mcp b) == 
                L.filter correct (mcp (prune b))
equivalence' b = trans (filterCorrectMcp b) (trans (addPruneRows b) (trans (rearrange1 b) (trans (addPruneCols b) (trans (rearrange2 b) (trans (addPruneBoxs b) (trans (rearrange3 b) (final b)))))))

equivalence : (b : Board) -> 
              sudokuNaive b == sudokuNaive2 b
equivalence b = equivalence' (choices b)


