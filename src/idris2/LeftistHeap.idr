module LeftistHeap

import Data.Nat

public export
data LeftistHeap : Nat -> Type -> Type where
    Empty : LeftistHeap 0 a
    Node  : (rank : Nat) -> a -> LeftistHeap n a -> LeftistHeap m a -> LeftistHeap (1 + n + m) a

public export
rank : LeftistHeap n a -> Nat
rank Empty = 0
rank (Node r _ _ _) = r

public export
makeNode : a -> LeftistHeap n a -> LeftistHeap m a -> LeftistHeap (1 + n + m) a
makeNode x l r =
  if rank l >= rank r
     then Node (rank r + 1) x l r
     else rewrite plusCommutative n m in Node (rank l + 1) x r l

0 mergeRightLemma : (n, mL, mR : Nat) -> S (mL + (n + mR)) = n + S (mL + mR)
mergeRightLemma Z mL mR = Refl
mergeRightLemma (S k) mL mR =
  let 0 rec = mergeRightLemma k mL mR
      0 pullS = sym (plusSuccRightSucc mL (k + mR))
  in rewrite pullS in rewrite rec in Refl

public export
merge : Ord a => LeftistHeap n a -> LeftistHeap m a -> LeftistHeap (n + m) a
merge Empty h2 = h2
merge {n} h1 Empty = rewrite plusZeroRightNeutral n in h1
merge h1@(Node {n=nL} {m=nR} _ x l1 r1) h2@(Node {n=mL} {m=mR} _ y l2 r2) =
  if x <= y
     then
       let merged = makeNode x l1 (merge r1 h2)
           0 prf = sym (plusAssociative nL nR (S (mL + mR)))
       in rewrite prf in merged
     else
       let merged = makeNode y l2 (merge h1 r2)
           0 prf = sym (mergeRightLemma (S (nL + nR)) mL mR)
       in rewrite prf in merged

public export
insert : Ord a => a -> LeftistHeap n a -> LeftistHeap (1 + n) a
insert x h = merge (Node 1 x Empty Empty) h

public export
findMin : LeftistHeap (S k) a -> a
findMin (Node _ x _ _) = x

public export
deleteMin : Ord a => LeftistHeap (S k) a -> LeftistHeap k a
deleteMin (Node _ _ l r) = merge l r

public export
Show a => Show (LeftistHeap n a) where
  show Empty = "."
  show (Node r x l rgt) =
    "(" ++ show x ++ " [r=" ++ show r ++ "] " ++ show l ++ " " ++ show rgt ++ ")"

public export
data Down : Type -> Type where
  MkDown : a -> Down a

public export
Eq a => Eq (Down a) where
  (MkDown x) == (MkDown y) = x == y

public export
Ord a => Ord (Down a) where
  compare (MkDown x) (MkDown y) = compare y x

public export
MinHeap : Nat -> Type -> Type
MinHeap n a = LeftistHeap n a

public export
MaxHeap : Nat -> Type -> Type
MaxHeap n a = LeftistHeap n (Down a)

public export
insertMin : Ord a => a -> MinHeap n a -> MinHeap (S n) a
insertMin = insert

public export
insertMax : Ord a => a -> MaxHeap n a -> MaxHeap (S n) a
insertMax x h = insert (MkDown x) h

public export
popMin : Ord a => MinHeap (S k) a -> (a, MinHeap k a)
popMin h = (findMin h, deleteMin h)

public export
popMax : Ord a => MaxHeap (S k) a -> (a, MaxHeap k a)
popMax h =
  let (MkDown x) = findMin h
  in (x, deleteMin h)
