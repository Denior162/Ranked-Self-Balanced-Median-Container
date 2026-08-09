module BMedianContainer

import LeftistHeap
import Data.Nat

public export
data BalanceState : Nat -> Nat -> Type where
  Equal  : BalanceState n n
  LHeavy : BalanceState (S n) n
  RHeavy : BalanceState n (S n)


public export
data MedianTree : (l : Nat) -> (r : Nat) -> Type -> Type where
  Root : (l : Nat) -> MaxHeap l a
      -> a
      -> (r : Nat) -> MinHeap r a
      -> BalanceState l r
      -> MedianTree l r a

public export
getMedian : MedianTree l r a -> a
getMedian (Root _ _ m _ _ _) = m

public export
Show a => Show (Down a) where
  show (MkDown x) = show x

public export
Show a => Show (MedianTree l r a) where
  show (Root l left m r right _) =
    "Root " ++ show l ++ " (" ++ show left ++ ") " ++ show m ++ " " ++ show r ++ " (" ++ show right ++ ")"

public export
rebalanceLeft : Ord a => (n : Nat) -> MaxHeap (S (S n)) a -> a -> MinHeap n a -> MedianTree (S n) (S n) a
rebalanceLeft n l m r =
  let (newM, newL) = popMax l
  in Root (S n) newL newM (S n) (insertMin m r) Equal

public export
rebalanceRight : Ord a => (n : Nat) -> MaxHeap n a -> a -> MinHeap (S (S n)) a -> MedianTree (S n) (S n) a
rebalanceRight n l m r =
  let (newM, newR) = popMin r
  in Root (S n) (insertMax m l) newM (S n) newR Equal
  
public export
data AnyTree : Type -> Type where
  MkAny : MedianTree l r a -> AnyTree a


public export
singleton : a -> AnyTree a
singleton x = MkAny (Root 0 Empty x 0 Empty Equal)

public export
getAnyMedian : AnyTree a -> a
getAnyMedian (MkAny t) = getMedian t

insertLeft : Ord a => a -> (l : Nat) -> MaxHeap l a -> a -> (r : Nat) -> MinHeap r a -> BalanceState l r -> AnyTree a
insertLeft x n left m n right Equal = 
  MkAny (Root (S n) (insertMax x left) m n right LHeavy)
insertLeft x (S n) left m n right LHeavy = 
  MkAny (rebalanceLeft n (insertMax x left) m right)
insertLeft x n left m (S n) right RHeavy = 
  MkAny (Root (S n) (insertMax x left) m (S n) right Equal)

insertRight : Ord a => a -> (l : Nat) -> MaxHeap l a -> a -> (r : Nat) -> MinHeap r a -> BalanceState l r -> AnyTree a
insertRight x n left m n right Equal = 
  MkAny (Root n left m (S n) (insertMin x right) RHeavy)
insertRight x (S n) left m n right LHeavy = 
  MkAny (Root (S n) left m (S n) (insertMin x right) Equal)
insertRight x n left m (S n) right RHeavy = 
  MkAny (rebalanceRight n left m (insertMin x right))

public export
insertMedian : Ord a => a -> AnyTree a -> AnyTree a
insertMedian x (MkAny (Root l left m r right state)) =
  if x < m
     then insertLeft x l left m r right state
     else insertRight x l left m r right state


public export
popMedian : Ord a => AnyTree a -> (a, Maybe (AnyTree a))
popMedian (MkAny (Root Z _ m Z _ Equal)) = (m, Nothing)
popMedian (MkAny (Root (S k) left m k right LHeavy)) = 
  let (newM, newL) = popMax left
  in (m, Just (MkAny (Root k newL newM k right Equal)))
popMedian (MkAny (Root k left m (S k) right RHeavy)) = 
  let (newM, newR) = popMin right
  in (m, Just (MkAny (Root k left newM k newR Equal)))
popMedian (MkAny (Root (S k) left m (S k) right Equal)) =
  let (newM, newL) = popMax left
  in (m, Just (MkAny (Root k newL newM (S k) right RHeavy)))

public export
fromList : Ord a => List a -> Maybe (AnyTree a)
fromList [] = Nothing
fromList (x :: xs) = Just (foldl (flip insertMedian) (singleton x) xs)