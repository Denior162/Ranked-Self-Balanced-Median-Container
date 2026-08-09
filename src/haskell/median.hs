import Data.Ord (Down(..))

data LeftistHeap a = Empty | Node Int a (LeftistHeap a) (LeftistHeap a) deriving (Show)

rank :: LeftistHeap a -> Int
rank Empty = 0
rank (Node r _ _ _) = r

makeNode :: a -> LeftistHeap a -> LeftistHeap a -> LeftistHeap a
makeNode x l r =
  if rank l >= rank r
     then Node (rank r + 1) x l r
     else Node (rank l + 1) x r l


merge :: Ord a => LeftistHeap a -> LeftistHeap a -> LeftistHeap a
merge Empty h2 = h2
merge h1 Empty = h1
merge h1@(Node _ x l1 r1) h2@(Node _ y l2 r2) =
  if x <= y
     then makeNode x l1 (merge r1 h2)
     else makeNode y l2 (merge h1 r2)
     
insert :: Ord a => a -> LeftistHeap a -> LeftistHeap a
insert x h = merge (Node 1 x Empty Empty) h

extract :: LeftistHeap a -> Maybe a
extract Empty = Nothing
extract (Node _ x _ _) = Just x

deleteMin :: Ord a => LeftistHeap a -> LeftistHeap a
deleteMin Empty = Empty
deleteMin (Node _ _ l r) = merge l r

newtype MinHeap a = MinHeap (LeftistHeap a) deriving (Show)
newtype MaxHeap a = MaxHeap (LeftistHeap (Down a)) deriving (Show)

insertMin :: Ord a => a -> MinHeap a -> MinHeap a
insertMin x (MinHeap h) = MinHeap (insert x h)

insertMax :: Ord a => a -> MaxHeap a -> MaxHeap a
insertMax x (MaxHeap h) = MaxHeap (insert (Down x) h)

popMin :: Ord a => MinHeap a -> Maybe (a, MinHeap a)
popMin (MinHeap h) = case extract h of
  Just x  -> Just (x, MinHeap (deleteMin h))
  Nothing -> Nothing

popMax :: Ord a => MaxHeap a -> Maybe (a, MaxHeap a)
popMax (MaxHeap h) = case extract h of
  Just (Down x) -> Just (x, MaxHeap (deleteMin h))
  Nothing       -> Nothing


data MedianTree a = Empt | Root {
    leftSize  :: Int,
    left      :: MaxHeap a,
    median    :: a,
    rightSize :: Int,
    right     :: MinHeap a
} deriving (Show)  

balance :: Ord a => MedianTree a -> MedianTree a
balance Empt = Empt
balance root@(Root lSize l m rSize r)
  | lSize - rSize > 1 = case popMax l of
      Just (newM, newL) -> Root (lSize - 1) newL newM (rSize + 1) (insertMin m r)
      Nothing           -> root
  | rSize - lSize > 1 = case popMin r of
      Just (newM, newR) -> Root (lSize + 1) (insertMax m l) newM (rSize - 1) newR
      Nothing           -> root
  | otherwise = root

insertMedian :: Ord a => a -> MedianTree a -> MedianTree a
insertMedian item Empt = Root 0 (MaxHeap Empty) item 0 (MinHeap Empty)
insertMedian x (Root lSize l m rSize r)
  | x >= m    = balance $ Root lSize l m (rSize + 1) (insertMin x r)
  | otherwise = balance $ Root (lSize + 1) (insertMax x l) m rSize r

getMedian :: MedianTree a -> Maybe a
getMedian Empt = Nothing
getMedian (Root _ _ m _ _) = Just m

fromList :: Ord a => [a] -> MedianTree a
fromList = foldl (flip insertMedian) Empt

main :: IO ()
main = do
    let nums = [5, 15, 1, 3, 20, 7, 9, 10, 11]
    let tree = fromList nums
    
    putStrLn $ "Вставлены элементы: " ++ show nums
    putStrLn $ "Текущая медиана: " ++ show (getMedian tree)
