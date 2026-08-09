import LeftistHeap
import BMedianContainer

public export
main : IO ()
main = do
    let nums = [5, 15, 1, 3, 20, 7, 9, 10, 11]

    case fromList nums of
         Nothing => putStrLn "The list was empty, no median tree created."
         Just tree => do
             putStrLn $ "Inserted elements: " ++ show nums
             putStrLn $ "Current median: " ++ show (getAnyMedian tree)

             let (popped, restTree) = popMedian tree
             putStrLn $ "Popped median: " ++ show popped

             case restTree of
                  Nothing => putStrLn "Tree is now completely empty."
                  Just rt => putStrLn $ "New median after pop: " ++ show (getAnyMedian rt)
