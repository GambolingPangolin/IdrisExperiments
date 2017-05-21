||| This module provides the SortedList type, representing lists that are 
||| guaranteed to be in ascending order.
module SortedList 

import Data.So

mutual
  export
  data SortedList : Type -> Type where
    Nil : SortedList a

    ||| @ x is the element to add
    ||| @ xs is the sorted list to be extended
    ||| We also include a proof that the element x is no larger than the other 
    ||| elements in the list
    Cons : (Ord a) => 
           (x : a) ->
           (xs : SortedList a) ->
           So (noMoreThanH x xs) -> 
           SortedList a

  export
  noMoreThanH : Ord a => a -> SortedList a -> Bool 
  noMoreThanH _ Nil = True
  noMoreThanH x (Cons y _ _) = x <= y 


export
Show a => Show (SortedList a) where
  show Nil = "Sorted[]"
  show (Cons x xs _) = "Sorted[" ++ show x ++ show' xs ++ "]" where
    show' Nil = ""
    show' (Cons y ys _) = ", " ++ show y ++ show' ys

||| Insert an element into a sorted list at the first possible position.
export
insert : Ord a => 
         a -> 
         SortedList a -> 
         SortedList a

insert x Nil = Cons x Nil Oh
insert x xs = 
  case choose (noMoreThanH x xs) of
    Left res => Cons x xs res
    Right _ =>
      let Cons y ys _ = xs in
      insert y (insert x ys)

||| Given two SortedList's, combine them into a SortedList.  
export
merge : Ord a => 
        SortedList a -> 
        SortedList a -> 
        SortedList a

merge Nil xs = xs
merge xs Nil = xs
merge (Cons x xs _) (Cons y ys _) = insert x $ insert y $ merge xs ys

||| Given a list, sort it and generate a SortedList by itereatively inserting 
||| elements.  O(n^2)
slowSort : Ord a => List a -> SortedList a
slowSort = foldl (flip insert) Nil
