# Dependent pattern matching

Below are three exercise on the notion of views and dependent pattern matching.  They were suggested by David Christiansen.

## Snoc lists 

/Problem:/ Implement snoc lists as a view on ordinary lists.

An ordinary list is either Nil or has the form `x :: xs` (by definition).  In order to view a list as a snoc list, when the list is not `Nil`, we need to be able to say `xs` has the form `ys ++ [y]`.  In the view below, if there is a value of `SnocList xs` constructed by `Snoc s y` where `s : SnocList l` then `xs = l ++ [y]` and we will be able to use this for pattern matching.

> data SnocList : List a -> Type where
>   Snoc : SnocList xs -> (x : a) -> SnocList (xs ++ [x]) 
>   Empty : SnocList Nil
>
> snocList : (l : List a) -> SnocList l
> snocList []  = Empty
> snocList (x :: xs) with (snocList xs)

In the `with` block we can do something very interesting.  Whatever `snocList xs` is, it has the type `SnocList xs`.  There are two possible ways to construct such a value.  Matching on one or the other constructor for SnocList implies that xs has a certain form.  In this case, matching Empty implies that xs = [] and matching on `Snoc s y` /implies/ that `xs = l ++ [y]`.  So on the left side of the `|`, we can rewrite xs using these patterns.

>   snocList (x :: [])          | Empty    = Snoc Empty x 
>   snocList (x :: (ys ++ [y])) | Snoc s y = Snoc (snocList $ x :: ys) y

We can use the snoc list view to define a (non-total) `last` function as well as `toList` that forgets the view.

> data NonemptySnoc : SnocList l -> Type where
>   IsNonemptySnoc : NonemptySnoc (Snoc ys y)
>
> last : {l : List a} -> (s : SnocList l) -> {auto ok : NonemptySnoc s} -> a
> last (Snoc _ y) = y
>
> toList : {l : List a} -> SnocList l -> List a 
> toList {l} _ = l

## List rotation

/Problem:/ Implement a function which rotates a list some number of positions to the left.

The type signature and one case are totally straightforward.

> rot : Nat -> List a -> List a
> rot Z xs = xs 

Now to define `rot (S k) xs` it would be nice if we could write `xs = ys ++ [y]` and recurse with `rot k (y :: ys)` (or see that `xs = []`).  This is exactly what a with block does:

> rot (S k) xs with (snocList xs)
>   rot (S k) []          | Empty    = []
>   rot (S k) (ys ++ [y]) | Snoc _ y = rot k (y :: ys)

## Comparison for Nats

/Problem:/  Define a view `Cmp k n` for comparing Nats.  (Hint: Give it three constructors LT, EQ, GT.)  

The view is clear:

> data Cmp : Nat -> Nat -> Type where
>   LT : Cmp k (k + S n)
>   EQ : Cmp k k
>   GT : Cmp (k + S n) k

We need to define the covering function.  The type signature is straightforward as are some of the cases.

> cmp : (x,y : Nat) -> Cmp x y
> cmp Z Z = EQ
> cmp Z (S k) = LT
> cmp (S k) Z = GT

So how do we implement `cmp (S k) (S n)`.  Is there a function `helper : Cmp k n -> Cmp (S k) (S n)`?  To define `helper x` we should be able to simply pattern match on `x`.

> cmp (S k) (S n) = helper $ cmp k n where
>   helper : Cmp k n -> Cmp (S k) (S n)
>   helper x = 
>       case x of
>           LT => LT
>           EQ => EQ
>           GT => GT

Indeed, it works!  
