module Math.Multiset

import Data.List
import Data.Linear
import Math.Interfaces

%default total

------------------------------------------------------------------------
-- 1. MULTISET DATA CONSTRUCTORS
------------------------------------------------------------------------

||| A Run-Length Encoded (RLE) Multiset optimized for high-generation Box Arithmetic.
public export
data Multiset : (c : Type) -> (a : Type) -> Type where
  ZeroM : Multiset c a
  AddM : a -> c -> Multiset c a -> Multiset c a

||| Strictly positive, non-empty Multiset (guarantees at least one element)
public export
data Multiset1 : (c : Type) -> (a : Type) -> Type where
  BaseM : a -> c -> Multiset1 c a
  AddM1 : a -> c -> Multiset1 c a -> Multiset1 c a

public export
insertItem : (Eq a, Num c, Eq c) => a -> c -> Multiset c a -> Multiset c a
insertItem k v ZeroM = if v == 0 then ZeroM else AddM k v ZeroM
insertItem k v (AddM k' v' rest) =
  if k == k' then
    let newV = v + v'
    in if newV == 0 then rest else AddM k newV rest
  else AddM k' v' (insertItem k v rest)

public export
addMultiset : Multiset c a -> Multiset c a -> Multiset c a
addMultiset ZeroM ys = ys
addMultiset (AddM x c xs) ys = AddM x c (addMultiset xs ys)

public export total
multisetToUrList : (1 _ : Multiset c a) -> Ur (List (a, c))
multisetToUrList ZeroM = MkUr []
multisetToUrList (AddM k v rest) =
  let MkUr listRest = multisetToUrList rest
  in MkUr ((k, v) :: listRest)

public export total
prependListToMultiset : List (a, c) -> (1 ys : Multiset c a) -> Multiset c a
prependListToMultiset [] ys = ys
prependListToMultiset ((k, v) :: xs) ZeroM = AddM k v (prependListToMultiset xs ZeroM)
prependListToMultiset ((k, v) :: xs) (AddM y c ys) = AddM k v (AddM y c (prependListToMultiset xs ys))

public export
laddMultiset : (1 xs : Multiset c a) -> (1 ys : Multiset c a) -> Multiset c a
laddMultiset xs ys =
  let MkUr listX = multisetToUrList xs
  in prependListToMultiset listX ys

public export
mapMultiset : (a -> b) -> Multiset c a -> Multiset c b
mapMultiset f ZeroM = ZeroM
mapMultiset f (AddM x c xs) = AddM (f x) c (mapMultiset f xs)

public export
Functor (Multiset c) where
  map = mapMultiset

public export
Bifunctor Multiset where
  bimap f g ZeroM = ZeroM
  bimap f g (AddM x c xs) = AddM (g x) (f c) (bimap f g xs)

public export
Foldable (Multiset c) where
  foldr f z ZeroM = z
  foldr f z (AddM x _ xs) = f x (foldr f z xs)

  foldMap f ZeroM = neutral
  foldMap f (AddM x _ xs) = f x <+> foldMap f xs

public export
Traversable (Multiset c) where
  traverse f ZeroM = pure ZeroM
  traverse f (AddM x c xs) = [| AddM (f x) (pure c) (traverse f xs) |]

public export
Semigroup (Multiset c a) where
  (<+>) = addMultiset

public export
Monoid (Multiset c a) where
  neutral = ZeroM

public export
scaleMultiset : (Num c, Eq c) => c -> Multiset c a -> Multiset c a
scaleMultiset scalar xs = if scalar == 0 then ZeroM else go xs
  where
    go : Multiset c a -> Multiset c a
    go ZeroM = ZeroM
    go (AddM k v rest) = AddM k (v * scalar) (go rest)

public export
(Num c, Eq c) => Applicative (Multiset c) where
  pure x = AddM x 1 ZeroM

  ZeroM <*> _ = ZeroM
  (AddM f vf fs) <*> xs =
    addMultiset (mapMultiset f (scaleMultiset vf xs)) (fs <*> xs)

public export
(Num c, Eq c) => Monad (Multiset c) where
  ZeroM >>= _ = ZeroM
  (AddM x v xs) >>= f =
    addMultiset (scaleMultiset v (f x)) (xs >>= f)

public export
convolveMultiset : (Semigroup a, Num c, Eq c) => Multiset c a -> Multiset c a -> Multiset c a
convolveMultiset xs ys = [| (<+>) xs ys |]

public export
fiberPushforward : (a -> b) -> Multiset c a -> Multiset c b
fiberPushforward = mapMultiset

||| Intuitive zoomOutMultiset operator: coarse-grains fine micro-multiset tokens to coarse macro-multiset tokens (Technical: fiberPushforward / f_push / f_*).
public export
zoomOutMultiset : (a -> b) -> Multiset c a -> Multiset c b
zoomOutMultiset = fiberPushforward

public export
fiberPullback : (Num c, Eq c) => (b -> List a) -> Multiset c b -> Multiset c a
fiberPullback fiberMap ZeroM = ZeroM
fiberPullback fiberMap (AddM y v ys) =
  let fiberItems = foldr (\x, acc => AddM x v acc) ZeroM (fiberMap y)
  in addMultiset fiberItems (fiberPullback fiberMap ys)

||| Intuitive zoomInMultiset operator: expands coarse macro-multiset tokens to micro-multiset token fibers (Technical: fiberPullback / f_pull / f^*).
public export
zoomInMultiset : (Num c, Eq c) => (b -> List a) -> Multiset c b -> Multiset c a
zoomInMultiset = fiberPullback



public export
annihilateMultiset : (Eq a, Num c, Eq c) => Multiset c a -> Multiset c a
annihilateMultiset xs = go ZeroM xs
  where
    go : Multiset c a -> Multiset c a -> Multiset c a
    go acc ZeroM = acc
    go acc (AddM k v rest) = go (insertItem k v acc) rest

public export
multiplicityAll : (Num c, Abs c) => Multiset c a -> c
multiplicityAll ZeroM = 0
multiplicityAll (AddM x c xs) = abs c + multiplicityAll xs

||| Looks up the total count/multiplicity of element `target` in a `Multiset c a`.
public export
lookupCount : (Eq a, Num c) => a -> Multiset c a -> c
lookupCount target ZeroM = 0
lookupCount target (AddM k v rest) =
  if target == k then v + lookupCount target rest else lookupCount target rest

||| Alias for lookupCount.
public export
multiplicity : (Eq a, Num c) => a -> Multiset c a -> c
multiplicity = lookupCount


public export
negateMultiset : Neg c => Multiset c a -> Multiset c a

negateMultiset ZeroM = ZeroM
negateMultiset (AddM x c xs) = AddM x (-c) (negateMultiset xs)

public export total
lnegateMultiset : Neg c => (1 _ : Multiset c a) -> Multiset c a
lnegateMultiset ZeroM = ZeroM
lnegateMultiset (AddM x c xs) = AddM x (-c) (lnegateMultiset xs)

public export
subMultiset : Neg c => Multiset c a -> Multiset c a -> Multiset c a
subMultiset a b = addMultiset a (negateMultiset b)

public export
lsubMultiset : Neg c => (1 xs : Multiset c a) -> (1 ys : Multiset c a) -> Multiset c a
lsubMultiset xs ys = laddMultiset xs (lnegateMultiset ys)

public export
(Eq a, Neg c, Num c, Eq c) => Eq (Multiset c a) where
  a == b = 
    let res = annihilateMultiset (addMultiset a (negateMultiset b))
    in isEmpty res
    where
      isEmpty : {0 b : Type} -> Multiset c b -> Bool
      isEmpty ZeroM = True
      isEmpty _ = False

export
(Show a, Show c) => Show (Multiset c a) where
  show ZeroM = "[]"
  show xs = "[" ++ showItems xs ++ "]"
    where
      showItems : Multiset c a -> String
      showItems ZeroM = ""
      showItems (AddM k v ZeroM) = "(" ++ show k ++ ", " ++ show v ++ ")"
      showItems (AddM k v rest) = "(" ++ show k ++ ", " ++ show v ++ "), " ++ showItems rest

public export
multisetToList : Multiset c a -> List (a, c)
multisetToList ZeroM = []
multisetToList (AddM k v rest) = (k, v) :: multisetToList rest

public export
fromList : (Eq a, Num c, Eq c) => List (a, c) -> Multiset c a
fromList [] = ZeroM
fromList ((k, v) :: rest) = insertItem k v (fromList rest)

public export total
dupMultiset : (1 _ : Multiset c a) -> (Multiset c a, Multiset c a)
dupMultiset ZeroM = (ZeroM, ZeroM)
dupMultiset (AddM x c xs) =
  let (xs1, xs2) = dupMultiset xs
  in (AddM x c xs1, AddM x c xs2)

public export total
consumeMultiset : (1 _ : Multiset c a) -> ()
consumeMultiset ZeroM = ()
consumeMultiset (AddM x c xs) = consumeMultiset xs

public export total
multisetToListL : (1 _ : Multiset c a) -> LPair (List (a, c)) (Multiset c a)
multisetToListL ZeroM = Builtin.(#) [] ZeroM
multisetToListL (AddM k v rest) =
  let (listRest # restM) = multisetToListL rest
  in Builtin.(#) ((k, v) :: listRest) (AddM k v restM)
