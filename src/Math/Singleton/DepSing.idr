module Math.Singleton.DepSing

%default total

||| A dependently typed singleton primitive.
||| Tracks coordinate element `x` at the type level.
public export
data DepSing : (a : Type) -> a -> Type where
  MkDepSing : (x : a) -> DepSing a x
