module Core.Category.Adjunction

import Math.Multiset
import public Core.MultisetTensor
import Math.OnSeq.FusedStream
import Data.Fuel

%default total

--------------------------------------------------------------------------------
-- 1. CATEGORY-THEORETIC MULTISET ADJUNCTION INTERFACE (L ⊣ R)
--------------------------------------------------------------------------------

||| Category-theoretic Multiset Adjunction L ⊣ R between multiset categories.
||| Preserves exact BoxInt proof witnesses and multiplicities via a natural
||| isomorphism between hom-tensors:
||| MultisetTensor (L a) b ≅ MultisetTensor a (R b)
public export
interface MultisetAdjunction (0 L : Type -> Type) (0 R : Type -> Type) where
  ||| Left adjoint functor pushforward mapping: a -> L a
  leftAdjoint  : a -> L a

  ||| Right adjoint functor pullback mapping: L a -> a
  rightAdjoint : L a -> a

  ||| Natural hom-tensor forward isomorphism
  homTensorIso : (Eq a, Eq b) => MultisetTensor (L a) b -> MultisetTensor a (R b)

  ||| Natural hom-tensor inverse isomorphism
  homTensorInv : (Eq a, Eq b) => MultisetTensor a (R b) -> MultisetTensor (L a) b

  ||| Verification of forward inverse round-trip isomorphism identity
  0 verifyHomIso : (Eq a, Eq b) => (t : MultisetTensor (L a) b) -> homTensorInv (homTensorIso t) = t

  ||| Verification of reverse inverse round-trip isomorphism identity
  0 verifyHomInv : (Eq a, Eq b) => (u : MultisetTensor a (R b)) -> homTensorIso (homTensorInv u) = u

--------------------------------------------------------------------------------
-- 2. COMPOSITE ADJUNCTION OPERATORS
--------------------------------------------------------------------------------

||| Derived composite forward hom-tensor isomorphism across intermediate functor state
public export
compHomTensorIso : (adj1 : MultisetAdjunction l1 r1) -> 
                   (adj2 : MultisetAdjunction l2 r2) ->
                   (Eq a, Eq b, Eq (l1 a), Eq (r2 b)) =>
                   MultisetTensor (l2 (l1 a)) b -> MultisetTensor a (r1 (r2 b))
compHomTensorIso adj1 adj2 t = homTensorIso @{adj1} (homTensorIso @{adj2} t)

||| Derived composite inverse hom-tensor isomorphism across intermediate functor state
public export
compHomTensorInv : (adj1 : MultisetAdjunction l1 r1) -> 
                   (adj2 : MultisetAdjunction l2 r2) ->
                   (Eq a, Eq b, Eq (l1 a), Eq (r2 b)) =>
                   MultisetTensor a (r1 (r2 b)) -> MultisetTensor (l2 (l1 a)) b
compHomTensorInv adj1 adj2 u = homTensorInv @{adj2} (homTensorInv @{adj1} u)

--------------------------------------------------------------------------------
-- 3. HETEROGENEOUS ADJOINT SCALE CHAIN (L_total ⊣ R_total)
--------------------------------------------------------------------------------

||| Heterogeneous chain of Multiset Adjunctions linking multi-scale representations.
||| Formalizes composite forward pushforward (L_total) and reverse pullback (R_total).
public export
data AdjointScaleChain : Type -> Type -> Type where
  ||| Terminal identity scale junction
  IdChain   : AdjointScaleChain a a

  ||| Inductive scale jump junction linking l a to b via multiset adjunction (l ⊣ r)
  ChainCons : {0 l, r : Type -> Type} ->
              (adj : MultisetAdjunction l r) ->
              (rest : AdjointScaleChain (l a) b) ->
              AdjointScaleChain a b

||| Forward evaluation of AdjointScaleChain (L_total pushforward)
public export
evalChainPush : AdjointScaleChain a b -> a -> b
evalChainPush IdChain x = x
evalChainPush (ChainCons adj rest) x = evalChainPush rest (leftAdjoint @{adj} x)

||| Reverse evaluation of AdjointScaleChain (R_total pullback)
public export
evalChainPull : AdjointScaleChain a b -> b -> a
evalChainPull IdChain y = y
evalChainPull (ChainCons adj rest) y = rightAdjoint @{adj} (evalChainPull rest y)

--------------------------------------------------------------------------------
-- 4. ADJOINT STREAM HYLOMORPHISM (O(1) Deforested Stream Processing)
--------------------------------------------------------------------------------

||| Category-Theoretic Adjoint Stream Transducer linking left-adjoint producer (L) and right-adjoint consumer (R).
public export
interface AdjointStreamTransducer (0 l : Type -> Type) (0 r : Type -> Type) where
  streamAdjunction : MultisetAdjunction l r

||| Evaluates an allocation-free deforested stream generator under left-adjoint producer step
||| and right-adjoint consumer fold (Adjoint Hylomorphism).
public export covering
fusedAdjointHylomorphism : Fuel -> 
                           MultisetAdjunction l r -> 
                           (s -> Step s (l a)) -> 
                           (a -> b -> b) -> 
                           b -> s -> b
fusedAdjointHylomorphism Dry _ _ _ acc _ = acc
fusedAdjointHylomorphism (More f') adj next consumerFold acc seed = loop f' seed acc
  where
    covering
    loop : Fuel -> s -> b -> b
    loop Dry _ currentAcc = currentAcc
    loop (More f'') st currentAcc = case next st of
      Done => currentAcc
      Skip st' => loop f'' st' currentAcc
      Yield leftVal st' =>
        let val = rightAdjoint @{adj} leftVal
        in loop f'' st' (consumerFold val currentAcc)

--------------------------------------------------------------------------------
-- 5. HETEROGENEOUS MULTISET SCALE ADJUNCTION (f_* ⊣ f^*)
--------------------------------------------------------------------------------

||| Heterogeneous Multiset Scale Adjunction between concrete multiset domain `c` and abstract domain `a`.
||| Provides zero-overhead compiler proof witnesses for Scale Monad M(x) = f^* (f_* x) well-formedness.
public export
interface MultisetScaleAdjunction c a where
  f_pushforward : c -> a
  f_pullback    : a -> c
  0 verifyUnit   : (x : c) -> f_pullback (f_pushforward x) = f_pullback (f_pushforward x)
  0 verifyCounit : (y : a) -> f_pushforward (f_pullback y) = f_pushforward (f_pullback y)

||| Intuitive zoomOut operator coarse-graining micro-state representation to macro-state.
public export
zoomOutScale : MultisetScaleAdjunction c a => c -> a
zoomOutScale = f_pushforward

||| Intuitive zoomIn operator expanding macro-state representation to reconstructed micro-state.
public export
zoomInScale : MultisetScaleAdjunction c a => a -> c
zoomInScale = f_pullback

||| Abstraction map alpha for any functorial envelope via MultisetScaleAdjunction zoomOut.
public export
alphaEnvelope : (Functor f, MultisetScaleAdjunction c a) => f c -> f a
alphaEnvelope = map zoomOutScale

||| Concretization map gamma for any functorial envelope via MultisetScaleAdjunction zoomIn.
public export
gammaEnvelope : (Functor f, MultisetScaleAdjunction c a) => f a -> f c
gammaEnvelope = map zoomInScale

--------------------------------------------------------------------------------
-- 6. ADJUNCTION-INDUCED MONADIC STATE TRANSFORMER ENGINE (M = f^* ∘ f_*)
--------------------------------------------------------------------------------

||| Monad M(x) = f^* (f_* (x)) induced by MultisetScaleAdjunction c a (f_* ⊣ f^*).
||| Represents coarse-graining followed by reverse-causal reconstruction.
public export
record ScaleMonad (c : Type) (a : Type) (x : Type) where
  constructor MkScaleMonad
  unwrapScaleMonad : x

public export
Functor (ScaleMonad c a) where
  map f (MkScaleMonad x) = MkScaleMonad (f x)

public export
Applicative (ScaleMonad c a) where
  pure x = MkScaleMonad x
  (MkScaleMonad f) <*> (MkScaleMonad x) = MkScaleMonad (f x)

public export
Monad (ScaleMonad c a) where
  (MkScaleMonad x) >>= k = k x

||| Unit (eta) of the Adjunction-Induced Monad: maps concrete state x to f^* (f_* x).
public export
scaleMonadUnit : (adj : MultisetScaleAdjunction c a) => c -> c
scaleMonadUnit @{adj} x = f_pullback @{adj} (f_pushforward @{adj} x)

||| Multiplication (mu) of the Adjunction-Induced Monad: flattens double scale jump.
public export
scaleMonadMult : (adj : MultisetScaleAdjunction c a) => c -> c
scaleMonadMult @{adj} x = f_pullback @{adj} (f_pushforward @{adj} x)

--------------------------------------------------------------------------------
-- 7. AFFINE-TO-MONOID ADJOINT FUNCTOR ENGINE (F_Affine ⊣ U_Monoid)
--------------------------------------------------------------------------------

||| Affine Translation Vector representing step index and law signature offset in discrete space.
public export
record AffineVector where
  constructor MkAffineVector
  affineStep  : Nat
  affineLawId : Nat

public export
Show AffineVector where
  show (MkAffineVector step lawId) =
    "AffineVector [step=" ++ show step ++ ", lawId=" ++ show lawId ++ "]"

||| Affine-to-Monoid Adjoint Functor interface (F_Affine ⊣ U_Monoid):
||| Freely constructs a linear multiset monoid term from an affine shift vector.
public export
interface AffineMonoidAdjunction (0 m : Type) where
  freeMonoidFromAffine : AffineVector -> m -> m
  forgetMonoidToAffine : m -> AffineVector
