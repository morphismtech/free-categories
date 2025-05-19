{-|
Module: Data.Quiver.Functor
Description: free categories
Copyright: (c) Eitan Chatav, 2019
Maintainer: eitan@morphism.tech
Stability: experimental

Consider the category of Haskell quivers with

* objects are types of higher kind
  * @p :: k -> k -> Type@
* morphisms are terms of @RankNType@,
  * @forall x y. p x y -> q x y@
* identity is `id`
* composition is `.`

There is a natural hierarchy of typeclasses for
endofunctors of the category of Haskell quivers,
analagous to that for Haskell types.
-}

{-# LANGUAGE
    PolyKinds
  , RankNTypes
#-}

module Data.Quiver.Functor
  ( QFoldable (..)
  , QTraversable (..)
  ) where

import Control.Category
import Data.Bifunctor.Functor
import Data.Bifunctor.Product
import Data.Profunctor.Cayley
import Data.Profunctor.Composition
import Data.Profunctor.Ran
import Data.Quiver
import Prelude hiding (id, (.))

instance Functor t => BifunctorFunctor (Cayley t) where bifmap f (Cayley t) = Cayley (f <$> t)
instance BifunctorFunctor OpQ where bifmap f = OpQ . f . getOpQ
instance BifunctorFunctor IsoQ where bifmap f (IsoQ u d) = IsoQ (f u) (f d)
instance BifunctorFunctor IQ where bifmap f = IQ . f . getIQ
instance BifunctorFunctor (Procompose p) where bifmap f (Procompose p q) = Procompose p (f q)
instance BifunctorFunctor (Ran p) where bifmap g (Ran f) = Ran (g . f)
instance BifunctorFunctor (Rift p) where bifmap g (Rift f) = Rift (g . f)

{- | Generalizing `Foldable` from `Monoid`s to `Category`s.

prop> bifmap f = qfoldMap (bireturn . f)
-}
class BifunctorFunctor c => QFoldable c where
  {- | Map each element of the structure to a `Category`,
  and combine the results.-}
  qfoldMap :: Category q => (forall x y. p x y -> q x y) -> c p x y -> q x y
  {- | Combine the elements of a structure using a `Category`.-}
  qfold :: Category q => c q x y -> q x y
  qfold = qfoldMap id
  {- | Right-associative fold of a structure.

  In the case of `Control.Category.Free.Path`s,
  `qfoldr`, when applied to a binary operator,
  a starting value, and a `Control.Category.Free.Path`,
  reduces the `Control.Category.Free.Path` using the binary operator,
  from right to left:

  prop> qfoldr (?) q (p1 :>> p2 :>> ... :>> pn :>> Done) == p1 ? (p2 ? ... (pn ? q) ...)
  -}
  qfoldr :: (forall x y z . p x y -> q y z -> q x z) -> q y z -> c p x y -> q x z
  qfoldr (?) q c = runRift (qfoldMap (\ x -> Rift (\ y -> x ? y)) c) q
  {- | Left-associative fold of a structure.

  In the case of `Control.Category.Free.Path`s,
  `qfoldl`, when applied to a binary operator,
  a starting value, and a `Control.Category.Free.Path`,
  reduces the `Control.Category.Free.Path` using the binary operator,
  from left to right:

  prop> qfoldl (?) q (p1 :>> p2 :>> ... :>> pn :>> Done) == (... ((q ? p1) ? p2) ? ...) ? pn
  -}
  qfoldl :: (forall x y z . q x y -> p y z -> q x z) -> q x y -> c p y z -> q x z
  qfoldl (?) q c = runRan (qfoldMap (\ x -> Ran (\ y -> y ? x)) c) q
  {- | Map each element of the structure to a `Monoid`,
  and combine the results.-}
  qtoMonoid :: Monoid m => (forall x y. p x y -> m) -> c p x y -> m
  qtoMonoid f = getKQ . qfoldMap (KQ . f)
  {- | Map each element of the structure, and combine the results in a list.-}
  qtoList :: (forall x y. p x y -> a) -> c p x y -> [a]
  qtoList f = qtoMonoid (pure . f)
  {- | Map each element of a structure to an `Applicative` on a `Category`,
  evaluate from left to right, and combine the results.-}
  qtraverse_
    :: (Applicative m, Category q)
    => (forall x y. p x y -> m (q x y)) -> c p x y -> m (q x y)
  qtraverse_ f = runCayley . qfoldMap (Cayley . f)
instance QFoldable (Product p) where qfoldMap f (Pair _ q) = f q
instance QFoldable IQ where qfoldMap f (IQ c) = f c

{- | Generalizing `Traversable` to quivers.-}
class QFoldable c => QTraversable c where
  {- | Map each element of a structure to an `Applicative` on a quiver,
  evaluate from left to right, and collect the results.-}
  qtraverse
    :: Applicative m
    => (forall x y. p x y -> m (q x y)) -> c p x y -> m (c q x y)
instance QTraversable (Product p) where
  qtraverse f (Pair p q) = Pair p <$> f q
instance QTraversable IQ where qtraverse f (IQ c) = IQ <$> f c

instance BifunctorMonad (HomQ p) where
  bijoin (HomQ q) = HomQ (\p -> getHomQ (q p) p)
  bireturn q = HomQ (const q)
instance Monad t => BifunctorMonad (Cayley t) where
  bibind f (Cayley t) = Cayley $ do
    p <- t
    runCayley $ f p
  bireturn = Cayley . pure
instance BifunctorMonad IQ where
  bijoin = getIQ
  bireturn = IQ
instance Category p => BifunctorMonad (Procompose p) where
  bijoin (Procompose yz (Procompose xy q)) = Procompose (yz . xy) q
  bireturn = Procompose id
