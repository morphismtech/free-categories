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
  ( QFunctor (..)
  , QPointed (..)
  , QFoldable (..)
  , QTraversable (..)
  , QMonad (..)
  ) where

import Control.Category
import Data.Quiver
import Prelude hiding (id, (.))

{- | An endfunctor of quivers.

prop> qmap id = id
prop> qmap (g . f) = qmap g . qmap f
-}
class QFunctor c where
  qmap :: (forall x y. p x y -> q x y) -> c p x y -> c q x y
instance QFunctor (ProductQ p) where qmap f (ProductQ p q) = ProductQ p (f q)
instance QFunctor (HomQ p) where qmap g (HomQ f) = HomQ (g . f)
instance Functor t => QFunctor (ApQ t) where qmap f (ApQ t) = ApQ (f <$> t)
instance QFunctor OpQ where qmap f = OpQ . f . getOpQ
instance QFunctor IsoQ where qmap f (IsoQ u d) = IsoQ (f u) (f d)
instance QFunctor IQ where qmap f = IQ . f . getIQ
instance QFunctor (ComposeQ p) where qmap f (ComposeQ p q) = ComposeQ p (f q)
instance QFunctor (LeftQ p) where qmap g (LeftQ f) = LeftQ (g . f)
instance QFunctor (RightQ p) where qmap g (RightQ f) = RightQ (g . f)

{- | Embed a single quiver arrow with `qsingle`.-}
class QFunctor c => QPointed c where qsingle :: p x y -> c p x y
instance QPointed (HomQ p) where qsingle q = HomQ (const q)
instance Applicative t => QPointed (ApQ t) where qsingle = ApQ . pure
instance QPointed IQ where qsingle = IQ
instance Category p => QPointed (ComposeQ p) where qsingle = ComposeQ id

{- | Generalizing `Foldable` from `Monoid`s to `Category`s.

prop> qmap f = qfoldMap (qsingle . f)
-}
class QFunctor c => QFoldable c where
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
  qfoldr (?) q c = getRightQ (qfoldMap (\ x -> RightQ (\ y -> x ? y)) c) q
  {- | Left-associative fold of a structure.

  In the case of `Control.Category.Free.Path`s,
  `qfoldl`, when applied to a binary operator,
  a starting value, and a `Control.Category.Free.Path`,
  reduces the `Control.Category.Free.Path` using the binary operator,
  from left to right:

  prop> qfoldl (?) q (p1 :>> p2 :>> ... :>> pn :>> Done) == (... ((q ? p1) ? p2) ? ...) ? pn
  -}
  qfoldl :: (forall x y z . q x y -> p y z -> q x z) -> q x y -> c p y z -> q x z
  qfoldl (?) q c = getLeftQ (qfoldMap (\ x -> LeftQ (\ y -> y ? x)) c) q
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
  qtraverse_ f = getApQ . qfoldMap (ApQ . f)
instance QFoldable (ProductQ p) where qfoldMap f (ProductQ _ q) = f q
instance QFoldable IQ where qfoldMap f (IQ c) = f c

{- | Generalizing `Traversable` to quivers.-}
class QFoldable c => QTraversable c where
  {- | Map each element of a structure to an `Applicative` on a quiver,
  evaluate from left to right, and collect the results.-}
  qtraverse
    :: Applicative m
    => (forall x y. p x y -> m (q x y)) -> c p x y -> m (c q x y)
instance QTraversable (ProductQ p) where
  qtraverse f (ProductQ p q) = ProductQ p <$> f q
instance QTraversable IQ where qtraverse f (IQ c) = IQ <$> f c

{- | Generalize `Monad` to quivers.

Associativity and left and right identity laws hold.

prop> qjoin . qjoin = qjoin . qmap qjoin
prop> qjoin . qsingle = id
prop> qjoin . qmap qsingle = id

The functions `qbind` and `qjoin` are related as

prop> qjoin = qbind id
prop> qbind f p = qjoin (qmap f p)
-}
class (QFunctor c, QPointed c) => QMonad c where
  qjoin :: c (c p) x y -> c p x y
  qjoin = qbind id
  qbind :: (forall x y. p x y -> c q x y) -> c p x y -> c q x y
  qbind f p = qjoin (qmap f p)
  {-# MINIMAL qjoin | qbind #-}
instance QMonad (HomQ p) where
  qjoin (HomQ q) = HomQ (\p -> getHomQ (q p) p)
instance Monad t => QMonad (ApQ t) where
  qbind f (ApQ t) = ApQ $ do
    p <- t
    getApQ $ f p
instance QMonad IQ where qjoin = getIQ
instance Category p => QMonad (ComposeQ p) where
  qjoin (ComposeQ yz (ComposeQ xy q)) = ComposeQ (yz . xy) q
