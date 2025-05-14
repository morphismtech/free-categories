{-|
Module: Data.Quiver
Description: free categories
Copyright: (c) Eitan Chatav, 2019
Maintainer: eitan@morphism.tech
Stability: experimental

A [quiver](https://ncatlab.org/nlab/show/quiver)
is a directed graph where loops and multiple arrows
between vertices are allowed, a multidigraph. A Haskell quiver
is a higher kinded type,

@p :: k -> k -> Type@

  * where vertices are types @x :: k@,
  * and arrows from @x@ to @y@ are terms @p :: p x y@.

Many Haskell typeclasses are constraints on quivers, such as
`Category`, `Data.Bifunctor.Bifunctor`,
@Profunctor@, and `Control.Arrow.Arrow`.
-}

{-# LANGUAGE
    GADTs
  , PolyKinds
  , QuantifiedConstraints
  , RankNTypes
  , StandaloneDeriving
  , TypeOperators
#-}

module Data.Quiver
  ( IQ (..)
  , OpQ (..)
  , IsoQ (..)
  , KQ (..)
  , HomQ (..)
  , ReflQ (..)
  ) where

import Control.Category
import Control.Monad (join)
import Prelude hiding (id, (.))

{- | The identity functor on quivers. -}
newtype IQ c x y = IQ {getIQ :: c x y} deriving (Eq, Ord, Show)
instance (Category c, x ~ y) => Semigroup (IQ c x y) where (<>) = (>>>)
instance (Category c, x ~ y) => Monoid (IQ c x y) where mempty = id
instance Category c => Category (IQ c) where
  id = IQ id
  IQ g . IQ f = IQ (g . f)

{- | Reverse all the arrows in a quiver.-}
newtype OpQ c x y = OpQ {getOpQ :: c y x} deriving (Eq, Ord, Show)
instance (Category c, x ~ y) => Semigroup (OpQ c x y) where (<>) = (>>>)
instance (Category c, x ~ y) => Monoid (OpQ c x y) where mempty = id
instance Category c => Category (OpQ c) where
  id = OpQ id
  OpQ g . OpQ f = OpQ (f . g)

{- | Arrows of `IsoQ` are bidirectional edges.-}
data IsoQ c x y = IsoQ
  { up :: c x y
  , down :: c y x
  } deriving (Eq, Ord, Show)
instance (Category c, x ~ y) => Semigroup (IsoQ c x y) where (<>) = (>>>)
instance (Category c, x ~ y) => Monoid (IsoQ c x y) where mempty = id
instance Category c => Category (IsoQ c) where
  id = IsoQ id id
  (IsoQ yz zy) . (IsoQ xy yx) = IsoQ (yz . xy) (yx . zy)

{- | The constant quiver.

@KQ ()@ is an [indiscrete category]
(https://ncatlab.org/nlab/show/indiscrete+category).
-}
newtype KQ r x y = KQ {getKQ :: r} deriving (Eq, Ord, Show)
instance (Semigroup m, x ~ y) => Semigroup (KQ m x y) where
  KQ f <> KQ g = KQ (f <> g)
instance (Monoid m, x ~ y) => Monoid (KQ m x y) where mempty = id
instance Monoid m => Category (KQ m) where
  id = KQ mempty
  KQ g . KQ f = KQ (f <> g)

{- | The quiver of quiver morphisms, `HomQ` is the [internal hom]
(https://ncatlab.org/nlab/show/internal+hom)
of the category of quivers.-}
newtype HomQ p q x y = HomQ { getHomQ :: p x y -> q x y }

{- | A term in @ReflQ r x y@ observes the equality @x ~ y@.

@ReflQ ()@ is the [discrete category]
(https://ncatlab.org/nlab/show/discrete+category).
-}
data ReflQ r x y where ReflQ :: r -> ReflQ r x x
deriving instance Show r => Show (ReflQ r x y)
deriving instance Eq r => Eq (ReflQ r x y)
deriving instance Ord r => Ord (ReflQ r x y)
instance Monoid m => Category (ReflQ m) where
  id = ReflQ mempty
  ReflQ yz . ReflQ xy = ReflQ (xy <> yz)
