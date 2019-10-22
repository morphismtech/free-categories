{-|
Module: Data.Quiver
Description: free categories
Copyright: (c) Eitan Chatav, 2019
Maintainer: eitan@morphism.tech
Stability: experimental

-}

{-# LANGUAGE
    GADTs
  , PolyKinds
  , QuantifiedConstraints
  , RankNTypes
  , StandaloneDeriving
#-}

module Data.Quiver
  ( KQ (..)
  , ProductQ (..)
  , swapQ
  , Quiver (..)
  , ApQ (..)
  , OpQ (..)
  , IsoQ (..)
  , IQ (..)
  , ReflQ (..)
  , ComposeQ (..)
  , ExtendQ (..)
  , LiftQ (..)
  ) where

import Control.Category
import Control.Monad (join)
import Prelude hiding (id, (.))

{- | Turn a `Monoid` into a `Category`,
used in the default definition of `ctoMonoid`.-}
newtype KQ r x y = KQ {getKQ :: r} deriving (Eq, Ord, Show)
instance (Semigroup m, x ~ y) => Semigroup (KQ m x y) where
  KQ f <> KQ g = KQ (f <> g)
instance (Monoid m, x ~ y) => Monoid (KQ m x y) where mempty = id
instance Monoid m => Category (KQ m) where
  id = KQ mempty
  KQ g . KQ f = KQ (f <> g)

{- | Product of quivers.-}
data ProductQ p q x y = ProductQ
  { fstQ :: p x y
  , sndQ :: q x y
  } deriving (Eq, Ord, Show)
instance (Category p, Category q, x ~ y)
  => Semigroup (ProductQ p q x y) where (<>) = (>>>)
instance (Category p, Category q, x ~ y)
  => Monoid (ProductQ p q x y) where mempty = id
instance (Category p, Category q) => Category (ProductQ p q) where
  id = ProductQ id id
  ProductQ pyz qyz . ProductQ pxy qxy = ProductQ (pyz . pxy) (qyz . qxy)

{- | Symmetry of `ProductQ`.-}
swapQ :: ProductQ p q x y -> ProductQ q p x y
swapQ (ProductQ p q) = ProductQ q p

{- | Morphism components of quivers.

Quivers form a Cartesian closed category with
  * product `ProductQ`
  * unit `KQ ()`
  * internal hom `Quiver`
-}
newtype Quiver p q x y = Quiver { getQuiver :: p x y -> q x y }

{- | Turn an `Applicative` over a `Category` into a `Category`,
used in the default definition of `ctraverse_`.-}
newtype ApQ m c x y = ApQ {getApQ :: m (c x y)} deriving (Eq, Ord, Show)
instance (Applicative m, Category c, x ~ y)
  => Semigroup (ApQ m c x y) where (<>) = (>>>)
instance (Applicative m, Category c, x ~ y)
  => Monoid (ApQ m c x y) where mempty = id
instance (Applicative m, Category c) => Category (ApQ m c) where
  id = ApQ (pure id)
  ApQ g . ApQ f = ApQ ((.) <$> g <*> f)

{- | Reverse all the arrows in a quiver.-}
newtype OpQ c x y = OpQ {getOpQ :: c y x} deriving (Eq, Ord, Show)
instance (Category c, x ~ y) => Semigroup (OpQ c x y) where (<>) = (>>>)
instance (Category c, x ~ y) => Monoid (OpQ c x y) where mempty = id
instance Category c => Category (OpQ c) where
  id = OpQ id
  OpQ g . OpQ f = OpQ (f . g)

{- | Turn all arrows in a quiver into bidirectional edges.-}
data IsoQ c x y = IsoQ
  { up :: c x y
  , down :: c y x
  } deriving (Eq, Ord, Show)
instance (Category c, x ~ y) => Semigroup (IsoQ c x y) where (<>) = (>>>)
instance (Category c, x ~ y) => Monoid (IsoQ c x y) where mempty = id
instance Category c => Category (IsoQ c) where
  id = IsoQ id id
  (IsoQ yz zy) . (IsoQ xy yx) = IsoQ (yz . xy) (yx . zy)

{- | The identity functor on quivers. -}
newtype IQ c x y = IQ {getIQ :: c x y} deriving (Eq, Ord, Show)
instance (Category c, x ~ y) => Semigroup (IQ c x y) where (<>) = (>>>)
instance (Category c, x ~ y) => Monoid (IQ c x y) where mempty = id
instance Category c => Category (IQ c) where
  id = IQ id
  IQ g . IQ f = IQ (g . f)

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

{- | Compose quivers along matching source and target. -}
data ComposeQ p q x z = forall y. ComposeQ (p y z) (q x y)
deriving instance (forall x y. (Show (p x y), Show (q x y)))
  => Show (ComposeQ p q x y)
instance (Category p, p ~ q, x ~ y)
  => Semigroup (ComposeQ p q x y) where (<>) = (>>>)
instance (Category p, p ~ q, x ~ y)
  => Monoid (ComposeQ p q x y) where mempty = id
instance (Category p, p ~ q) => Category (ComposeQ p q) where
  id = ComposeQ id id
  ComposeQ pyz qxy . ComposeQ pwx qvw = ComposeQ (pyz . qxy) (pwx . qvw)

{- | The left internal hom of `ComposeQ`.-}
newtype ExtendQ p q x y = ExtendQ {getExtendQ :: forall w. p w x -> q w y}
instance (p ~ q, x ~ y) => Semigroup (ExtendQ p q x y) where (<>) = (>>>)
instance (p ~ q, x ~ y) => Monoid (ExtendQ p q x y) where mempty = id
instance p ~ q => Category (ExtendQ p q) where
  id = ExtendQ id
  ExtendQ g . ExtendQ f = ExtendQ (g . f)

{- | The right internal hom of `ComposeQ`.-}
newtype LiftQ p q x y = LiftQ {getLiftQ :: forall z. p y z -> q x z}
instance (p ~ q, x ~ y) => Semigroup (LiftQ p q x y) where (<>) = (>>>)
instance (p ~ q, x ~ y) => Monoid (LiftQ p q x y) where mempty = id
instance p ~ q => Category (LiftQ p q) where
  id = LiftQ id
  LiftQ f . LiftQ g = LiftQ (g . f)