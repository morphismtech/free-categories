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
  , UndecidableInstances
#-}

module Data.Quiver
  ( IQ (..)
  , OpQ (..)
  , IsoQ (..)
  , ApQ (..)
  , IxApQ (..)
  , KQ (..)
  , ProductQ (..)
  , qswap
  , HomQ (..)
  , ReflQ (..)
  , ComposeQ (..)
  , LeftQ (..)
  , RightQ (..)
  ) where

import Control.Category
import Control.Atkey
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

{- | Apply a constructor to the arrows of a quiver.-}
newtype ApQ m c x y = ApQ {getApQ :: m (c x y)} deriving (Eq, Ord, Show)
instance (Applicative m, Category c, x ~ y)
  => Semigroup (ApQ m c x y) where (<>) = (>>>)
instance (Applicative m, Category c, x ~ y)
  => Monoid (ApQ m c x y) where mempty = id
instance (Applicative m, Category c) => Category (ApQ m c) where
  id = ApQ (pure id)
  ApQ g . ApQ f = ApQ ((.) <$> g <*> f)

newtype IxApQ m c x y = IxApQ {getIxApQ :: m x y (c x y)}
deriving instance Eq (m x y (c x y)) => Eq (IxApQ m c x y)
deriving instance Ord (m x y (c x y)) => Ord (IxApQ m c x y)
deriving instance Show (m x y (c x y)) => Show (IxApQ m c x y)
instance (IxApplicative m, Category c, x ~ y)
  => Semigroup (IxApQ m c x y) where (<>) = (>>>)
instance (IxApplicative m, Category c, x ~ y)
  => Monoid (IxApQ m c x y) where mempty = id
instance (IxApplicative m, Category c) => Category (IxApQ m c) where
  id = IxApQ (ipure id)
  IxApQ g . IxApQ f = IxApQ (iliftA2 (flip (.)) f g)

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

{- | [Cartesian monoidal product]
(https://ncatlab.org/nlab/show/cartesian+monoidal+category)
of quivers.-}
data ProductQ p q x y = ProductQ
  { qfst :: p x y
  , qsnd :: q x y
  } deriving (Eq, Ord, Show)
instance (Category p, Category q, x ~ y)
  => Semigroup (ProductQ p q x y) where (<>) = (>>>)
instance (Category p, Category q, x ~ y)
  => Monoid (ProductQ p q x y) where mempty = id
instance (Category p, Category q) => Category (ProductQ p q) where
  id = ProductQ id id
  ProductQ pyz qyz . ProductQ pxy qxy = ProductQ (pyz . pxy) (qyz . qxy)

{- | Symmetry of `ProductQ`.-}
qswap :: ProductQ p q x y -> ProductQ q p x y
qswap (ProductQ p q) = ProductQ q p

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

{- | Compose quivers along matching source and target.-}
data ComposeQ p q x z = forall y. ComposeQ (p y z) (q x y)
deriving instance (forall y. Show (p y z), forall y. Show (q x y))
  => Show (ComposeQ p q x z)
instance (Category p, p ~ q, x ~ y)
  => Semigroup (ComposeQ p q x y) where (<>) = (>>>)
instance (Category p, p ~ q, x ~ y)
  => Monoid (ComposeQ p q x y) where mempty = id
instance (Category p, p ~ q) => Category (ComposeQ p q) where
  id = ComposeQ id id
  ComposeQ yz xy . ComposeQ wx vw = ComposeQ (yz . xy) (wx . vw)

{- | The left [residual]
(https://ncatlab.org/nlab/show/residual)
of `ComposeQ`.-}
newtype LeftQ p q x y = LeftQ
  {getLeftQ :: forall w. p w x -> q w y}
instance (p ~ q, x ~ y) => Semigroup (LeftQ p q x y) where (<>) = (>>>)
instance (p ~ q, x ~ y) => Monoid (LeftQ p q x y) where mempty = id
instance p ~ q => Category (LeftQ p q) where
  id = LeftQ id
  LeftQ g . LeftQ f = LeftQ (g . f)

{- | The right [residual]
(https://ncatlab.org/nlab/show/residual)
of `ComposeQ`.-}
newtype RightQ p q x y = RightQ
  {getRightQ :: forall z. p y z -> q x z}
instance (p ~ q, x ~ y) => Semigroup (RightQ p q x y) where (<>) = (>>>)
instance (p ~ q, x ~ y) => Monoid (RightQ p q x y) where mempty = id
instance p ~ q => Category (RightQ p q) where
  id = RightQ id
  RightQ f . RightQ g = RightQ (g . f)
