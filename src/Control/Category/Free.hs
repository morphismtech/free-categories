{-|
Module: Control.Category.Free
Description: free categories
Copyright: (c) Eitan Chatav, 2019
Maintainer: eitan@morphism.tech
Stability: experimental

Consider the category of Haskell "quivers" with

* objects are types of higher kind
  * @p :: k -> k -> Type@
* morphisms are terms of @RankNType@,
  * @forall x y. p x y -> q x y@
* identity is `id`
* composition is `.`

Now, consider the subcategory of Haskell `Category`s with

* constrained objects `Category` @c => c@
* morphisms act functorially
  * @t :: (Category c, Category d) => c x y -> d x y@
  * @t id = id@
  * @t (g . f) = t g . t f@

The [free category functor](https://ncatlab.org/nlab/show/free+category)
from quivers to `Category`s may be defined up to isomorphism as

* the functor `Path` of type-aligned lists

* the functor `FoldPath` of categorical folds

* abstractly as `CFree` @path => path@, the class of
  left adjoints to the functor which
  forgets the constraint on `Category` @c => c@

* or as any isomorphic data structure
-}

{-# LANGUAGE
    FlexibleInstances
  , GADTs
  , LambdaCase
  , MultiParamTypeClasses
  , PatternSynonyms
  , PolyKinds
  , QuantifiedConstraints
  , RankNTypes
  , StandaloneDeriving
#-}

module Control.Category.Free
  ( Path (..)
  , pattern (:<<)
  , FoldPath (..)
  , Category (..)
  , CFunctor (..)
  , CFoldable (..)
  , CTraversable (..)
  , CFree (..)
  , toPath
  , creverse
  , beforeAll
  , afterAll
  , EndoL (..)
  , EndoR (..)
  , MCat (..)
  , ApCat (..)
  , Op (..)
  , Iso (..)
  ) where

import Control.Category
import Prelude hiding (id, (.))

{- | A `Path` with steps in @p@ is a singly linked list of
"type-aligned" constructions of @p@.

>>> :{
let
  path :: Path (->) String Int
  path = length :>> (\x -> x^2) :>> Done
in
  cfold path "hello"
:}
25
-}
data Path p x y where
  Done :: Path p x x
  (:>>) :: p x y -> Path p y z -> Path p x z
infixr 7 :>>
{- | The snoc pattern for right-to-left composition.-}
pattern (:<<) :: Path p y z -> p x y -> Path p x z
pattern ps :<< p = p :>> ps
infixl 7 :<<
deriving instance (forall x y. Show (p x y)) => Show (Path p x y)
instance x ~ y => Semigroup (Path p x y) where
  (<>) = (>>>)
instance x ~ y => Monoid (Path p x y) where
  mempty = Done
  mappend = (>>>)
instance Category (Path p) where
  id = Done
  (.) path = \case
    Done -> path
    p :>> ps -> p :>> (ps >>> path)
instance CFunctor Path where
  cmap _ Done = Done
  cmap f (p :>> ps) = f p :>> cmap f ps
instance CFoldable Path where
  cfoldMap _ Done = id
  cfoldMap f (p :>> ps) = f p >>> cfoldMap f ps
  ctoMonoid _ Done = mempty
  ctoMonoid f (p :>> ps) = f p <> ctoMonoid f ps
  ctoList _ Done = []
  ctoList f (p :>> ps) = f p : ctoList f ps
  ctraverse_ _ Done = pure id
  ctraverse_ f (p :>> ps) = (>>>) <$> f p <*> ctraverse_ f ps
instance CTraversable Path where
  ctraverse _ Done = pure Done
  ctraverse f (p :>> ps) = (:>>) <$> f p <*> ctraverse f ps
instance CFree Path where csingleton p = p :>> Done

{- | Encodes a path as its `cfoldMap` function.-}
newtype FoldPath p x y = FoldPath
  {getFoldPath :: forall q. Category q => (forall x y. p x y -> q x y) -> q x y}
instance x ~ y => Semigroup (FoldPath p x y) where
  (<>) = (>>>)
instance x ~ y => Monoid (FoldPath p x y) where
  mempty = id
  mappend = (>>>)
instance Category (FoldPath p) where
  id = FoldPath $ \ _ -> id
  FoldPath g . FoldPath f = FoldPath $ \ k -> g k . f k
instance CFunctor FoldPath where cmap f = cfoldMap (csingleton . f)
instance CFoldable FoldPath where cfoldMap k (FoldPath f) = f k
instance CTraversable FoldPath where
  ctraverse f = getApCat . cfoldMap (ApCat . fmap csingleton . f)
instance CFree FoldPath where csingleton p = FoldPath $ \ k -> k p

{- | An endfunctor of quivers.

prop> cmap id = id
prop> cmap (g . f) = cmap g . cmap f

A functor from quivers to `Category`s
has @(CFunctor c, forall p. Category (c p))@ with

prop> cmap f id = id
prop> cmap f (q . p) = cmap f q . cmap f p
-}
class CFunctor c where
  cmap :: (forall x y. p x y -> q x y) -> c p x y -> c q x y

{- | Generalizing `Foldable` from `Monoid`s to `Category`s.

prop> cmap f = cfoldMap (csingleton . f)
-}
class CFunctor c => CFoldable c where
  {- | Map each element of the structure to a `Category`,
  and combine the results.-}
  cfoldMap :: Category q => (forall x y. p x y -> q x y) -> c p x y -> q x y
  {- | Combine the elements of a structure using a `Category`.-}
  cfold :: Category q => c q x y -> q x y
  cfold = cfoldMap id
  {- | Right-associative fold of a structure.

  In the case of `Path`s, `cfoldr`, when applied to a binary operator,
  a starting value, and a `Path`, reduces the `Path` using the binary operator,
  from right to left:

  prop> cfoldr (?) q (p1 :>> p2 :>> ... :>> pn :>> Done) == p1 ? (p2 ? ... (pn ? q) ...)
  -}
  cfoldr :: (forall x y z . p x y -> q y z -> q x z) -> q y z -> c p x y -> q x z
  cfoldr (?) q c = getEndoR (cfoldMap (\ x -> EndoR (\ y -> x ? y)) c) q
  {- | Left-associative fold of a structure.

  In the case of `Path`s, `cfoldl`, when applied to a binary operator,
  a starting value, and a `Path`, reduces the `Path` using the binary operator,
  from left to right:

  prop> cfoldl (?) q (p1 :>> p2 :>> ... :>> pn :>> Done) == (... ((q ? p1) ? p2) ? ...) ? pn
  -}
  cfoldl :: (forall x y z . q x y -> p y z -> q x z) -> q x y -> c p y z -> q x z
  cfoldl (?) q c = getEndoL (cfoldMap (\ x -> EndoL (\ y -> y ? x)) c) q
  {- | Map each element of the structure to a `Monoid`,
  and combine the results.-}
  ctoMonoid :: Monoid m => (forall x y. p x y -> m) -> c p x y -> m
  ctoMonoid f = getMCat . cfoldMap (MCat . f)
  {- | Map each element of the structure, and combine the results in a list.-}
  ctoList :: (forall x y. p x y -> a) -> c p x y -> [a]
  ctoList f = ctoMonoid (pure . f)
  {- | Map each element of a structure to an `Applicative` on a `Category`,
  evaluate from left to right, and combine the results.-}
  ctraverse_
    :: (Applicative m, Category q)
    => (forall x y. p x y -> m (q x y)) -> c p x y -> m (q x y)
  ctraverse_ f = getApCat . cfoldMap (ApCat . f)

{- | Generalizing `Traversable` to `Category`s.-}
class CFoldable c => CTraversable c where
  {- | Map each element of a structure to an `Applicative` on a quiver,
  evaluate from left to right, and collect the results.-}
  ctraverse
    :: Applicative m
    => (forall x y. p x y -> m (q x y)) -> c p x y -> m (c q x y)

{- | Unpacking the definition of a left adjoint to the forgetful functor
from `Category`s to quivers, there must be a function `csingleton`,
such that any function

@f :: Category d => p x y -> d x y@

factors uniquely through @c p x y@ as

prop> cfoldMap f . csingleton = f
-}
class (CTraversable c, forall p. Category (c p)) => CFree c where
  csingleton :: p x y -> c p x y

{- | `toPath` collapses any `CFoldable` into a `CFree`.
It is the unique isomorphism which exists
between any two `CFree` functors.
-}
toPath :: (CFoldable c, CFree path) => c p x y -> path p x y
toPath = cfoldMap csingleton

{- | Reverse all the arrows in a path. -}
creverse :: (CFoldable c, CFree path) => c p x y -> path (Op p) y x
creverse = getOp . cfoldMap (Op . csingleton . Op)

{- | Insert a given endomorphism before each step. -}
beforeAll
  :: (CFoldable c, CFree path)
  => (forall x. p x x) -> c p x y -> path p x y
beforeAll sep = cfoldMap (\p -> csingleton sep >>> csingleton p)

{- | Insert a given endomorphism before each step. -}
afterAll
  :: (CFoldable c, CFree path)
  => (forall x. p x x) -> c p x y -> path p x y
afterAll sep = cfoldMap (\p -> csingleton p >>> csingleton sep)

{- | Used in the default definition of `cfoldr`.-}
newtype EndoR p y x = EndoR {getEndoR :: forall z. p x z -> p y z}
instance Category (EndoR p) where
  id = EndoR id
  EndoR f1 . EndoR f2 = EndoR (f2 . f1)

{- | Used in the default definition of `cfoldr`.-}
newtype EndoL p x y = EndoL {getEndoL :: forall w . p w x -> p w y}
instance Category (EndoL p) where
  id = EndoL id
  EndoL f1 . EndoL f2 = EndoL (f1 . f2)

{- | Turn a `Monoid` into a `Category`,
used in the default definition of `ctoMonoid`.-}
newtype MCat m x y = MCat {getMCat :: m} deriving (Eq, Ord, Show)
instance Monoid m => Category (MCat m) where
  id = MCat mempty
  MCat g . MCat f = MCat (f <> g)

{- | Turn an `Applicative` over a `Category` into a `Category`,
used in the default definition of `ctraverse_`.-}
newtype ApCat m c x y = ApCat {getApCat :: m (c x y)} deriving (Eq, Ord, Show)
instance (Applicative m, Category c) => Category (ApCat m c) where
  id = ApCat (pure id)
  ApCat g . ApCat f = ApCat ((.) <$> g <*> f)
instance Functor m => CFunctor (ApCat m) where
  cmap f (ApCat m) = ApCat (f <$> m)

{- | Reverse all the arrows in a quiver. If @c@ is a `Category`
then so is @Op c@.-}
newtype Op c x y = Op {getOp :: c y x} deriving (Eq, Ord, Show)
instance Category c => Category (Op c) where
  id = Op id
  Op g . Op f = Op (f . g)
instance CFunctor Op where cmap f = Op . f . getOp

{- | Turn all arrows in a quiver into bidirectional edges.
If @c@ is a `Category` then so is `Iso`.-}
data Iso c x y = Iso
  { up :: c x y
  , down :: c y x
  } deriving (Eq, Ord, Show)
instance Category c => Category (Iso c) where
  id = Iso id id
  (Iso yz zy) . (Iso xy yx) = Iso (yz . xy) (yx . zy)
instance CFunctor Iso where
  cmap f (Iso u d) = Iso (f u) (f d)
