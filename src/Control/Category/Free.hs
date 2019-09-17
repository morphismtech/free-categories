{-|
Module: Control.Category.Free
Description: free categories
Copyright: (c) Eitan Chatav, 2019
Maintainer: eitan@morphism.tech
Stability: experimental

Consider the category of Haskell "quivers" with

* objects are types
  * @p :: k -> k -> Type@
* morphisms are terms of @RankNType@,
  * @forall x y. p x y -> q x y@
* identity is `id`
* composition is `.`

Now, consider the subcategory of Haskell `Category`s with

* constrained objects `Category` @c => c@
* morphisms are functorial terms with
  * @t :: (Category c, Category d) => c x y -> d x y@

prop> t id = id
prop> t (g . f) = t g . t f

The free category functor from quivers to `Category`s
may be defined up to isomorphism as

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
  , PolyKinds
  , QuantifiedConstraints
  , RankNTypes
  , StandaloneDeriving
#-}

module Control.Category.Free
  ( Path (..)
  , FoldPath (..)
  , CFunctor (..)
  , CFoldable (..)
  , CFree (..)
  , toPath
  , EndoL (..)
  , EndoR (..)
  , KCat (..)
  , Category (..)
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
instance CFree Path where csingleton p = p :>> Done

{- | Encodes a `Path` as its `cfoldMap` function.-}
newtype FoldPath p x y = FoldPath
  {getFoldPath :: forall q. Category q => (forall x y. p x y -> q x y) -> q x y}
instance Category (FoldPath p) where
  id = FoldPath $ \ _ -> id
  FoldPath g . FoldPath f = FoldPath $ \ k -> g k . f k
instance CFunctor FoldPath where cmap f = cfoldMap (csingleton . f)
instance CFoldable FoldPath where cfoldMap k (FoldPath f) = f k
instance CFree FoldPath where csingleton p = FoldPath $ \ k -> k p

{- | A functor from quivers to `Category`s.

prop> cmap _ id = id
prop> cmap f (c >>> c') = f c >>> f c'
-}
class (forall p. Category (c p)) => CFunctor c where
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
  {- | Combine the elements of a structure using a `Monoid`.-}
  ctoMonoid :: Monoid m => (forall x y. p x y -> m) -> c p x y -> m
  ctoMonoid f = getKCat . cfoldMap (KCat . f)
  {- | Combine the elements of a structure into a list.-}
  ctoList :: (forall x y. p x y -> a) -> c p x y -> [a]
  ctoList f = ctoMonoid (pure . f)

{- | Unpacking the definition of a left adjoint to the forgetful functor
from `Category`s to quivers, for any function

  @f :: Category d => p x y -> d x y@

there must be a function `csingleton` factoring @f@ uniquely through
the free category. The function taking @f@ to the unique functor from
@d@ to the free category has the same type as `cfoldMap` and hence must be it.

prop> cfoldMap f . csingleton = f
-}
class CFoldable c => CFree c where csingleton :: p x y -> c p x y

{- | `toPath` collapses any `CFoldable` into a `CFree`.
It is the unique isomorphism which exists
between any two `CFree` functors.
-}
toPath :: (CFoldable c, CFree path) => c p x y -> path p x y
toPath = cfoldMap csingleton

-- | Used in the default definition of `cfoldr`.
newtype EndoR p y x = EndoR {getEndoR :: forall z. p x z -> p y z}
instance Category (EndoR p) where
  id = EndoR id
  EndoR f1 . EndoR f2 = EndoR (f2 . f1)

-- | Used in the default definition of `cfoldr`.
newtype EndoL p x y = EndoL {getEndoL :: forall w . p w x -> p w y}
instance Category (EndoL p) where
  id = EndoL id
  EndoL f1 . EndoL f2 = EndoL (f1 . f2)

-- | The constant category, used in the default definition of `ctoMonoid`.
newtype KCat m x y = KCat { getKCat :: m } deriving (Eq, Ord, Show)
instance Monoid m => Category (KCat m) where
  id = KCat mempty
  KCat m2 . KCat m1 = KCat (m1 <> m2)
