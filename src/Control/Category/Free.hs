{-|
Module: Control.Category.Free
Description: free categories
Copyright: (c) Eitan Chatav, 2019
Maintainer: eitan@morphism.tech
Stability: experimental

Consider the category of Haskell `Category`s, a subcategory
of the category of quivers with,

* constrained objects `Category` @c => c@
* morphisms act functorially
  * @t :: (Category c, Category d) => c x y -> d x y@
  * @t id = id@
  * @t (g . f) = t g . t f@

A functor from quivers to `Category`s
has @(CFunctor c, forall p. Category (c p))@ with

prop> cmap f id = id
prop> cmap f (q . p) = cmap f q . cmap f p

The [free category functor](https://ncatlab.org/nlab/show/free+category)
from quivers to `Category`s may be defined up to isomorphism as

* the functor `Path` of type-aligned lists

* the functor `FoldPath` of categorical folds

* abstractly as `CFree` @path => path@,
  the class of left adjoints to the functor which
  forgets the constraint on `Category` @c => c@

* or as any isomorphic data structure
-}

{-# LANGUAGE
    GADTs
  , LambdaCase
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
  , CFree (..)
  , toPath
  , creverse
  , beforeAll
  , afterAll
  ) where

import Data.Quiver
import Data.Quiver.Functor
import Control.Category
import Control.Monad (join)
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
instance x ~ y => Semigroup (Path p x y) where (<>) = (>>>)
instance x ~ y => Monoid (Path p x y) where mempty = Done
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
instance CPointed Path where csingleton p = p :>> Done
instance CMonad Path where cjoin = cfold
instance CFree Path

{- | Encodes a path as its `cfoldMap` function.-}
newtype FoldPath p x y = FoldPath
  {getFoldPath :: forall q. Category q
    => (forall x y. p x y -> q x y) -> q x y}
instance x ~ y => Semigroup (FoldPath p x y) where (<>) = (>>>)
instance x ~ y => Monoid (FoldPath p x y) where mempty = id
instance Category (FoldPath p) where
  id = FoldPath $ \ _ -> id
  FoldPath g . FoldPath f = FoldPath $ \ k -> g k . f k
instance CFunctor FoldPath where cmap f = cfoldMap (csingleton . f)
instance CFoldable FoldPath where cfoldMap k (FoldPath f) = f k
instance CTraversable FoldPath where
  ctraverse f = getApQ . cfoldMap (ApQ . fmap csingleton . f)
instance CPointed FoldPath where csingleton p = FoldPath $ \ k -> k p
instance CMonad FoldPath where cjoin (FoldPath f) = f id
instance CFree FoldPath

{- | Unpacking the definition of a left adjoint to the forgetful functor
from `Category`s to quivers, any

@f :: Category d => p x y -> d x y@

factors uniquely through the free `Category` @c@ as

prop> cfoldMap f . csingleton = f
-}
class
  ( CPointed c
  , CFoldable c
  , forall p. Category (c p)
  ) => CFree c where

{- | `toPath` collapses any `CFoldable` into a `CFree`.
It is the unique isomorphism which exists
between any two `CFree` functors.
-}
toPath :: (CFoldable c, CFree path) => c p x y -> path p x y
toPath = cfoldMap csingleton

{- | Reverse all the arrows in a path. -}
creverse :: (CFoldable c, CFree path) => c p x y -> path (OpQ p) y x
creverse = getOpQ . cfoldMap (OpQ . csingleton . OpQ)

{- | Insert a given loop before each step. -}
beforeAll
  :: (CFoldable c, CFree path)
  => (forall x. p x x) -> c p x y -> path p x y
beforeAll sep = cfoldMap (\p -> csingleton sep >>> csingleton p)

{- | Insert a given loop before each step. -}
afterAll
  :: (CFoldable c, CFree path)
  => (forall x. p x x) -> c p x y -> path p x y
afterAll sep = cfoldMap (\p -> csingleton p >>> csingleton sep)
