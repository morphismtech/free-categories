{-|
Module: Control.Category.Free
Description: free categories
Copyright: (c) Eitan Chatav, 2019
Maintainer: eitan@morphism.tech
Stability: experimental

Consider the category of Haskell `Category`s, a subcategory
of the category of quivers with,

* constrained objects `Category` @c => c@
* morphisms are functors (which preserve objects)
  * @t :: (Category c, Category d) => c x y -> d x y@
  * @t id = id@
  * @t (g . f) = t g . t f@

Thus, a functor from quivers to `Category`s
has @(QFunctor c, forall p. Category (c p))@ with.

prop> qmap f id = id
prop> qmap f (q . p) = qmap f q . qmap f p

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
  , CFree (..)
  , toPath
  , reversePath
  , beforeAll
  , afterAll
  , Category (..)
  ) where

import Data.Quiver
import Data.Quiver.Functor
import Control.Category
import Control.Atkey
import Control.Monad (join)
import Prelude hiding (id, (.))

{- | A `Path` with steps in @p@ is a singly linked list of
"type-aligned" constructions of @p@.

>>> :{
let
  path :: Path (->) String Int
  path = length :>> (\x -> x^2) :>> Done
in
  qfold path "hello"
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
instance QFunctor Path where
  qmap _ Done = Done
  qmap f (p :>> ps) = f p :>> qmap f ps
instance QFoldable Path where
  qfoldMap _ Done = id
  qfoldMap f (p :>> ps) = f p >>> qfoldMap f ps
  qtoMonoid _ Done = mempty
  qtoMonoid f (p :>> ps) = f p <> qtoMonoid f ps
  qtoList _ Done = []
  qtoList f (p :>> ps) = f p : qtoList f ps
  qtraverse_ _ Done = ipure id
  qtraverse_ f (p :>> ps) = iliftA2 (>>>) (f p) (qtraverse_ f ps)
instance QTraversable Path where
  qtraverse _ Done = ipure Done
  qtraverse f (p :>> ps) = iliftA2 (:>>) (f p) (qtraverse f ps)
instance QPointed Path where qsingle p = p :>> Done
instance QMonad Path where qjoin = qfold
instance CFree Path

{- | Encodes a path as its `qfoldMap` function.-}
newtype FoldPath p x y = FoldPath
  {getFoldPath :: forall q. Category q
    => (forall x y. p x y -> q x y) -> q x y}
instance x ~ y => Semigroup (FoldPath p x y) where (<>) = (>>>)
instance x ~ y => Monoid (FoldPath p x y) where mempty = id
instance Category (FoldPath p) where
  id = FoldPath $ \ _ -> id
  FoldPath g . FoldPath f = FoldPath $ \ k -> g k . f k
instance QFunctor FoldPath where qmap f = qfoldMap (qsingle . f)
instance QFoldable FoldPath where qfoldMap k (FoldPath f) = f k
instance QTraversable FoldPath where
  qtraverse f = getIxApQ . qfoldMap (IxApQ . imap qsingle . f)
instance QPointed FoldPath where qsingle p = FoldPath $ \ k -> k p
instance QMonad FoldPath where qjoin (FoldPath f) = f id
instance CFree FoldPath

{- | Unpacking the definition of a left adjoint to the forgetful functor
from `Category`s to quivers, any

@f :: Category d => p x y -> d x y@

factors uniquely through the free `Category` @c@ as

prop> qfoldMap f . qsingle = f
-}
class
  ( QPointed c
  , QFoldable c
  , forall p. Category (c p)
  ) => CFree c where

{- | `toPath` collapses any `QFoldable` into a `CFree`.
It is the unique isomorphism which exists
between any two `CFree` functors.
-}
toPath :: (QFoldable c, CFree path) => c p x y -> path p x y
toPath = qfoldMap qsingle

{- | Reverse all the arrows in a path. -}
reversePath :: (QFoldable c, CFree path) => c p x y -> path (OpQ p) y x
reversePath = getOpQ . qfoldMap (OpQ . qsingle . OpQ)

{- | Insert a given loop before each step. -}
beforeAll
  :: (QFoldable c, CFree path)
  => (forall x. p x x) -> c p x y -> path p x y
beforeAll sep = qfoldMap (\p -> qsingle sep >>> qsingle p)

{- | Insert a given loop before each step. -}
afterAll
  :: (QFoldable c, CFree path)
  => (forall x. p x x) -> c p x y -> path p x y
afterAll sep = qfoldMap (\p -> qsingle p >>> qsingle sep)
