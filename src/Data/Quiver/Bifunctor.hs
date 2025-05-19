{-|
Module: Data.Quiver.Bifunctor
Description: free categories
Copyright: (c) Eitan Chatav, 2019
Maintainer: eitan@morphism.tech
Stability: experimental

The category of quivers forms a closed monoidal
category in two ways, under `Product` or `Procompose`.
The relations between these and their adjoints can be
characterized by typeclasses below.
-}

{-# LANGUAGE
    FlexibleInstances
  , FunctionalDependencies
  , GADTs
  , PolyKinds
  , QuantifiedConstraints
  , RankNTypes
#-}

module Data.Quiver.Bifunctor
  ( QBifunctor (..)
  , QProfunctor (..)
  , QMonoidal (..)
  , QClosed (..)
  ) where

import Data.Bifunctor.Functor
import Data.Bifunctor.Product
import Data.Profunctor.Composition
import Data.Profunctor.Ran
import Data.Quiver
import Data.Quiver.Functor

{- | A endo-bifunctor on the category of quivers,
covariant in both its arguments.

prop> qbimap id id = id
prop> qbimap (g . f) (i . h) = qbimap g i . qbimap f h
prop> qbimap id f = bifmap f
prop> qbimap f id = qlmap f
-}
class (forall q. BifunctorFunctor (prod q)) => QBifunctor prod where
  qbimap
    :: (forall x y. p x y -> p' x y)
    -> (forall x y. q x y -> q' x y)
    -> prod p q x y -> prod p' q' x y
  qlmap
    :: (forall x y. p x y -> p' x y)
    -> prod p q x y -> prod p' q x y
  qlmap f = qbimap f id
instance QBifunctor Product where
  qbimap f g (Pair p q) = Pair (f p) (g q)
instance QBifunctor Procompose where
  qbimap f g (Procompose p q) = Procompose (f p) (g q)

{- | A endo-bifunctor on the category of quivers,
contravariant in its first argument,
and covariant in its second argument.

prop> qdimap id id = id
prop> qdimap (g . f) (i . h) = qdimap f i . qdimap g h
prop> qdimap id f = bifmap f
prop> qdimap f id = qpremap f
-}
class (forall q. BifunctorFunctor (hom q)) => QProfunctor hom where
  qdimap
    :: (forall x y. p' x y -> p x y)
    -> (forall x y. q x y -> q' x y)
    -> hom p q x y -> hom p' q' x y
  qpremap
    :: (forall x y. p' x y -> p x y)
    -> hom p q x y -> hom p' q x y
  qpremap f = qdimap f id
instance QProfunctor HomQ where qdimap f h (HomQ g) = HomQ (h . g . f)
instance QProfunctor Ran where qdimap f h (Ran g) = Ran (h . g . f)
instance QProfunctor Rift where qdimap f h (Rift g) = Rift (h . g . f)

{-| A [monoidal category]
(https://ncatlab.org/nlab/show/monoidal+category)
structure on the category of quivers.

This consists of a product bifunctor, a unit object and
structure morphisms, an invertible associator,

prop> qassoc . qdisassoc = id
prop> qdisassoc . qassoc = id

and invertible left and right unitors,

prop> qintro1 . qelim1 = id
prop> qelim1 . qintro1 = id
prop> qintro2 . qelim2 = id
prop> qelim2 . qintro2 = id

that satisfy the pentagon equation,

prop> bifmap qassoc . qassoc . qlmap qassoc = qassoc . qassoc

and the triangle equation,

prop> bifmap qelim1 . qassoc = qlmap qelim2
-}
class QBifunctor prod => QMonoidal prod unit | prod -> unit where
  qintro1 :: p x y -> prod unit p x y
  qintro2 :: p x y -> prod p unit x y
  qelim1 :: prod unit p x y -> p x y
  qelim2 :: prod p unit x y -> p x y
  qassoc :: prod (prod p q) r x y -> prod p (prod q r) x y
  qdisassoc :: prod p (prod q r) x y -> prod (prod p q) r x y
instance QMonoidal Product (KQ ()) where
  qintro1 p = Pair (KQ ()) p
  qintro2 p = Pair p (KQ ())
  qelim1 (Pair _ p) = p
  qelim2 (Pair p _) = p
  qassoc (Pair (Pair p q) r) = Pair p (Pair q r)
  qdisassoc (Pair p (Pair q r)) = Pair (Pair p q) r
instance QMonoidal Procompose (ReflQ ()) where
  qintro1 p = Procompose (ReflQ ()) p
  qintro2 p = Procompose p (ReflQ ())
  qelim1 (Procompose (ReflQ ()) p) = p
  qelim2 (Procompose p (ReflQ ())) = p
  qassoc (Procompose (Procompose p q) r) = Procompose p (Procompose q r)
  qdisassoc (Procompose p (Procompose q r)) = Procompose (Procompose p q) r

{- | A [(bi-)closed monoidal category]
(https://ncatlab.org/nlab/show/closed+monoidal+category)
is one for which the products
@prod _ p@ and @prod p _@ both have right adjoint functors,
the left and right [residuals](https://ncatlab.org/nlab/show/residual)
@lhom p@ and @rhom p@. If @prod@ is symmetric then the
left and right residuals coincide as the
[internal hom](https://ncatlab.org/nlab/show/internal+hom).

prop> qcurry  . quncurry = id
prop> qflurry . qunflurry = id

prop> qlev . qlmap (qcurry f) = f
prop> qcurry (qlev . qlmap g) = g
prop> qrev . bifmap (qflurry f) = f
prop> qflurry (qrev . bifmap g) = g
-}
class (QBifunctor prod, QProfunctor lhom, QProfunctor rhom)
  => QClosed prod lhom rhom | prod -> lhom, prod -> rhom where
    qlev :: prod (lhom p q) p x y -> q x y
    qrev :: prod p (rhom p q) x y -> q x y
    qcurry :: (forall x y. prod p q x y -> r x y) -> p x y -> lhom q r x y
    quncurry :: (forall x y. p x y -> lhom q r x y) -> prod p q x y -> r x y
    qflurry :: (forall x y. prod p q x y -> r x y) -> q x y -> rhom p r x y
    qunflurry :: (forall x y. q x y -> rhom p r x y) -> prod p q x y -> r x y
instance QClosed Product HomQ HomQ where
  qlev (Pair (HomQ pq) p) = pq p
  qrev (Pair p (HomQ pq)) = pq p
  qcurry f p = HomQ (\q -> f (Pair p q))
  quncurry f (Pair p q) = getHomQ (f p) q
  qflurry f q = HomQ (\p -> f (Pair p q))
  qunflurry f (Pair p q) = getHomQ (f q) p
instance QClosed Procompose Ran Rift where
  qlev (Procompose (Ran pq) p) = pq p
  qrev (Procompose p (Rift pq)) = pq p
  qcurry f p = Ran (\q -> f (Procompose p q))
  quncurry f (Procompose p q) = runRan (f p) q
  qflurry f q = Rift (\p -> f (Procompose p q))
  qunflurry f (Procompose p q) = runRift (f q) p
