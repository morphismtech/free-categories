{-|
Module: Data.Quiver.Bifunctor
Description: free categories
Copyright: (c) Eitan Chatav, 2019
Maintainer: eitan@morphism.tech
Stability: experimental

The category of quivers forms a closed monoidal
category in two ways, under `ProductQ` or `ComposeQ`.
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

import Data.Quiver
import Data.Quiver.Functor

{- | A endo-bifunctor on the category of quivers,
covariant in both its arguments.

prop> qbimap id id = id
prop> qbimap (g . f) (i . h) = qbimap g i . qbimap f h
-}
class (forall q. QFunctor (prod q)) => QBifunctor prod where
  qbimap
    :: (forall x y. p x y -> p' x y)
    -> (forall x y. q x y -> q' x y)
    -> prod p q x y -> prod p' q' x y
instance QBifunctor ProductQ where
  qbimap f g (ProductQ p q) = ProductQ (f p) (g q)
instance QBifunctor ComposeQ where
  qbimap f g (ComposeQ p q) = ComposeQ (f p) (g q)

{- | A endo-bifunctor on the category of quivers,
contravariant in its first argument,
and covariant in its second argument.

prop> qdimap id id = id
prop> qdimap (g . f) (i . h) = qdimap f i . qdimap g h
-}
class (forall q. QFunctor (hom q)) => QProfunctor hom where
  qdimap
    :: (forall x y. p' x y -> p x y)
    -> (forall x y. q x y -> q' x y)
    -> hom p q x y -> hom p' q' x y
instance QProfunctor HomQ where qdimap f h (HomQ g) = HomQ (h . g . f)
instance QProfunctor LeftQ where qdimap f h (LeftQ g) = LeftQ (h . g . f)
instance QProfunctor RightQ where qdimap f h (RightQ g) = RightQ (h . g . f)

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

prop> qbimap id qassoc . qassoc . qbimap qassoc id = qassoc . qassoc

and the triangle equation,

prop> qbimap id qelim1 . qassoc = qbimap qelim2 id
-}
class QBifunctor prod => QMonoidal prod unit | prod -> unit where
  qintro1 :: p x y -> prod unit p x y
  qintro2 :: p x y -> prod p unit x y
  qelim1 :: prod unit p x y -> p x y
  qelim2 :: prod p unit x y -> p x y
  qassoc :: prod (prod p q) r x y -> prod p (prod q r) x y
  qdisassoc :: prod p (prod q r) x y -> prod (prod p q) r x y
instance QMonoidal ProductQ (KQ ()) where
  qintro1 p = ProductQ (KQ ()) p
  qintro2 p = ProductQ p (KQ ())
  qelim1 (ProductQ _ p) = p
  qelim2 (ProductQ p _) = p
  qassoc (ProductQ (ProductQ p q) r) = ProductQ p (ProductQ q r)
  qdisassoc (ProductQ p (ProductQ q r)) = ProductQ (ProductQ p q) r
instance QMonoidal ComposeQ (ReflQ ()) where
  qintro1 p = ComposeQ (ReflQ ()) p
  qintro2 p = ComposeQ p (ReflQ ())
  qelim1 (ComposeQ (ReflQ ()) p) = p
  qelim2 (ComposeQ p (ReflQ ())) = p
  qassoc (ComposeQ (ComposeQ p q) r) = ComposeQ p (ComposeQ q r)
  qdisassoc (ComposeQ p (ComposeQ q r)) = ComposeQ (ComposeQ p q) r

{- | A [(bi-)closed monoidal category]
(https://ncatlab.org/nlab/show/closed+monoidal+category)
is one for which the products
@prod _ p@ and @prod p _@ both have right adjoint functors,
the left and right residuals @lhom p@ and @rhom p@.
If @prod@ is symmetric then the left and right residuals
coincide as the internal hom.

prop> qcurry  . quncurry = id
prop> qflurry . qunflurry = id

prop> qlev . (qcurry f `qbimap` id) = f
prop> qcurry (qlev . (g `qbimap` id)) = g
prop> qrev . (id `qbimap` qflurry f) = f
prop> qflurry (qrev . (id `qbimap` g)) = g
-}
class (QBifunctor prod, QProfunctor lhom, QProfunctor rhom)
  => QClosed prod lhom rhom | prod -> lhom, prod -> rhom where
    qlev :: prod (lhom p q) p x y -> q x y
    qrev :: prod p (rhom p q) x y -> q x y
    qcurry :: (forall x y. prod p q x y -> r x y) -> p x y -> lhom q r x y
    quncurry :: (forall x y. p x y -> lhom q r x y) -> prod p q x y -> r x y
    qflurry :: (forall x y. prod p q x y -> r x y) -> q x y -> rhom p r x y
    qunflurry :: (forall x y. q x y -> rhom p r x y) -> prod p q x y -> r x y
instance QClosed ProductQ HomQ HomQ where
  qlev (ProductQ (HomQ pq) p) = pq p
  qrev (ProductQ p (HomQ pq)) = pq p
  qcurry f p = HomQ (\q -> f (ProductQ p q))
  quncurry f (ProductQ p q) = getHomQ (f p) q
  qflurry f q = HomQ (\p -> f (ProductQ p q))
  qunflurry f (ProductQ p q) = getHomQ (f q) p
instance QClosed ComposeQ LeftQ RightQ where
  qlev (ComposeQ (LeftQ pq) p) = pq p
  qrev (ComposeQ p (RightQ pq)) = pq p
  qcurry f p = LeftQ (\q -> f (ComposeQ p q))
  quncurry f (ComposeQ p q) = getLeftQ (f p) q
  qflurry f q = RightQ (\p -> f (ComposeQ p q))
  qunflurry f (ComposeQ p q) = getRightQ (f q) p
