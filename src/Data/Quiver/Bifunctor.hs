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
  ( CBifunctor (..)
  , CProfunctor (..)
  , CMonoidal (..)
  , CClosed (..)
  ) where

import Data.Quiver
import Data.Quiver.Functor

{- | A endo-bifunctor on the category of quivers,
covariant in both its arguments.

prop> cbimap id id = id
prop> cbimap (g . f) (i . h) = cbimap g i . cbimap f h
-}
class (forall q. CFunctor (prod q)) => CBifunctor prod where
  cbimap
    :: (forall x y. p x y -> p' x y)
    -> (forall x y. q x y -> q' x y)
    -> prod p q x y -> prod p' q' x y
instance CBifunctor ProductQ where
  cbimap f g (ProductQ p q) = ProductQ (f p) (g q)
instance CBifunctor ComposeQ where
  cbimap f g (ComposeQ p q) = ComposeQ (f p) (g q)

{- | A endo-bifunctor on the category of quivers,
contravariant in its first argument,
and covariant in its second argument.

prop> cdimap id id = id
prop> cdimap (g . f) (i . h) = cdimap f i . cdimap g h
-}
class (forall q. CFunctor (hom q)) => CProfunctor hom where
  cdimap
    :: (forall x y. p' x y -> p x y)
    -> (forall x y. q x y -> q' x y)
    -> hom p q x y -> hom p' q' x y
instance CProfunctor Quiver where cdimap f h (Quiver g) = Quiver (h . g . f)
instance CProfunctor ExtendQ where cdimap f h (ExtendQ g) = ExtendQ (h . g . f)
instance CProfunctor LiftQ where cdimap f h (LiftQ g) = LiftQ (h . g . f)

{-| A [monoidal category]
(https://ncatlab.org/nlab/show/monoidal+category)
structure on the category of quivers.

This consists of a product bifunctor, a unit object and
structure morphisms, an invertible associator
and invertible left and right unitors that satisfy
the pentagon equation,

prop> cbimap id cassoc . cassoc . cbimap cassoc id = cassoc . cassoc

and the triangle equation,

prop> cbimap id celim1 . cassoc = cbimap celim2 id
-}
class CBifunctor prod => CMonoidal prod unit | prod -> unit where
  cintro1 :: p x y -> prod unit p x y
  cintro2 :: p x y -> prod p unit x y
  celim1 :: prod unit p x y -> p x y
  celim2 :: prod p unit x y -> p x y
  cassoc :: prod (prod p q) r x y -> prod p (prod q r) x y
  cdisassoc :: prod p (prod q r) x y -> prod (prod p q) r x y
instance CMonoidal ProductQ (KQ ()) where
  cintro1 p = ProductQ (KQ ()) p
  cintro2 p = ProductQ p (KQ ())
  celim1 (ProductQ _ p) = p
  celim2 (ProductQ p _) = p
  cassoc (ProductQ (ProductQ p q) r) = ProductQ p (ProductQ q r)
  cdisassoc (ProductQ p (ProductQ q r)) = ProductQ (ProductQ p q) r
instance CMonoidal ComposeQ (ReflQ ()) where
  cintro1 p = ComposeQ (ReflQ ()) p
  cintro2 p = ComposeQ p (ReflQ ())
  celim1 (ComposeQ (ReflQ ()) p) = p
  celim2 (ComposeQ p (ReflQ ())) = p
  cassoc (ComposeQ (ComposeQ p q) r) = ComposeQ p (ComposeQ q r)
  cdisassoc (ComposeQ p (ComposeQ q r)) = ComposeQ (ComposeQ p q) r

{- | A [(bi-)closed monoidal category]
(https://ncatlab.org/nlab/show/closed+monoidal+category)
is one for which the products
@prod _ p@ and @prod p _@ both have right adjoint functors,
the left and right residuals @lhom p@ and @rhom p@.
If @prod@ is symmetric then the left and right residuals
coincide as the internal hom.

prop> ccurry  . cuncurry = id
prop> cflurry . cunflurry = id

prop> clev . (ccurry f `cbimap` id) = f
prop> ccurry (clev . (g `cbimap` id)) = g
prop> crev . (cflurry f `cbimap` id) = f
prop> cflurry (crev . (g `cbimap` id)) = g
-}
class (CBifunctor prod, CProfunctor lhom, CProfunctor rhom)
  => CClosed prod lhom rhom | prod -> lhom, prod -> rhom where
    clev :: prod (lhom p q) p x y -> q x y
    crev :: prod p (rhom p q) x y -> q x y
    ccurry :: (forall x y. prod p q x y -> r x y) -> p x y -> lhom q r x y
    cuncurry :: (forall x y. p x y -> lhom q r x y) -> prod p q x y -> r x y
    cflurry :: (forall x y. prod p q x y -> r x y) -> q x y -> rhom p r x y
    cunflurry :: (forall x y. q x y -> rhom p r x y) -> prod p q x y -> r x y
instance CClosed ProductQ Quiver Quiver where
  clev (ProductQ (Quiver pq) p) = pq p
  crev (ProductQ p (Quiver pq)) = pq p
  ccurry f p = Quiver (\q -> f (ProductQ p q))
  cuncurry f (ProductQ p q) = getQuiver (f p) q
  cflurry f q = Quiver (\p -> f (ProductQ p q))
  cunflurry f (ProductQ p q) = getQuiver (f q) p
instance CClosed ComposeQ ExtendQ LiftQ where
  clev (ComposeQ (ExtendQ pq) p) = pq p
  crev (ComposeQ p (LiftQ pq)) = pq p
  ccurry f p = ExtendQ (\q -> f (ComposeQ p q))
  cuncurry f (ComposeQ p q) = getExtendQ (f p) q
  cflurry f q = LiftQ (\p -> f (ComposeQ p q))
  cunflurry f (ComposeQ p q) = getLiftQ (f q) p
