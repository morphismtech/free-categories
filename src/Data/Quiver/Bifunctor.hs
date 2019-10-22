{-|
Module: Control.Category.Bifunctor
Description: free categories
Copyright: (c) Eitan Chatav, 2019
Maintainer: eitan@morphism.tech
Stability: experimental

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
  ( CBifunctor
  , CProfunctor
  , CMonoidal
  , CClosed
  ) where

import Data.Quiver
import Data.Quiver.Functor

class (CBifunctor prod, CProfunctor lhom, CProfunctor rhom)
  => CClosed prod lhom rhom | prod -> lhom, prod -> rhom where
    ccurry :: (forall x y. prod p q x y -> r x y) -> p x y -> lhom q r x y
    cuncurry :: (forall x y. p x y -> lhom q r x y) -> prod p q x y -> r x y
    cflurry :: (forall x y. prod p q x y -> r x y) -> q x y -> rhom p r x y
    cunflurry :: (forall x y. q x y -> rhom p r x y) -> prod p q x y -> r x y
instance CClosed ProductQ Quiver Quiver where
  ccurry f p = Quiver (\q -> f (ProductQ p q))
  cuncurry f (ProductQ p q) = getQuiver (f p) q
  cflurry f q = Quiver (\p -> f (ProductQ p q))
  cunflurry f (ProductQ p q) = getQuiver (f q) p
instance CClosed ComposeQ ExtendQ LiftQ where
  ccurry f p = ExtendQ (\q -> f (ComposeQ p q))
  cuncurry f (ComposeQ p q) = getExtendQ (f p) q
  cflurry f q = LiftQ (\p -> f (ComposeQ p q))
  cunflurry f (ComposeQ p q) = getLiftQ (f q) p

class CBifunctor prod => CMonoidal prod unit | prod -> unit where
  cintro1 :: p x y -> prod unit p x y
  cintro2 :: p x y -> prod p unit x y
  celim1 :: prod unit p x y -> p x y
  celim2 :: prod p unit x y -> p x y
  cassoc :: prod p (prod q r) x y -> prod (prod p q) r x y
  cdisassoc :: prod (prod p q) r x y -> prod p (prod q r) x y
instance CMonoidal ProductQ (KQ ()) where
  cintro1 p = ProductQ (KQ ()) p
  cintro2 p = ProductQ p (KQ ())
  celim1 (ProductQ _ p) = p
  celim2 (ProductQ p _) = p
  cassoc (ProductQ p (ProductQ q r)) = ProductQ (ProductQ p q) r
  cdisassoc (ProductQ (ProductQ p q) r) = ProductQ p (ProductQ q r)
instance CMonoidal ComposeQ (ReflQ ()) where
  cintro1 p = ComposeQ (ReflQ ()) p
  cintro2 p = ComposeQ p (ReflQ ())
  celim1 (ComposeQ (ReflQ ()) p) = p
  celim2 (ComposeQ p (ReflQ ())) = p
  cassoc (ComposeQ p (ComposeQ q r)) = ComposeQ (ComposeQ p q) r
  cdisassoc (ComposeQ (ComposeQ p q) r) = ComposeQ p (ComposeQ q r)

class (forall q. CFunctor (prod q)) => CBifunctor prod where
  cbimap
    :: (forall x y. p x y -> p' x y)
    -> (forall x y. q x y -> q' x y)
    -> prod p q x y -> prod p' q' x y
instance CBifunctor ProductQ where
  cbimap f g (ProductQ p q) = ProductQ (f p) (g q)
instance CBifunctor ComposeQ where
  cbimap f g (ComposeQ p q) = ComposeQ (f p) (g q)

class (forall q. CFunctor (hom q)) => CProfunctor hom where
  cdimap
    :: (forall x y. p' x y -> p x y)
    -> (forall x y. q x y -> q' x y)
    -> hom p q x y -> hom p' q' x y
instance CProfunctor Quiver where cdimap f h (Quiver g) = Quiver (h . g . f)
instance CProfunctor ExtendQ where cdimap f h (ExtendQ g) = ExtendQ (h . g . f)
instance CProfunctor LiftQ where cdimap f h (LiftQ g) = LiftQ (h . g . f)
