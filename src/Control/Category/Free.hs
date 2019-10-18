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

* abstractly as @CFree path => path@,
  the class of left adjoints to the functor which
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
  , CPointed (..)
  , CApplicative (..)
  , CMonad (..)
  , CFree (..)
  , toPath
  , creverse
  , beforeAll
  , afterAll
  , Quiver (..)
  , EndoL (..)
  , EndoR (..)
  , KQ (..)
  , ApQ (..)
  , Op (..)
  , Iso (..)
  , IQ (..)
  , MaybeQ (..)
  , EitherQ (..)
  , ProductQ (..)
  ) where

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
  ctoMonoid f = getKQ . cfoldMap (KQ . f)
  {- | Map each element of the structure, and combine the results in a list.-}
  ctoList :: (forall x y. p x y -> a) -> c p x y -> [a]
  ctoList f = ctoMonoid (pure . f)
  {- | Map each element of a structure to an `Applicative` on a `Category`,
  evaluate from left to right, and combine the results.-}
  ctraverse_
    :: (Applicative m, Category q)
    => (forall x y. p x y -> m (q x y)) -> c p x y -> m (q x y)
  ctraverse_ f = getApQ . cfoldMap (ApQ . f)

{- | Generalizing `Traversable` to quivers.-}
class CFoldable c => CTraversable c where
  {- | Map each element of a structure to an `Applicative` on a quiver,
  evaluate from left to right, and collect the results.-}
  ctraverse
    :: Applicative m
    => (forall x y. p x y -> m (q x y)) -> c p x y -> m (c q x y)

{- | Embed a single quiver arrow with `csingleton`.-}
class CPointed c where csingleton :: p x y -> c p x y

{- | Generalize `Applicative` to quivers. -}
class (CFunctor c, CPointed c) => CApplicative c where
  cap :: c (Quiver p q) x y -> c p x y -> c q x y
  cap = czip getQuiver
  czip
    :: (forall x y z. p x y -> q x y -> r x y)
    -> c p x y -> c q x y -> c r x y
  czip f p q = (Quiver . f) `cmap` p `cap` q
  {-# MINIMAL cap | czip #-}

{- | Generalize `Monad` to quivers. -}
class (CFunctor c, CPointed c) => CMonad c where
  cjoin :: c (c p) x y -> c p x y
  cjoin = cbind id
  cbind :: (forall x y. p x y -> c q x y) -> c p x y -> c q x y
  cbind f p = cjoin (cmap f p)
  {-# MINIMAL cjoin | cbind #-}

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
creverse :: (CFoldable c, CFree path) => c p x y -> path (Op p) y x
creverse = getOp . cfoldMap (Op . csingleton . Op)

{- | Insert a given endo before each step. -}
beforeAll
  :: (CFoldable c, CFree path)
  => (forall x. p x x) -> c p x y -> path p x y
beforeAll sep = cfoldMap (\p -> csingleton sep >>> csingleton p)

{- | Insert a given endo before each step. -}
afterAll
  :: (CFoldable c, CFree path)
  => (forall x. p x x) -> c p x y -> path p x y
afterAll sep = cfoldMap (\p -> csingleton p >>> csingleton sep)

{- | Morphisms of quivers. -}
newtype Quiver p q x y = Quiver { getQuiver :: p x y -> q x y }
instance CFunctor (Quiver p) where cmap g (Quiver f) = Quiver (g . f)
instance CPointed (Quiver p) where csingleton q = Quiver (const q)
instance CApplicative (Quiver p) where
  cap (Quiver cf) (Quiver cq) = Quiver (\p -> getQuiver (cf p) (cq p))
instance CMonad (Quiver p) where
  cjoin (Quiver q) = Quiver (\p -> getQuiver (q p) p)

{- | Used in the default definition of `cfoldr`.-}
newtype EndoR p y x = EndoR {getEndoR :: forall z. p x z -> p y z}
instance x ~ y => Semigroup (EndoR p y x) where (<>) = (>>>)
instance x ~ y => Monoid (EndoR p x y) where mempty = id
instance Category (EndoR p) where
  id = EndoR id
  EndoR f1 . EndoR f2 = EndoR (f2 . f1)

{- | Used in the default definition of `cfoldr`.-}
newtype EndoL p x y = EndoL {getEndoL :: forall w . p w x -> p w y}
instance x ~ y => Semigroup (EndoL p x y) where (<>) = (>>>)
instance x ~ y => Monoid (EndoL p x y) where mempty = id
instance Category (EndoL p) where
  id = EndoL id
  EndoL f1 . EndoL f2 = EndoL (f1 . f2)

{- | Turn a `Monoid` into a `Category`,
used in the default definition of `ctoMonoid`.-}
newtype KQ m x y = KQ {getKQ :: m} deriving (Eq, Ord, Show)
instance (Semigroup m, x ~ y) => Semigroup (KQ m x y) where
  KQ f <> KQ g = KQ (f <> g)
instance (Monoid m, x ~ y) => Monoid (KQ m x y) where mempty = id
instance Monoid m => Category (KQ m) where
  id = KQ mempty
  KQ g . KQ f = KQ (f <> g)

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
instance Functor t => CFunctor (ApQ t) where
  cmap f (ApQ t) = ApQ (f <$> t)
instance Applicative t => CPointed (ApQ t) where
  csingleton = ApQ . pure
instance Applicative t => CApplicative (ApQ t) where
  czip f (ApQ tp) (ApQ tq) = ApQ (f <$> tp <*> tq)
instance Monad t => CMonad (ApQ t) where
  cbind f (ApQ t) = ApQ $ do
    p <- t
    getApQ $ f p

{- | Reverse all the arrows in a quiver.-}
newtype Op c x y = Op {getOp :: c y x} deriving (Eq, Ord, Show)
instance (Category c, x ~ y) => Semigroup (Op c x y) where (<>) = (>>>)
instance (Category c, x ~ y) => Monoid (Op c x y) where mempty = id
instance Category c => Category (Op c) where
  id = Op id
  Op g . Op f = Op (f . g)
instance CFunctor Op where cmap f = Op . f . getOp

{- | Turn all arrows in a quiver into bidirectional edges.-}
data Iso c x y = Iso
  { up :: c x y
  , down :: c y x
  } deriving (Eq, Ord, Show)
instance (Category c, x ~ y) => Semigroup (Iso c x y) where (<>) = (>>>)
instance (Category c, x ~ y) => Monoid (Iso c x y) where mempty = id
instance Category c => Category (Iso c) where
  id = Iso id id
  (Iso yz zy) . (Iso xy yx) = Iso (yz . xy) (yx . zy)
instance CFunctor Iso where
  cmap f (Iso u d) = Iso (f u) (f d)

{- | The identity functor on quivers. -}
newtype IQ c x y = IQ {getIQ :: c x y} deriving (Eq, Ord, Show)
instance (Category c, x ~ y) => Semigroup (IQ c x y) where (<>) = (>>>)
instance (Category c, x ~ y) => Monoid (IQ c x y) where mempty = id
instance Category c => Category (IQ c) where
  id = IQ id
  IQ g . IQ f = IQ (g . f)
instance CFunctor IQ where cmap f = IQ . f . getIQ
instance CFoldable IQ where cfoldMap f (IQ c) = f c
instance CTraversable IQ where ctraverse f (IQ c) = IQ <$> f c
instance CPointed IQ where csingleton = IQ

{- | Generalize `Maybe` to quivers.
If @p@ is a @Semigroupoid@, @MaybeQ p@ can be
made into a `Category`. -}
data MaybeQ p x y where
  NoneQ :: MaybeQ p x x
  OneQ :: p x y -> MaybeQ p x y
deriving instance (Eq (p x y)) => Eq (MaybeQ p x y)
deriving instance (Ord (p x y)) => Ord (MaybeQ p x y)
deriving instance (Show (p x y)) => Show (MaybeQ p x y)
instance CFunctor MaybeQ where
  cmap _ NoneQ = NoneQ
  cmap f (OneQ p) = OneQ (f p)
instance CFoldable MaybeQ where
  cfoldMap _ NoneQ = id
  cfoldMap f (OneQ p) = f p
instance CTraversable MaybeQ where
  ctraverse _ NoneQ = pure NoneQ
  ctraverse f (OneQ p) = OneQ <$> f p
instance CPointed MaybeQ where csingleton = OneQ
instance CApplicative MaybeQ where
  cap NoneQ _ = NoneQ
  cap _ NoneQ = NoneQ
  cap (OneQ (Quiver f)) (OneQ p) = OneQ (f p)
instance CMonad MaybeQ where
  cjoin NoneQ = NoneQ
  cjoin (OneQ NoneQ) = NoneQ
  cjoin (OneQ (OneQ p)) = OneQ p

{- | Generalize `Either` to quivers.
If @m@ is a `Monoid` and @p@ is a @Semigroupoid@,
@EitherQ m p@ can be made into a `Category`. -}
data EitherQ m p x y where
  LeftQ :: m -> EitherQ m p x x
  RightQ :: p x y -> EitherQ m p x y
deriving instance (Eq m, Eq (p x y)) => Eq (EitherQ m p x y)
deriving instance (Ord m, Ord (p x y)) => Ord (EitherQ m p x y)
deriving instance (Show m, Show (p x y)) => Show (EitherQ m p x y)
instance CFunctor (EitherQ m) where
  cmap _ (LeftQ m) = LeftQ m
  cmap f (RightQ p) = RightQ (f p)
instance CFoldable (EitherQ m) where
  cfoldMap _ (LeftQ _) = id
  cfoldMap f (RightQ p) = f p
instance CTraversable (EitherQ m) where
  ctraverse _ (LeftQ m) = pure (LeftQ m)
  ctraverse f (RightQ p) = RightQ <$> f p
instance CPointed (EitherQ m) where csingleton = RightQ
instance CApplicative (EitherQ m) where
  cap (LeftQ m) _ = LeftQ m
  cap _ (LeftQ m) = LeftQ m
  cap (RightQ (Quiver f)) (RightQ p) = RightQ (f p)
instance CMonad (EitherQ m) where
  cjoin (LeftQ m) = LeftQ m
  cjoin (RightQ (LeftQ m)) = LeftQ m
  cjoin (RightQ (RightQ p)) = RightQ p

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
instance CFunctor (ProductQ p) where cmap f (ProductQ p q) = ProductQ p (f q)
instance CFoldable (ProductQ p) where cfoldMap f (ProductQ _ q) = f q
instance CTraversable (ProductQ p) where
  ctraverse f (ProductQ p q) = ProductQ p <$> f q
