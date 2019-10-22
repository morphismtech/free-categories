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

* abstractly as `CFree` @path => path@,
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
  , CStrong (..)
  , CApplicative (..)
  , CMonad (..)
  , CFree (..)
  , toPath
  , creverse
  , beforeAll
  , afterAll
  , KQ (..)
  , ProductQ (..)
  , assocQ
  , disassocQ
  , productQ
  , swapQ
  , Quiver (..)
  , EndoL (..)
  , EndoR (..)
  , ApQ (..)
  , OpQ (..)
  , IsoQ (..)
  , IQ (..)
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

{- | Strength for quiver endofunctors with respect to `ProductQ`.

/Note:/ Every `Functor` is strong with respect to @(,)@,
but not every `CFunctor` is strong with respect to @ProductQ@.

prop> csecond . productQ id csecond . disassocQ = cmap disassocQ . csecond
prop> cmap sndQ . csecond = sndQ

`cfirst` and `csecond` are related as
prop> cfirst = cmap swapQ . csecond . swapQ
prop> csecond = cmap swapQ . cfirst . swapQ
-}
class CFunctor c => CStrong c where
  cfirst :: ProductQ (c p) q x y -> c (ProductQ p q) x y
  cfirst = cmap swapQ . csecond . swapQ
  csecond :: ProductQ p (c q) x y -> c (ProductQ p q) x y
  csecond = cmap swapQ . cfirst . swapQ
  {-# MINIMAL cfirst | csecond #-}

{- | Generalize `Applicative` to quivers.

The laws of a strong lax monoidal endofunctor hold.

>>> let cunit = csingleton (KQ ())
>>> let ctimes = czip ProductQ

prop> cmap (f `productQ` g) (p `ctimes` q) = cmap f p `ctimes` cmap g q
prop> cmap sndQ (cunit `ctimes` q) = q
prop> cmap fstQ (p `ctimes` cunit) = p
prop> cmap assocQ (p `ctimes` (q `ctimes` r)) = (p `ctimes` q) `ctimes` r

The functions `cap` and `czip` are related as

prop> cap = czip getQuiver
prop> czip f p q = (Quiver . f) `cmap` p `cap` q
-}
class (CStrong c, CPointed c) => CApplicative c where
  cap :: c (Quiver p q) x y -> c p x y -> c q x y
  cap = czip getQuiver
  czip
    :: (forall x y. p x y -> q x y -> r x y)
    -> c p x y -> c q x y -> c r x y
  czip f p q = (Quiver . f) `cmap` p `cap` q
  {-# MINIMAL cap | czip #-}

{- | Generalize `Monad` to quivers.

Associativity and left and right identity laws hold.

prop> cjoin . cjoin = cjoin . cmap cjoin
prop> cjoin . csingleton = id
prop> cjoin . cmap csingleton = id

The functions `cbind` and `cjoin` are related as

prop> cjoin = cbind id
prop> cbind f p = cjoin (cmap f p)
-}
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
creverse :: (CFoldable c, CFree path) => c p x y -> path (OpQ p) y x
creverse = getOpQ . cfoldMap (OpQ . csingleton . OpQ)

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

{- | Turn a `Monoid` into a `Category`,
used in the default definition of `ctoMonoid`.-}
newtype KQ r x y = KQ {getKQ :: r} deriving (Eq, Ord, Show)
instance (Semigroup m, x ~ y) => Semigroup (KQ m x y) where
  KQ f <> KQ g = KQ (f <> g)
instance (Monoid m, x ~ y) => Monoid (KQ m x y) where mempty = id
instance Monoid m => Category (KQ m) where
  id = KQ mempty
  KQ g . KQ f = KQ (f <> g)

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

{- | Associator of `ProductQ`.-}
assocQ :: ProductQ p (ProductQ q r) x y -> ProductQ (ProductQ p q) r x y
assocQ (ProductQ p (ProductQ q r)) = ProductQ (ProductQ p q) r

{- | Inverse associator of `ProductQ`.-}
disassocQ :: ProductQ (ProductQ p q) r x y -> ProductQ p (ProductQ q r) x y
disassocQ (ProductQ (ProductQ p q) r) = ProductQ p (ProductQ q r)

{- | Map over the `fstQ` and `sndQ` of a `ProductQ`.-}
productQ
  :: (p0 x y -> p1 x y)
  -> (q0 x y -> q1 x y)
  -> ProductQ p0 q0 x y
  -> ProductQ p1 q1 x y
productQ f g (ProductQ p q) = ProductQ (f p) (g q)

{- | Symmetry of `ProductQ`.-}
swapQ :: ProductQ p q x y -> ProductQ q p x y
swapQ (ProductQ p q) = ProductQ q p

{- | Morphism components of quivers.

Quivers form a Cartesian closed category with
  * product `ProductQ`
  * unit `KQ ()`
  * internal hom `Quiver`
-}
newtype Quiver p q x y = Quiver { getQuiver :: p x y -> q x y }
instance CFunctor (Quiver p) where cmap g (Quiver f) = Quiver (g . f)
instance CPointed (Quiver p) where csingleton q = Quiver (const q)
instance CStrong (Quiver p) where
  csecond (ProductQ p (Quiver f)) = Quiver (ProductQ p . f)
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

{- | Used in the default definition of `cfoldl`.-}
newtype EndoL p x y = EndoL {getEndoL :: forall w . p w x -> p w y}
instance x ~ y => Semigroup (EndoL p x y) where (<>) = (>>>)
instance x ~ y => Monoid (EndoL p x y) where mempty = id
instance Category (EndoL p) where
  id = EndoL id
  EndoL f1 . EndoL f2 = EndoL (f1 . f2)

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
instance Functor t => CStrong (ApQ t) where
  csecond (ProductQ p (ApQ t)) = ApQ (ProductQ p <$> t)
instance Applicative t => CApplicative (ApQ t) where
  czip f (ApQ tp) (ApQ tq) = ApQ (f <$> tp <*> tq)
instance Monad t => CMonad (ApQ t) where
  cbind f (ApQ t) = ApQ $ do
    p <- t
    getApQ $ f p

{- | Reverse all the arrows in a quiver.-}
newtype OpQ c x y = OpQ {getOpQ :: c y x} deriving (Eq, Ord, Show)
instance (Category c, x ~ y) => Semigroup (OpQ c x y) where (<>) = (>>>)
instance (Category c, x ~ y) => Monoid (OpQ c x y) where mempty = id
instance Category c => Category (OpQ c) where
  id = OpQ id
  OpQ g . OpQ f = OpQ (f . g)
instance CFunctor OpQ where cmap f = OpQ . f . getOpQ

{- | Turn all arrows in a quiver into bidirectional edges.-}
data IsoQ c x y = IsoQ
  { up :: c x y
  , down :: c y x
  } deriving (Eq, Ord, Show)
instance (Category c, x ~ y) => Semigroup (IsoQ c x y) where (<>) = (>>>)
instance (Category c, x ~ y) => Monoid (IsoQ c x y) where mempty = id
instance Category c => Category (IsoQ c) where
  id = IsoQ id id
  (IsoQ yz zy) . (IsoQ xy yx) = IsoQ (yz . xy) (yx . zy)
instance CFunctor IsoQ where
  cmap f (IsoQ u d) = IsoQ (f u) (f d)

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
instance CStrong IQ where csecond (ProductQ p (IQ q)) = IQ (ProductQ p q)
instance CApplicative IQ where czip f (IQ p) (IQ q) = IQ (f p q)
instance CMonad IQ where cjoin = getIQ

data ReflQ r x y where ReflQ :: r -> ReflQ r x x

data ComposeQ p q x y where ComposeQ :: p y z -> q x y -> ComposeQ p q x z
instance CFunctor (ComposeQ p) where
  cmap f (ComposeQ p q) = ComposeQ p (f q)
instance Category p => CPointed (ComposeQ p) where
  csingleton = ComposeQ id
instance Category p => CMonad (ComposeQ p) where
  cjoin (ComposeQ p' (ComposeQ p q)) = ComposeQ (p' . p) q

newtype ExtendQ p q x y = ExtendQ {getExtendQ :: forall w. p w x -> q w y}
instance CFunctor (ExtendQ p) where
  cmap g (ExtendQ f) = ExtendQ (g . f)
instance (p ~ q, x ~ y) => Semigroup (ExtendQ p q x y) where (<>) = (>>>)
instance (p ~ q, x ~ y) => Monoid (ExtendQ p q x y) where mempty = id
instance p ~ q => Category (ExtendQ p q) where
  id = ExtendQ id
  ExtendQ g . ExtendQ f = ExtendQ (g . f)

newtype LiftQ p q x y = LiftQ {getLiftQ :: forall z. p y z -> q x z}
instance CFunctor (LiftQ p) where
  cmap g (LiftQ f) = LiftQ (g . f)
instance (p ~ q, x ~ y) => Semigroup (LiftQ p q x y) where (<>) = (>>>)
instance (p ~ q, x ~ y) => Monoid (LiftQ p q x y) where mempty = id
instance p ~ q => Category (LiftQ p q) where
  id = LiftQ id
  LiftQ f . LiftQ g = LiftQ (g . f)
