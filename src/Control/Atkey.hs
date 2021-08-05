{-# language PolyKinds #-}
{-# language RankNTypes #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language StandaloneDeriving #-}
{-# language ScopedTypeVariables #-}
{-# language InstanceSigs #-}

-- | A polykinded and modified copy of @Data.Functor.Indexed@ from the moribund
-- @indexed@ package.
module Control.Atkey
  ( IxFunctor (..)
  , IxApply (..)
  , IxApplicative (..)
  , IxConst (..)
  , WrappedApplicative (..)
  ) where

import Control.Category
import Data.Coerce
import Data.Quiver.Internal
import Control.Applicative (liftA2)
import Prelude hiding (id, (.))

class IxFunctor f where
  infixl 4 `imap`
  imap :: (a -> b) -> f j k a -> f j k b

class IxFunctor m => IxApply m where
  {-# MINIMAL iap | iliftA2 #-}
  infixl 4 `iap`
  iap :: m i j (a -> b) -> m j k a -> m i k b
  iap = iliftA2 id
  iliftA2 :: (a -> b -> c) -> m i j a -> m j k b -> m i k c
  iliftA2 f x y = f `imap` x `iap` y

class IxApply m => IxApplicative m where
  ipure :: a -> m i i a

newtype WrappedApplicative f x y a = WrappedApplicative { getWrappedApplicative :: f a }
  deriving (Eq, Ord, Show, Functor, Applicative)
instance Functor f => IxFunctor (WrappedApplicative f) where
  imap = ((WrappedApplicative .) . (. getWrappedApplicative)) #. fmap
instance Applicative f => IxApply (WrappedApplicative f) where
  iap :: forall a b i j k.
    WrappedApplicative f i j (a -> b) -> WrappedApplicative f j k a -> WrappedApplicative f i k b
  iap = coerce ((<*>) :: f (a -> b) -> f a -> f b)

  iliftA2 :: forall a b c i j k.
    (a -> b -> c) -> WrappedApplicative f i j a -> WrappedApplicative f j k b -> WrappedApplicative f i k c
  iliftA2 = coerce (liftA2 :: (a -> b -> c) -> f a -> f b -> f c)
instance Applicative f => IxApplicative (WrappedApplicative f) where
  ipure = WrappedApplicative #. pure

newtype IxConst d x y z = IxConst { getIxConst :: d x y }
  deriving (Eq, Ord, Show)
instance IxFunctor (IxConst d) where
  imap _ (IxConst x) = IxConst x
instance Category d => IxApply (IxConst d) where
  iap (IxConst x) (IxConst y) = IxConst (y . x)
instance Category d => IxApplicative (IxConst d) where
  ipure _ = IxConst id
