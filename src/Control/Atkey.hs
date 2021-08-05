{-# language PolyKinds #-}
{-# language RankNTypes #-}

-- | A polykinded and modified copy of @Data.Functor.Indexed@ from the moribund
-- @indexed@ package.
module Control.Atkey
  ( IxFunctor (..)
  , IxApply (..)
  , IxApplicative (..)
  , IxConst (..)
  ) where

import Control.Category
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

newtype IxConst d x y z = IxConst { getIxConst :: d x y }
instance IxFunctor (IxConst d) where
  imap _ (IxConst x) = IxConst x
instance Category d => IxApply (IxConst d) where
  iap (IxConst x) (IxConst y) = IxConst (y . x)
instance Category d => IxApplicative (IxConst d) where
  ipure _ = IxConst id
