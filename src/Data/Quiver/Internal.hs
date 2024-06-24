module Data.Quiver.Internal where
import Data.Coerce

-- Borrowed from Data.Profunctor and specialized to ->

infixr 9 #.
(#.) :: Coercible b c => p b c -> (a -> b) -> a -> c
(#.) _ = coerce

infixl 8 .#
(.#) :: Coercible a b => (b -> c) -> p a b -> a -> c
f .# _ = coerce f
