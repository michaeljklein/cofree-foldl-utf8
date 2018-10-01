{-# LANGUAGE DeriveFunctor #-}

module Data.Range where

-- | Possibly-empty strict ranges
data Range a = Range0
             | Range1 !a
             | Range2 !a !a
             deriving (Eq, Ord, Read, Show, Functor)

instance Ord a => Monoid (Range a) where
  mempty = Range0

  mappend Range0 y = y
  mappend x Range0 = x
  mappend (Range1 x) (Range1 y) = case compare x y of
                                    LT -> Range2 x y
                                    EQ -> Range1 x
                                    GT -> Range2 y x
  mappend (Range1 x  ) (Range2 y z) = Range2 (min x y) (max x z)
  mappend (Range2 x y) (Range1 z  ) = Range2 (min x z) (max y z)
  mappend (Range2 x y) (Range2 z w) = Range2 (min x z) (max y w)


instance Applicative Range where
  pure = Range1

  Range0 <*> _ = Range0
  _ <*> Range0 = Range0
  Range1 f <*> x = fmap f x
  f <*> Range1 x = fmap ($ x) f
  Range2 f g <*> Range2 x y = Range2 (f x) (g y)


