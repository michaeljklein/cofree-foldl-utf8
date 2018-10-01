{-# LANGUAGE RankNTypes #-}

module Control.Foldl.Utils where

import Control.Foldl
import Control.Monad

-- | Advance a `Fold` one step
advanceF :: a -> Fold a b -> Fold a b
advanceF x f = (`purely` f) $ \stp ini ext -> Fold stp (stp ini x) ext

-- | Advance a `FoldM` one step
advanceFM :: Monad m => a -> FoldM m a b -> FoldM m a b
advanceFM x f = (`impurely` f) $ \stp ini ext -> FoldM stp (ini >>= flip stp x) ext

-- | Extract a result from a `FoldM`
extractM :: Monad m => FoldM m a b -> m b
extractM = flip Control.Foldl.foldM Nothing

-- | Join an inner `Monad`ic value in a `FoldM`
joinFoldM :: Monad m => FoldM m a (m b) -> FoldM m a b
joinFoldM f = (`impurely` f) $ \stp ini ext -> FoldM stp ini (join . ext)

hoistFoldM :: (forall x. m x -> n x) -> FoldM m a b -> FoldM n a b
hoistFoldM f g = (`impurely` g) $ \stp ini ext -> FoldM (\x y -> f (stp x y)) (f ini) (f . ext)


