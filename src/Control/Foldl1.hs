{-# LANGUAGE RankNTypes #-}


module Control.Foldl1 where

import Control.Foldl
import Control.Foldl.Utils
import Control.Comonad
import Data.Functor.Identity


-- | A `Fold` over non-empty inputs
newtype Fold1 a b = Fold1 { runFold1 :: a -> Fold (a, a) b }

-- | A `FoldM` over non-empty inputs
newtype FoldM1 m a b = FoldM1 { runFoldM1 :: a -> FoldM m (a, a) b }


toFold1 :: Fold a b -> Fold1 a b
toFold1 f = (`purely` f) $ \stp ini ext -> Fold1 (\x -> Fold (\x ~(_, y) -> stp x y) (stp ini x) ext)

toFoldM1 :: Monad m => FoldM m a b -> FoldM1 m a b
toFoldM1 f = (`impurely` f) $ \stp ini ext -> FoldM1 (\x -> FoldM (\x ~(_, y) -> stp x y) (ini >>= flip stp x) ext)


-- | Given a default result, we can transform a `Fold` that requires an initial
--   value and folds over @(prev value, current value)@ into a simple `Fold`.
fold1 :: b -> Fold1 a b -> Fold a b
fold1 x0 (Fold1 f) =
  Fold
    (\x y -> Just $ case x of
                      Nothing -> (y, f y)
                      ~(Just (yPrev, f')) -> runIdentity $ do
                        (`purely` f') $ \stp ini ext -> do
                          let ini'' = stp ini (yPrev, y)
                          let f'' = Fold stp ini'' ext
                          return (y, f'')
    )
    Nothing
    (maybe x0 (\((_, x)) -> extract x))

-- | `foldPairF` for `FoldM`
foldM1 :: Monad m => b -> FoldM1 m a b -> FoldM m a b
foldM1 x0 (FoldM1 f) =
  FoldM
    (\x y -> Just <$> case x of
                        Nothing -> do
                          return (y, f y)
                        ~(Just (yPrev, f')) -> do
                          (`impurely` f') $ \stp ini ext -> do
                            ini'  <- ini
                            let ini'' = stp ini' (yPrev, y)
                            let f'' = FoldM stp ini'' ext
                            return (y, f'')
    )
    (return Nothing)
    (maybe (return x0) (\(~(_, x)) -> extractM x))


