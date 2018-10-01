{-# LANGUAGE RankNTypes #-}

module Control.Comonad.CofreeF where

import Control.Applicative
import Control.Comonad
import Control.Comonad.Cofree
import Control.Monad.Trans.Maybe
import Control.Monad
import Control.Foldl
import Control.Foldl.Utils

-- | A `Functor` composed with its `Cofree` `Comonad`
newtype CofreeF f a = CofreeF { runCofreeF :: f (Cofree f a) }

instance Functor f => Functor (CofreeF f) where
  fmap f (CofreeF x) = CofreeF (fmap f <$> x)

instance Comonad f => Comonad (CofreeF f) where
  extract = extract . extract . runCofreeF

  duplicate (CofreeF x) = CofreeF . flip fmap x $ \z@(y :< ys) -> CofreeF (const z <$> ys) :< (runCofreeF . duplicate . CofreeF $ ys)

instance Alternative f => Applicative (CofreeF f) where
  pure = CofreeF . pure . pure

  CofreeF f <*> CofreeF x = CofreeF (liftA2 (<*>) f x)

instance (Alternative f, Monad f) => Monad (CofreeF f) where
  CofreeF x >>= f = CofreeF $ do
    (x' :< xs) <- x
    (y :< ys) <- (runCofreeF . f) x'
    let zs = runCofreeF $ orDown (CofreeF ys) (CofreeF xs >>= f)
    return (y :< zs)

instance Alternative f => Alternative (CofreeF f) where
  empty = CofreeF empty
  (<|>) = orDown

instance Foldable f => Foldable (CofreeF f) where
  foldr f x (CofreeF xs) = foldr (flip (foldr f)) x xs

instance Traversable f => Traversable (CofreeF f) where
  traverse f (CofreeF x) = CofreeF <$> traverse (traverse f) x

-- | Hoist a natural transformation to `CofreeF`
hoistCofreeF :: (Functor f, Functor g) => (forall x. f x -> g x) -> CofreeF f a -> CofreeF g a
hoistCofreeF f (CofreeF x) = CofreeF $ fmap (\(~(y :< ys)) -> y :< runCofreeF (hoistCofreeF f (CofreeF ys))) (f x)

-- | Convert the internal `Functor` of `CofreeF` from
-- `Maybe` to any `Alternative`
hoistCofreeAlt :: Alternative f => CofreeF Maybe a -> CofreeF f a
hoistCofreeAlt = hoistCofreeF altMaybe


-- | Effectively attaches the second at the first level where the first fails,
-- e.g. for CofreeF Maybe, this is isomorphic to (<>)
orDown :: Alternative f => CofreeF f a -> CofreeF f a -> CofreeF f a
orDown (CofreeF x) cy@(CofreeF y) = CofreeF ((\(z :< zs) -> z :< runCofreeF (orDown (CofreeF zs) cy)) <$> x <|> y)

-- | Convert `Maybe` to any `Alternative`
altMaybe :: Alternative f => Maybe a -> f a
altMaybe = maybe empty pure

-- | Convert the internal `Functor` of `CofreeF` from
-- `Maybe` to any `Alternative`.
altMaybeT :: MonadPlus m => MaybeT m a -> m a
altMaybeT (MaybeT x) = x >>= maybe mzero return


spanCofreeF :: Monad m => (a -> m Bool) -> FoldM m a b -> CofreeF m a -> m (b, CofreeF m a)
spanCofreeF p f cx@(CofreeF x) = do
  (y :< ys) <- x
  p' <- p y
  (`impurely` f) $ \stp ini ext -> do
    ini' <- ini
    if p'
       then do
         ini'' <- stp ini' y
         spanCofreeF' p stp ini'' ext (CofreeF ys)
       else do
         ext' <- ext ini'
         return (ext', cx)

spanCofreeF' :: Monad m =>
                (a -> m Bool)
             -> (x -> a -> m x)
             -> x
             -> (x -> m b)
             -> CofreeF m a
             -> m (b, CofreeF m a)
spanCofreeF' p stp ini ext cx@(CofreeF x) = do
  (y :< ys) <- x
  p' <- p y
  if p'
     then do
       ini' <- stp ini y
       spanCofreeF' p stp ini' ext (CofreeF ys)
     else do
       ext' <- ext ini
       return (ext', cx)


foldCofreeF :: Monad m => (a -> m b) -> FoldM m b c -> CofreeF (MaybeT m) a -> m c
foldCofreeF f g (CofreeF (MaybeT x)) = do
  x' <- x
  case x' of
    Nothing -> extractM g
    ~(Just (y :< ys)) -> do
      y' <- f y
      foldCofreeF f (advanceFM y' g) (CofreeF ys)



