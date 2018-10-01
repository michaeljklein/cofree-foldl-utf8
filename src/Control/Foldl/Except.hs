{-# LANGUAGE RankNTypes #-}

module Control.Foldl.Except where


import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Except
import Control.Monad.Trans.Class
import Control.Foldl
import Control.Foldl.Utils
import Data.Bifunctor
import Control.Applicative
import Control.Comonad

import Control.Foldl1
import Control.Comonad.CofreeF
import Control.Comonad
import Control.Comonad.Cofree
import Control.Monad.Fail

joinEither :: Either a a -> a
joinEither  (Left  x) = x
joinEither ~(Right x) = x

-- | Monadic fold with early result (before folding over an entire input)
--
-- For example, could define:
--
-- @
--  countIndent :: FoldE Char m Int
--  countIndent = FoldE (FoldM (\i y -> if isSpace y then return (i+1) else throwE i) 0 return)
-- @
--
newtype FoldE a m b = FoldE { runFoldE :: FoldM (ExceptT b m) a b }

instance Monad m => Functor (FoldE a m) where
  fmap f (FoldE x) = FoldE (fmap f (hoistFoldM (mapExceptT (fmap (first f))) x))

-- | Extract the current result
extractE :: Monad m => FoldE a m b -> m b
extractE = fmap joinEither . runExceptT . extractM . runFoldE

-- | Consume no input and return the given value
pureFoldE :: Monad m => b -> FoldE a m b
pureFoldE x = FoldE (FoldM (\_ _ -> throwE x) (throwE x) (\_ -> throwE x))

-- | returnFoldE and pureFoldE should be pretty quick, they end the `FoldE` at every point.
returnFoldE :: Monad m => m b -> FoldE a m b
returnFoldE x = FoldE (FoldM (\_ _ -> lift x >>= throwE) (lift x >>= throwE) (\_ -> lift x >>= throwE))


-- matchStack :: [(Char, loc)]
--
-- parseOpen { openStack = os, matchedStack = ms } c | isOpen (extract c) = do
--   return $ (extract c, ask c) : os
--
-- parseClose { openStack = ((c,l,x):os), matchedStack = ms } d | isClosed c (extract d) = do
--   (c, l, ask d, x) : ms
--
-- parseClose { openStack = [], matchedStack = ((c,l,l',x):ms), closeStack = cs } d | isClosed1 (extract d) = do
--
-- parseNeither { openStack = ((c,l,x):os) } d = do
--   x' <- stp x d
--   (c, l, x') : os
--
-- parseNeither { openStack = [], matchedStack  } d = do
--   x' <- stp x d
--   (c, l, x') : os
--
--
-- (
-- ( x y ..
-- )
-- ()
-- (x) -- foldM (Just x)
-- (x y) -- foldM (x y)
-- x
-- x y


-- | Given a default and `Foldable` collection of ways to parse a @b@,
-- try each (only rewinding up to a single char) and return (Left the_first_to_throwE (Just x)),
-- or recurse.
foldEs :: (Monad m, Foldable t) =>
           FoldE c m (Maybe b)
     -> t (FoldE c m (Maybe b))
     -> CofreeF (MaybeT m) c
     -> CofreeF (MaybeT m) (Either b c)
foldEs f xs ys = foldr (\g -> fmap (first joinEither) . foldE1 g) (foldE0 f ys) xs

foldEs_ :: (Monad m, Foldable t) =>
        t (FoldE c m (Maybe b))
     -> CofreeF (MaybeT m) c
     -> CofreeF (MaybeT m) (Either b c)
foldEs_ = foldEs (pureFoldE Nothing)


-- To ensure that there are no loops like with (many canFail), we always loop until
-- failure and then always return the input.

-- | `foldE1` may be combined with `foldE0` as follows to combine arbitrarily large numbers of `FoldE`s:
--
-- @
-- \f g -> foldE1 g . foldE0 f
--   :: Monad m =>
--         FoldE a m (Maybe b)
--      -> FoldE a m (Maybe c)
--      -> CofreeF (MaybeT m) a
--      -> CofreeF (MaybeT m) (Either (Either b c) a)
--
-- \f g h -> foldE1 h . foldE1 g . foldE0 f
--   :: Monad m =>
--         FoldE a m (Maybe b)
--      -> FoldE a m (Maybe c1)
--      -> FoldE a m (Maybe c2)
--      -> CofreeF (MaybeT m) a
--      -> CofreeF (MaybeT m) (Either (Either (Either b c1) c2) a)
-- @
--
-- Or, we may not want to preserve distinct `FoldE` types:
--
-- @
-- \f g -> fmap (first joinEither) . foldE1 g . foldE0 f
--   :: Monad m =>
--         FoldE c m (Maybe b)
--      -> FoldE c m (Maybe b)
--      -> CofreeF (MaybeT m) c
--      -> CofreeF (MaybeT m) (Either b c)
--
-- \f g h -> fmap (first joinEither) . foldE1 h . fmap (first joinEither) . foldE1 g . foldE0 f
--   :: Monad m =>
--         FoldE c m (Maybe b)
--      -> FoldE c m (Maybe b)
--      -> FoldE c m (Maybe b)
--      -> CofreeF (MaybeT m) c
--      -> CofreeF (MaybeT m) (Either b c)
-- @
--
--
foldE1 :: Monad m => FoldE a m (Maybe c) -> CofreeF (MaybeT m) (Either b a) -> CofreeF (MaybeT m) (Either (Either b c) a)
foldE1 (FoldE f) (CofreeF (MaybeT x)) = CofreeF . MaybeT $ do
  (`impurely` f) $ \stp (ExceptT ini0) ext -> do
    eitherIni <- ini0
    let retX = fmap (fmap (first Left)) <$> x -- never return from f
    case eitherIni of
      Left Nothing -> do -- no input state
        retX -- never return from f
      Left (Just y) -> do -- singleton input state
        return . Just $ (Left (Right y) :< MaybeT retX) -- return the single result then never again from f
      Right ini -> do
        x' <- x
        case x' of
          Nothing -> do
            return Nothing
          (Just (Left y :< MaybeT ys)) -> do
            ys' <- ys
            return . Just $ (Left (Left y) :< MaybeT (foldE1' stp ini ext ys'))
          ~(Just (Right y :< MaybeT ys)) -> do
            eitherIni' <- runExceptT $ stp ini y
            case eitherIni' of
              Left Nothing -> do
                fmap (fmap (first Left)) <$> x
              Left (Just y) -> do
                return . Just $ (Left (Right y) :< MaybeT (fmap (fmap (first Left)) <$> ys))
              Right ini' -> do
                ys' <- ys
                foldE1' stp ini' ext ys'

foldE1' :: Monad m => (x -> a -> ExceptT (Maybe c) m x)
             -> x
             -> (x -> ExceptT (Maybe c) m (Maybe c))
             -> Maybe (Cofree (MaybeT m) (Either b a))
             -> m (Maybe (Cofree (MaybeT m) (Either (Either b c) a)))
foldE1' stp ini ext x = do
  case x of
    Nothing -> do
      return Nothing
    (Just (Left y :< MaybeT ys)) -> do
      ys' <- ys
      return . Just $ (Left (Left y) :< MaybeT (foldE1' stp ini ext ys'))
    ~(Just (Right y :< MaybeT ys)) -> do
      eitherIni' <- runExceptT $ stp ini y
      case eitherIni' of
        Left Nothing -> do
          return $ fmap (first Left) <$> x
        Left (Just y) -> do
          return . Just $ (Left (Right y) :< MaybeT (fmap (fmap (first Left)) <$> ys))
        Right ini' -> do
          ys' <- ys
          foldE1' stp ini' ext ys'


foldE0 :: Monad m => FoldE a m (Maybe b) -> CofreeF (MaybeT m) a -> CofreeF (MaybeT m) (Either b a)
foldE0 (FoldE f) (CofreeF (MaybeT x)) = CofreeF . MaybeT $
  (`impurely` f) $ \stp ini ext -> do
    eitherIni <- runExceptT ini
    let retX = fmap (fmap return) <$> x
    case eitherIni of
      Left Nothing -> do
        retX
      Left (Just y) -> do
        return . Just $ (Left y :< MaybeT retX)
      Right ini -> do
        x' <- x
        flip (maybe (return Nothing)) x' $ \(y :< MaybeT ys) -> do
          ys' <- ys
          foldE0' stp (stp ini y) ext ys'

foldE0' :: Monad m => (x -> a -> ExceptT (Maybe b) m x)
             -> ExceptT (Maybe b) m x
             -> (x -> ExceptT (Maybe b) m (Maybe b))
             -> Maybe (Cofree (MaybeT m) a)
             -> m (Maybe (Cofree (MaybeT m) (Either b a)))
foldE0' stp (ExceptT ini0) ext x = do
  eitherIni <- ini0
  let retX = return $ fmap return <$> x
  case eitherIni of
    Left Nothing -> do
      retX
    Left (Just y) -> do
      return . Just $ (Left y :< MaybeT retX)
    Right ini -> case x of
                   Nothing -> do
                     ini' <- joinEither <$> runExceptT (ext ini)
                     case ini' of
                       Nothing -> do
                         retX
                       ~(Just y) -> do
                         return (Just (Left y :< MaybeT retX))
                   ~(Just (y :< MaybeT ys)) -> do
                     ys' <- ys
                     foldE0' stp (stp ini y) ext ys'

-- | `FoldE` for non-empty inputs
newtype Fold1E a m b = Fold1E { runFold1E :: FoldM1 (ExceptT b m) a b }

fold1E :: Monad m => b -> Fold1E a m b -> FoldE a m b
fold1E x (Fold1E f) = FoldE (foldM1 x f)

foldIf1 :: Monad m => (a -> Bool) -> Fold1E a m (Maybe b) -> FoldE a m (Maybe b)
foldIf1 p (Fold1E (FoldM1 f)) = fold1E Nothing $
  Fold1E . FoldM1 $ \x ->
    (if p x
        then id
        else runFoldE
           . returnFoldE
           . extractE
           . FoldE
    ) (f x)


span1E :: Monad m => (a -> Bool) -> (a -> a -> MaybeT m b) -> Fold1E a m (Maybe b)
span1E p f = Fold1E . FoldM1 $ \x0 ->
  FoldM
    (\_ (_, y) -> if p y
                     then return ()
                     else do
                       z <- lift . runMaybeT $ f x0 y
                       throwE z
    )
    (if p x0
        then return ()
        else do
          z <- lift . runMaybeT $ f x0 x0
          throwE z
    )
    (\_ -> throwE Nothing) -- can only succeed on a value or init, using throwE

span2E :: Monad m => (a -> a -> Bool) -> (a -> a -> MaybeT m b) -> Fold1E a m (Maybe b)
span2E p f = Fold1E . FoldM1 $ \x0 ->
  FoldM
    (\_ (x, y) -> if p x y
                     then return ()
                     else do
                       z <- lift . runMaybeT $ f x0 y
                       throwE z
    )
    (return ())
    (\_ -> throwE Nothing) -- can only succeed on a value, using throwE



spanIfE2 :: Monad m => (a -> Bool) -> (a -> a -> Bool) -> (a -> a -> MaybeT m b) -> FoldE a m (Maybe b)
spanIfE2 p p2 f = foldIf1 p (span2E p2 f)

parseStringWith :: (Comonad w, Monad m) => (w Char -> w Char -> MaybeT m b) -> FoldE (w Char) m (Maybe b)
parseStringWith = spanIfE2 ((== '"') . extract) (\x y -> (extract x == '\\') || (extract y /= '"'))


-- | If empty, @`extractM`@, if the predicate passes
-- then fold with the given fold else `throwE`.
foldIf :: Monad m => (a -> Bool) -> FoldE a m b -> FoldE a m b
foldIf p (FoldE f) = FoldE $ (`impurely` f) $ \stp ini ext ->
  FoldM
    (\x y -> case x of
               Nothing -> if p y
                             then Just <$> ini
                             else ini >>= ext >>= throwE -- early throw
               ~(Just x') -> Just <$> stp x' y
    )
    (return Nothing)
    (\x -> maybe (ini >>= ext) ext x)


takeWhile1 :: Monad m => (a -> Bool) -> FoldE a m b -> FoldE a m b
takeWhile1 p (FoldE f) = FoldE . joinFoldM $ (`impurely` f) $ \stp ini ext ->
  FoldM
    (\x y -> if p y
                then stp x y
                else ext x >>= throwE
    )
    ini
    (return . ext)

takeUntil1 :: Monad m => (a -> Bool) -> FoldE a m b -> FoldE a m b
takeUntil1 p (FoldE f) = FoldE . joinFoldM $ (`impurely` f) $ \stp ini ext ->
  FoldM
    (\x y -> if p y
                then ext x >>= throwE
                else stp x y
    )
    ini
    (return . ext)


