{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}

module Lib where

import Control.Applicative
import Control.Comonad
import Control.Comonad.Cofree
import Control.Foldl (Fold(..), FoldM(..), fold, foldM, purely, impurely, simplify, generalize, premap)
import Control.Monad hiding (fail)
import Control.Monad.Fail
import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer.Lazy
import Data.ByteString (ByteString)
import Data.Function
import Data.IntMap (IntMap)
import Data.Monoid
import Data.Proxy
import Data.Text (Text)
import Data.Trie (Trie)
import Data.Vector.Sized hiding (foldl, foldl', empty, fromList)
import GHC.TypeLits
import Prelude hiding (fail)
import qualified Data.ByteString as B
import qualified Data.IntMap as I
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Trie as Tr
import Data.Char
import Data.Foldable hiding (fold)
import System.Environment
import Data.Functor.Identity
import Control.Monad.Trans.Free
import Data.List.NonEmpty hiding (fromList)
import Control.Comonad.Trans.Cofree (CofreeT)
import qualified Control.Comonad.Trans.Cofree as CT
import Control.Monad.Trans.Except
import Data.Profunctor





-- Read bytes into buffer
-- Take up to newline or maxLineLen
--   if newline
--     if ended

-- lines :: Fold Char a -> Fold a b -> Fold Char b
-- ->
-- spaced :: Fold Char a -> Fold (Spaces, Char) (Spaces, a) -- give the number of preceding spaces each step, and the number of trailing spaces at the end
-- ->
-- indented :: Fold Char a -> Fold (Spaces, Char) (Spaces, Indented a) -- the number of preceding spaces of the line
-- ->
-- withComment :: Fold Char a -> Fold (Spaces, Char) (Spaces, WithComment a) -- a comment may occur at either the beginning or the end of the line
-- ->

-- | Assumes the initial is True
foldEitherP :: (a -> Bool) -> Fold a b -> Fold a c -> Fold (Either b c) d -> Fold a d
foldEitherP p f g h = (`purely` f) $ \stpx inix extx ->
                      (`purely` g) $ \stpy iniy exty ->
                      (`purely` h) $ \stpz iniz extz ->
  Fold
    (\x y -> case x of
               Left (z, w) -> if p y
                                 then Left (stpx z y, w)
                                 else Right (stpy iniy y, stpz w (Left  (extx z)))
               Right (z, w) -> if p y
                                  then Left (stpx inix y, stpz w (Right (exty z)))
                                  else Right (stpy z y, w)
    )
    (Left (inix, iniz))
    (extz . either (\(x, y) -> stpz y (Left (extx x))) (\(x, y) -> stpz y (Right (exty x))))


-- (a -> Bool) -> (a -> Bool) -> (a -> a -> Bool) -> Fold a b -> Fold a c ->


-- blocks :: headLine :< next indent up [headLine :< ..]
-- ->






-- data Fold a b Source#

-- Efficient representation of a left fold that preserves the fold's step function, initial accumulator, and extraction function

-- This allows the Applicative instance to assemble derived folds that traverse the container only once

-- A 'Fold a b' processes elements of type a and results in a value of type b.

-- Constructors

-- Fold (x -> a -> x) x (x -> b)
-- Fold step initial extract

-- Fold a b -> Fold (a, a) (Maybe b)

-- | Source location
data Loc = Loc { lineNum  :: !Int
               , beginLoc :: !Int
               , endLoc   :: !Int
               } deriving (Eq, Ord, Show, Read)

newtype Token = Token { unToken :: Int } deriving (Bounded)

-- | Make or lookup a `Token`
class MonadFail m => MonadToken m where
  token    :: Loc -> Text -> m Token
  getToken :: Token -> m (Loc, Text)

data TokenState = TokenState { currentToken :: !Token
                             , lookupTrie   :: !(Trie Token)
                             , tokenMap     :: !(IntMap (Loc, ByteString))
                             }

newtype TokenT m a = TokenT { getTokenT :: StateT TokenState m a } deriving (Functor)

instance Monad m => Applicative (TokenT m) where
  pure = TokenT . pure

  TokenT f <*> TokenT x = TokenT (f <*> x)

instance Monad m => Monad (TokenT m) where
  TokenT x >>= f = TokenT (x >>= getTokenT . f)

instance MonadTrans TokenT where
  lift = TokenT . lift

instance MonadFail m => MonadFail (TokenT m) where
  fail = lift . fail

instance MonadFail m => MonadToken (TokenT m) where
  token loc txt = TokenT . StateT $ \(~(TokenState (Token tok) trie mp)) -> do
    if tok == maxBound
       then fail $ "maxBound hit: " <> show (maxBound `asTypeOf` tok)
       else do
         let tok'  = succ tok
         let bs    = TE.encodeUtf8 txt
         let trie' = Tr.insert bs (Token tok) trie
         let mp'   = I.insert tok (loc, bs) mp
         return (Token tok, TokenState (Token tok') trie' mp')

  getToken (Token tok) = TokenT . StateT $ \(ts@(~(TokenState _ _ mp))) -> do
    let err = fail $ "Token not found: " <> show tok
    maybe err (return . (, ts) . fmap TE.decodeUtf8) $ I.lookup tok mp

runTokenT :: Monad m => TokenT m a -> m (a, TokenState)
runTokenT = flip runStateT (TokenState minBound Tr.empty I.empty) . getTokenT


parseText :: Monad m => Text -> Cofree (ReaderT Char m) a -> Either a (m a)
parseText txt (x :< ReaderT xs) = case T.uncons txt of
                            Nothing -> Left x
                            ~(Just (y, ys)) -> Right $ xs y >>= either return id . parseText ys

-- | Strict homogenous pairs
data Pair a = Pair { fstPair :: !a
                   , sndPair :: !a
                   } deriving (Eq, Ord, Show, Functor)


enumCofree :: (Enum i, Functor m) => Cofree m a -> WriterT i (Cofree m) a
enumCofree ~(x :< xs) = WriterT ((x, i0) :< (fmap (runWriterT . enumCofree) xs))
  where
    i0 = toEnum 0

mark :: Functor m => WriterT i (Cofree m) a -> WriterT (Pair i) (Cofree m) a
mark (WriterT ((x, i) :< xs)) = WriterT ((x, Pair i i) :< fmap (fmap (fmap (Pair i))) xs)


-- | Extract the current marked range
getMark :: WriterT (Pair i) (Cofree m) a -> Pair i
getMark ~(WriterT ((_, p) :< _)) = p


unMarkToken :: (Enum i, MonadToken m) => i -> Text -> WriterT (Pair i) (Cofree m) a -> m (Token, WriterT i (Cofree m) a)
unMarkToken i txt ~(WriterT ((x, p) :< xs)) = do
  tok <- selectToken i txt p
  xs' <- fmap (fmap sndPair) <$> xs
  return (tok, WriterT xs')


selectToken :: (Enum i, MonadToken m) => i -> Text -> Pair i -> m Token
selectToken i txt p@(Pair x y) = selectText txt p >>= token (Loc (fromEnum i) (fromEnum x) (fromEnum y))

selectText :: (Enum i, MonadFail m) => Text -> Pair i -> m Text
selectText txt (Pair x y)
  | x' < 0    = fail "x < 0"
  | x' == 0    = return $ T.take (y' + 1) txt
  | otherwise = return (T.take (y' + 1) (T.drop x' txt))
    where
      x' = fromEnum x
      y' = fromEnum y

-- | Use a Cofree Reader to take all for a token
takeToken :: (Enum i, MonadToken m) => i -> Text -> ReaderT a m (Cofree (ReaderT a m) Bool) -> WriterT (Pair i) (Cofree m) a -> m (Token, WriterT i (Cofree m) a)
takeToken i txt rd wt = dropCofreeReader rd wt >>= unMarkToken i txt

-- | Drop using a Cofree Reader to encode a (possibly stateful) predicate
dropCofreeReader :: Monad m => ReaderT a m (Cofree (ReaderT a m) Bool) -> WriterT (Pair i) (Cofree m) a -> m (WriterT (Pair i) (Cofree m) a)
dropCofreeReader (ReaderT rd) w@(~(WriterT ((x, p) :< xs))) = do
  (y :< ys) <- rd x
  if y
     then xs >>= dropCofreeReader ys . WriterT
     else return w


unitReader :: Applicative m => (a -> Bool) -> ReaderT a m (Cofree (ReaderT a m) Bool)
unitReader p = ReaderT ((\b -> pure (b :< unitReader p)) . p)

unitReaderM :: Applicative m => (a -> m Bool) -> ReaderT a m (Cofree (ReaderT a m) Bool)
unitReaderM p = ReaderT (fmap (:< unitReaderM p) . p)


-- | Example usage of `unitReader` to read digits
digitReader :: Applicative m => ReaderT Char m (Cofree (ReaderT Char m) Bool)
digitReader = unitReader isDigit



fromList :: Alternative f => [a] -> f (Cofree f a)
fromList [] = empty
fromList ~(x:xs) = pure (x :< fromList xs)



-- data Loc = Loc { lineNum  :: !Int
--                , beginLoc :: !Int
--                , endLoc   :: !Int
--                } deriving (Eq, Ord, Show, Read)




foldlChar :: Fold Char b -> Fold Text b
foldlChar = purely (Fold . T.foldl)

foldlChar' :: Fold Char b -> Fold Text b
foldlChar' = purely (Fold . T.foldl')




-- | Fold into groups, then fold those groups.
--
-- Roughly equivalent to:
--
-- @
--  fold fy . map (fold fx) . groupBy p == groupByF
-- @
--
groupByF :: (a -> a -> Bool) -> Fold a b -> Fold b c -> Fold a c
groupByF p fx fy =
  (`purely` fx) $ \stpx inix extx ->
  (`purely` fy) $ \stpy iniy exty ->
  Fold
    (\(~(stx, sty, x)) y -> case x of
      Nothing -> (stpx stx y, sty, Just (p y))
      ~(Just p') -> if p' y
                       then (stpx stx  y,      sty           , Just  p'  )
                       else (stpx inix y, stpy sty (extx stx), Just (p y))
    )
    (inix, iniy, Nothing)
    (\(~(_, sty, _)) -> exty sty)

groupByF' :: (a -> a -> Bool) -> Fold a b -> Fold b c -> Fold a c
groupByF' p fx fy =
  (`purely` fx) $ \stpx inix extx ->
  (`purely` fy) $ \stpy iniy exty ->
  Fold
    (\x y -> Just $ case x of
                      Nothing -> (stpx inix y, iniy, p y)
                      ~(Just (stx, sty, p')) -> if p' y
                        then (stpx stx  y,      sty           , p' )
                        else (stpx inix y, stpy sty (extx stx), p y)
    )
    Nothing
    (maybe (exty iniy) (\(~(_, sty, _)) -> exty sty))

groupByF'' :: (a -> a -> Bool) -> Fold a b -> Fold b c -> Fold a c
groupByF'' p fx fy =
  (`purely` fx) $ \stpx inix extx ->
  (`purely` fy) $ \stpy iniy exty ->
  Fold
    (\(~(stx, sty, p')) y -> if p' y
                       then (stpx stx  y,      sty           , p' )
                       else (stpx inix y, stpy sty (extx stx), p y)
    )
    (inix, iniy, const False)
    (exty . snd3)


-- | `Fold` with the first `Fold` until the predicate returns `False`, then with the second `Fold`.
--
-- For example:
--
-- @
--  λ> fold (spanF (< 3) sumF (\x -> liftA2 (,) (pure x) ((+ x) <$> sumF))) $ [1..10]
--  (3,55)
-- @
spanF :: (a -> Bool) -> Fold a b -> (b -> Fold a c) -> Fold a c
spanF p fx fy =
  (`purely` fx) $ \stpx inix extx ->
  Fold
    (\x y -> case x of
      Left x' -> if p y
        then Left  (stpx x' y)
        else Right (y, fy (extx x'))
      ~(Right (y', fz)) -> Right ( y
                                 , (`purely` fz) $ \stpy iniy extx ->
                                   Fold stpy (stpy iniy y') extx
                                 )
    )
    (Left inix)
    (either
      (extract . fy . extx)
      (\(~(y, fz)) -> (`purely` fz) $ \stpy iniy exty -> exty (stpy iniy y)
      )
    )


sumF :: Num a => Fold a a
sumF = Fold (+) 0 id



-- span2F :: (a -> Bool) -> (a -> a -> Bool) -> Fold a b -> (b -> Fold a c) -> Fold a c
-- span2F p1 p2 fx fy =
--   (`purely` fx) $ \stpx inix extx ->
--   Fold


-- What would a parenthases Fold look like?
--   (a -> Bool) -- open parens
--   (a -> Bool) -- close parens
--   Unfolds into a Forest, which is then folded how?
--     Forest = [a :< [a :< ..]]
--     = [Cofree [] a]

--     Fold (Cofree [] a) b
--     ReaderT a (Cofree (ReaderT a (Fold a))) b -- (a -> Fold a (b, a -> Fold a ..))


-- (a -> Bool) -> (a -> Bool) -> ReaderT a (Cofree (Fold1 a)) b -> Fold b c -> Fold a c
-- matchBegin matchEnd (

-- a :< f (Cofree f a)

-- a -> [Cofree [] a] -> b

-- Hmm, need some other way to represent tree fold
--   A Tree Fold is a function taking a node and returning a Forest Fold
--   A Forest Fold is a Tree Fold and a output fold

-- FoldTree a b c = (a -> FoldForest a b c)
-- FoldForest a b c = (FoldTree a b, Fold b c)

-- FoldTree a b c = a -> FoldForest a b c
-- FoldForest a b c = (Fold b c, a -> FoldForest a b c)

-- FoldForest a b c = Cofree (ReaderT a (FoldForest a b) c) (Fold b c)

-- Tree = [Either a (Tree a)]
-- Tree = FreeT Identity []

-- Fold (Tree a) b -> Fold (Either a (Tree a)) b -> Fold (Either a b) b

-- Fold (Tree a) b = Fold (Either a (Tree a)) b





-- Pos (Ptr a) (Ptr a)

-- Ptr (Pos (Ptr a) (Ptr a))

-- ReaderT (Ptr (Ptr a))

-- ended stack -- just the end positions
-- began stack -- ptr to end position of began
-- parens stack -- (ptr (begin position), ptr (end position | nullPtr))



-- | Fold as a Tree where pure values are Left and subtrees are folded into Right (ignoring unmatched right (endP) values)
-- treeF :: (a -> Bool) -> (a -> Bool) -> Fold (Either a b) b -> Fold a b
-- treeF beginP endP f = simplify $ extract <$> treeFM' beginP endP (const (return ())) (generalize f)

-- -- | Warning: function is lossy and will not return for: @liftM2 (||) beginP endP@ (except when emitting)
-- --
-- -- If not parsing in chunks (so there are no previous given or non-given parenthases to match), @emit@ should be an "unmatched parens" error.
-- -- Otherwise,
-- treeFM :: Monad m => (a -> Bool) -> (a -> Bool) -> (a -> m ()) -> FoldM m (Either a b) b -> FoldM m a (Either (b, FoldM m a b) b)
-- treeFM beginP endP emit f = (`impurely` f) $ \stp ini ext ->
--   let folder = \(xss@(~(x :| xs))) y -> if beginP y
--                                  then do
--                                    ini' <- ini
--                                    return (ini' :| (x:xs))
--                                  else if endP y
--                                  then case xs of
--                                         [] -> do
--                                           emit y
--                                           return xss
--                                         ~(z:zs) -> do
--                                           x' <- ext x
--                                           z' <- stp z (Right x')
--                                           return (z' :| zs)
--                                  else (:| xs) <$> stp x (Left y)
--   in
--   let extracter = \(~(z :| zs)) -> do
--       z' <- ext z
--       case zs of
--         [] -> return (Right z')
--         (~(w:ws)) -> Left <$> do
--           return (z', either fst id <$> FoldM folder (return $ w :| ws) extracter)
--   in
--   FoldM folder ((:| []) <$> ini) extracter

-- -- | `treeFM`, but allow for arbitrary-depth returning of a continuation fold.
-- --
-- -- For example, when parsing parenthases, "()(" would return a continuation fold with the "(" on the stack (the NonEmpty).
-- treeFM' :: Monad m => (a -> Bool) -> (a -> Bool) -> (a -> m ()) -> FoldM m (Either a b) b -> FoldM m a (Cofree (MaybeT (FoldM m a)) b)
-- treeFM' beginP endP emit f = (`impurely` f) $ \stp ini ext ->
--   let folder = \(xss@(~(x :| xs))) y -> if beginP y
--                                  then do
--                                    ini' <- ini
--                                    return (ini' :| (x:xs))
--                                  else if endP y
--                                  then case xs of
--                                         [] -> do
--                                           emit y
--                                           return xss
--                                         ~(z:zs) -> do
--                                           x' <- ext x
--                                           z' <- stp z (Right x')
--                                           return (z' :| zs)
--                                  else (:| xs) <$> stp x (Left y)
--   in
--   let extracter = \(~(z :| zs)) -> do
--       z' <- ext z
--       case zs of
--         [] -> do
--           return (z' :< MaybeT (pure Nothing))
--         (~(w:ws)) -> do
--           return (z' :< MaybeT (Just <$> (FoldM folder (return $ w :| ws) extracter)))
--   in
--   FoldM folder ((:| []) <$> ini) extracter


nothingT :: Applicative m => MaybeT m a
{-# INLINE nothingT #-}
nothingT = MaybeT (pure Nothing)



-- newtype TreeReader a m b = TreeReader { runTreeReader :: FoldM (FreeReaderT (TreeReader a m b) m) a (Cofree (MaybeT (TreeReader a m)) b) }

-- instance Functor m => Functor (TreeReader a m) where
--   fmap f (TreeReader x) = TreeReader $ (`impurely` x) $ \stp ini ext -> FoldM (_ stp) (_ ini) (_ . ext)


-- -- treeFM'' :: Monad m => (a -> Bool) -> (a -> Bool) -> FoldM m (Either a b) b -> FoldM (FreeReaderT (FoldM m (Either a b) b)) a (Cofree (MaybeT (FoldM m a)) b)
-- treeFM'' beginP endP f =
--   let folder = \(xss@(~(x :| xs))) y -> if beginP y
--                                  then do
--                                    return (f :| (x:xs))
--                                  else if endP y
--                                  then case xs of
--                                         [] -> withRead $ \z -> do
--                                           x' <- extractM x
--                                           let z' = feedFM (Right x') z
--                                           return (z' :| [])
--                                         ~(z:zs) -> do
--                                           x' <- extractM x
--                                           let z' = feedFM (Right x') z
--                                           return (z' :| zs)
--                                   else feedFM (Left y) x :| xs
--   in
--   let extracter = \(~(z :| zs)) -> do
--       z' <- extractM z
--       case zs of
--         [] -> do
--           return (z', Nothing) -- MaybeT (pure Nothing))
--         (~(w:ws)) -> do
--           return (z', FoldM folder (return $ w :| ws) extracter)
--   in
--   FoldM folder (return (f :| [])) return

-- (x :< xs) ->

pushTop :: Monad m => a -> NonEmpty a -> m (NonEmpty a)
pushTop f (x :| xs) = return (f :| (x:xs))

feedTop :: Monad m => a -> NonEmpty (FoldM m (Either a b) c) -> m (NonEmpty (FoldM m (Either a b) c))
feedTop y (x :| xs) = return (feedFM (Left y) x :| xs)

popTop :: MonadReader (FoldM m (Either a b) b) m =>
           NonEmpty (FoldM m (Either a b) b)
     -> m (NonEmpty (FoldM m (Either a b) b))
popTop (x :| xs) = case xs of
                     [] -> withRead $ \y -> do
                       x' <- extractM x
                       let y' = feedFM (Right x') y
                       return (y' :| [])
                     ~(y:ys) -> do
                       x' <- extractM x
                       let y' = feedFM (Right x') y
                       return (y' :| ys)

pushFeedPop :: MonadReader (FoldM m (Either a b) b) m =>
               (a -> Bool) -> (a -> Bool) -> FoldM m (Either a b) b -> a -> NonEmpty (FoldM m (Either a b) b) -> m (NonEmpty (FoldM m (Either a b) b))
pushFeedPop beginP endP f x y | beginP x  = pushTop f y
                              | endP x    = popTop y
                              | otherwise = feedTop x y

pushFeedPopFold :: MonadReader (FoldM m (Either a b) b) m => (a -> Bool) -> (a -> Bool)
     -> FoldM m (Either a b) b
     -> FoldM m a (NonEmpty (FoldM m (Either a b) b))
pushFeedPopFold p q f = (`impurely` f) $ \stp ini ext ->
  FoldM (flip (pushFeedPop p q f)) (return (return f)) return


-- -- | Continue a collection of folds
-- extendFold :: NonEmpty (FoldM (Either a b) b) -> FoldM m a (NonEmpty (FoldM m (Either a b) b))


collect :: Enum i => (a -> Bool) -> Fold (Either a i) b -> Fold a b
collect p f = (`purely` f) $ \stp ini ext ->
  Fold
    (\x y -> if p y
                then case x of
                       Right x' -> Left (x', toEnum 1)
                       ~(Left (x', i)) -> Left (x', succ i)
                else case x of
                       Right x' -> Right (stp x' (Left y))
                       Left (x', i) -> Right (stp x' (Right i))
    )
    (Right ini)
    (ext . either (\(~(x, i)) -> stp x (Right i)) id)

collectM_ :: (Enum i, Monad m) => (a -> Bool) -> FoldM m (Either a i) b -> FoldM m a b
collectM_ p f = (`impurely` f) $ \stp ini ext ->
  FoldM
    (\x y -> if p y
                then return . Left $ case x of
                       Right x' -> (x', toEnum 1)
                       ~(Left (x', i)) -> (x', succ i)
                else Right <$> case x of
                       Right x' -> stp x' (Left y)
                       Left (x', i) -> stp x' (Right i)
    )
    (Right <$> ini)
    ((>>= ext) . either (\(~(x, i)) -> stp x (Right i)) return)

collectM :: (Enum i, Monad m) => (a -> m Bool) -> FoldM m (Either a i) b -> FoldM m a b
collectM p f = (`impurely` f) $ \stp ini ext ->
  FoldM
    (\x y -> do
      y' <- p y
      if y'
         then return . Left $ case x of
                Right x' -> (x', toEnum 1)
                ~(Left (x', i)) -> (x', succ i)
         else Right <$> case x of
                Right x' -> stp x' (Left y)
                Left (x', i) -> stp x' (Right i)
    )
    (Right <$> ini)
    ((>>= ext) . either (\(~(x, i)) -> stp x (Right i)) return)


newtype Spaces = Spaces { numSpaces :: Int } deriving (Eq, Ord, Read, Show)

instance Enum Spaces where
  toEnum = Spaces
  fromEnum = numSpaces

type MaybeSpaces a = Either Spaces a

swapEither :: Either a b -> Either b a
swapEither = either Right Left

collectSpaces :: Fold (MaybeSpaces Char) b -> Fold Char b
collectSpaces = collect isSpace . lmap swapEither

collectSpacesM :: Monad m => FoldM m (MaybeSpaces Char) b -> FoldM m Char b
collectSpacesM = collectM_ isSpace . lmap swapEither

foldSpaces :: Fold Char b -> Fold (MaybeSpaces b) c -> Fold (MaybeSpaces Char) c
foldSpaces f g = (`purely` f) $ \stpx inix extx ->
                 (`purely` g) $ \stpy iniy exty ->
  Fold
    (\(x, y) z -> case z of
                    l@(Left s) -> (inix, stpy (stpy y (Right (extx x))) (Left s))
                    Right c -> (stpx x c, y)
                    )
    (inix, iniy)
    (\(x, y) -> exty y)

foldSpacesM :: Monad m => FoldM m Char b -> FoldM m (MaybeSpaces b) c -> FoldM m (MaybeSpaces Char) c
foldSpacesM f g = (`impurely` f) $ \stpx inix extx ->
                  (`impurely` g) $ \stpy iniy exty ->
  FoldM
    (\(x, y) z -> case z of
                    l@(Left s) -> do
                      inix' <- inix
                      x'  <- extx x
                      y'  <- stpy y  (Right x')
                      y'' <- stpy y' (Left s)
                      return (inix', y'')
                    Right c -> do
                      x' <- stpx x c
                      return (x', y)
                    )
    (liftM2 (,) inix iniy)
    (\(x, y) -> exty y)


collectFoldSpaces :: Fold Char a -> Fold (MaybeSpaces a) b -> Fold Char b
collectFoldSpaces = fmap collectSpaces . foldSpaces

collectFoldSpacesM :: Monad m => FoldM m Char a -> FoldM m (MaybeSpaces a) b -> FoldM m Char b
collectFoldSpacesM = fmap collectSpacesM . foldSpacesM

exampleCountChars :: Fold Char Int
exampleCountChars = collectFoldSpaces countF (premap (either numSpaces id) sumF)

stringF :: Fold Char String
stringF = Fold (\x y -> x <> [y]) [] id


newtype FreeReaderT a m b = FreeReaderT { runFreeReaderT :: FreeT (Reader a) m b } deriving (Functor)

instance Monad m => Applicative (FreeReaderT a m) where
  pure = FreeReaderT . pure

  FreeReaderT f <*> FreeReaderT x = FreeReaderT (f <*> x)

instance Monad m => Monad (FreeReaderT a m) where
  FreeReaderT x >>= f = FreeReaderT (x >>= runFreeReaderT . f)

instance MonadTrans (FreeReaderT a) where
  lift = FreeReaderT . lift

class Monad m => MonadReader a m | m -> a where
  withRead :: (a -> m b) -> m b

instance Monad m => MonadReader a (FreeReaderT a m) where
  withRead f = FreeReaderT . wrap . ReaderT $ return . runFreeReaderT . f

cofreeRead :: MonadReader a m => m (Cofree m a)
cofreeRead = withRead (return . (:< cofreeRead))

hoistFreeReaderT :: Monad m => (forall x. m x -> n x) -> FreeReaderT a m b -> FreeReaderT a n b
hoistFreeReaderT f (FreeReaderT x) = FreeReaderT (hoistFreeT f x)



-- FreeT (ReaderT (FoldM m (Either a b) b) m) m c -> m (FreeT (ReaderT (FoldM m (Either a b) b) m) m c)

feedF :: a -> Fold a b -> Fold a b
feedF x f = (`purely` f) $ \stp ini ext -> Fold stp (stp ini x) ext


feedFM :: Monad m => a -> FoldM m a b -> FoldM m a b
feedFM x f = (`impurely` f) $ \stp ini ext -> FoldM stp (ini >>= flip stp x) ext


joinFoldM :: Monad m => FoldM m a (m b) -> FoldM m a b
joinFoldM f = (`impurely` f) $ \stp ini ext -> FoldM stp ini (join . ext)

returnFoldM :: Monad m => FoldM m (m a) b -> FoldM m a b
returnFoldM f = (`impurely` f) $ \stp ini ext -> FoldM (\x y -> stp x (return y)) ini ext

bindFoldM :: Monad m => FoldM m a b -> FoldM m (m a) b
bindFoldM f = (`impurely` f) $ \stp ini ext -> FoldM (\x y -> y >>= stp x) ini ext

mapMFoldM :: Monad m => (b -> m c) -> FoldM m a b -> FoldM m a c
mapMFoldM f = joinFoldM . fmap f

dimapFoldM :: Monad m => (b -> m a) -> (c -> m d) -> FoldM m a c -> FoldM m b d
dimapFoldM f g = joinFoldM . dimap f g . bindFoldM


extractM :: Monad m => FoldM m a b -> m b
extractM = flip Control.Foldl.foldM Nothing

swapMaybe :: a -> Maybe b -> Maybe a
swapMaybe x = maybe (Just x) (const Nothing)

endTreeFM :: Monad m => FoldM m a (Cofree (MaybeT (FoldM m a)) b) -> FoldM m a (Maybe b)
endTreeFM = joinFoldM . fmap (\(~(x :< MaybeT xs)) -> extractM xs >>= return . swapMaybe x)


-- | run the resulting fold over a groupBy-like function and collect the results, including the continuation fold
-- runTreeFMSection :: FoldM m a (Cofree (MaybeT (FoldM m a)) b) -> FoldM m b c -> ((FoldM m a b -> FoldM m b c -> r) -> r) -> FoldM m a (Cofree (MaybeT (FoldM m a)) c)




-- ok, this emitting version is ok, but what we really want to do is construct a data-type that encodes: left-missing pieces, matched pieces, right-missing pieces

-- "(" -> rightMissing :: a -> FoldM m a b
-- ")" -> leftMissing :: (a -> FoldM m a b -> r) -> r
-- "(x)" -> matched :: (a -> a -> FoldM m a b -> r) -> r

-- FoldM m (Either a b) b -> FoldM m a (Cofree (MaybeT (FoldM m a)) b)

-- treeFMFree :: Monad m => (a -> Bool) -> (a -> Bool) -> FoldM m (Either a b) b -> FoldM (FreeT (ReaderT a m) m) a (Cofree (MaybeT (FoldM m a)) b)
-- -- treeFM' :: Monad m => (a -> Bool) -> (a -> Bool) -> FoldM m (Either a b) b -> FoldM m a (Cofree (MaybeT (FoldM m a)) b)
-- treeFMFree beginP endP f = (`impurely` f) $ \stp ini ext ->
--   let folder = \(xss@(~(x :| xs))) y -> if beginP y
--                                  then lift $ do
--                                    ini' <- ini
--                                    return (ini' :| (x:xs))
--                                  else if endP y
--                                  then case xs of
--                                         [] -> do
--                                           FreeT . Free . ReaderT $ \z -> if beginP y then _ else _ -- folder (x :| [_ z]) y
--                                         ~(z:zs) -> lift $ do
--                                           x' <- ext x
--                                           z' <- stp z (Right x')
--                                           return (z' :| zs)
--                                  else (:| xs) <$> lift (stp x (Left y))
--   in
--   let extracter = \(~(z :| zs)) -> do
--       z' <- lift (ext z)
--       case zs of
--         [] -> do
--           return (z' :< MaybeT (return Nothing))
--         (~(w:ws)) -> do
--           let initlW = return ((w `asTypeOf` z) :| (ws `asTypeOf` zs))
--           return (z' :< MaybeT (_ $ FoldM folder initlW extracter))
--   in
--   let initl = lift $ do
--       ini' <- ini
--       return (ini' :| [])
--   in
--   FoldM folder initl extracter


-- treeFReader :: Monad m => (a -> Bool) -> (a -> Bool) -> FoldM m (Either a b) b -> FoldM (FreeT (ReaderT a m) m) a (Cofree (MaybeT (FoldM m a)) b)
-- treeFReader beginP endP f = (`impurely` f) $ \stp ini ext ->
--   let folder = \(xss@(~(x :| xs))) y -> if beginP y
--                                  then do
--                                    ini' <- lift ini
--                                    return (ini' :| (x:xs))
--                                  else if endP y
--                                  then case xs of
--                                         [] -> do
--                                           FreeT . return . Free . ReaderT $ \z -> do
--                                             x' <- lift $ stp x (Right z)
--                                             return . return $ (x' :| [])
--                                         ~(z:zs) -> do
--                                           x' <- lift (ext x)
--                                           z' <- lift (stp z (Right x'))
--                                           return (z' :| zs)
--                                  else do
--                                    x' <- lift (stp x (Left y))
--                                    return (x' :| xs)
--   in
--   let extracter = \(zss@(~(z :| zs))) -> do
--       z' <- lift (ext z)
--       case zs of
--         [] -> do
--           return (Right z')
--         (~(w:ws)) -> do
--           let folder' = FoldM folder (return (w :| ws)) extracter
--           return (Left (z', folder'))
--   in
--   let initl = do
--       ini' <- lift ini
--       return (ini' :| [])
--   in
--   FoldM folder initl extracter

-- genericTreeF :: (forall a. m a -> n a) -> (a -> Bool) -> -> FoldM m (Either a b) b -> FoldM n (Either a b) b
-- genericTreeF lft f = (`impurely` f) $ \stp ini ext ->
--   FoldM (_ stp ini ext) ((:| []) <$> lft ini) (\(zss@(~(z :| zs))) -> _ stp ini ext)



-- (x, xs) = span (not . liftM2 (||) (== '(') (== ')'))
-- ('(':ys) -> begin parens group
-- (')':ys) -> if no parens group to end, then Pure (context which requires the results so far (b) and a close parens to make a b?)
--   (z, zs) -> span (not . liftM2 (||) (== '(') (== ')')) ys
--     []       -> hanging parens
--     ('(':ws) -> begin nested parens group
--     (')':ws) -> end parens group, continue

-- begin parens group
--   push init onto stack
-- end parens group
--   extract the top of the stack :: m b
--   provide (Right b) to the step function
-- continue
--   provide (Left a) to the step function

-- FoldM m (Either a b) b -> FoldM m a ..

-- (forall a. FoldM m (Either a b) b -> FoldM m

-- type PushPopM x t m r = (x -> t x -> m (t x)) -> (t x -> m (x, Maybe (t x))) -> r

-- newtype PushPopMT t m r = PushPopMT { runPushPopMT :: (forall x. PushPopM x t m r) -> r }


-- (\(x :< xs) y -> (f x :< xs) (ini :< _ x xs) (xs >>= \(z :< zs) -> g z zs))

--   | _ = modify (push ini)
--   | _ = modify (


-- stackNonEmpty' :: Monad m => (forall x. PushPopM x NonEmpty m r) -> r
-- stackNonEmpty' = stackNonEmpty

stackNonEmpty :: Monad m => (forall x. (x -> NonEmpty x -> m (NonEmpty x)) -> (NonEmpty x -> m (x, Maybe (NonEmpty x))) -> r) -> r
stackNonEmpty f = f pushNonEmpty popNonEmpty

pushNonEmpty :: Monad m => x -> NonEmpty x -> m (NonEmpty x)
pushNonEmpty x ~(y :| ys) = return (x :| (y : ys))

popNonEmpty :: Monad m => NonEmpty x -> m (x, Maybe (NonEmpty x))
popNonEmpty ~(x :| xs) = return (x, case xs of
                       [] -> Nothing
                       ~(y:ys) -> Just (y :| ys)
                           )



    -- _ :: (x -> a -> m x) -> m x -> (x -> m b) -> x0 -> a1 -> m1 x0
    -- _ :: m x -> m1 x0
    -- _ :: (x -> a -> m x) -> m x -> (x -> m b) -> x0 -> m1 b1


-- (a -> Bool) -> Fold (Maybe a) b -> Fold a b



-- ..(..(..(..
-- ..)..)..)..


-- NonEmpty x -- the y in (y :| ys) is the state of the base-level of the fold, the ys are the states of open parenthases
-- Now, what if we end with additional parenthases' states?
--   We must put them in a FoldM, since they include x, a hidden var.
--     FoldM folder (return (y :| ys)) extracter


-- Open:
--   Push onto stack
--   extract: Fold with continuation
-- Close:
--   Pop from stack
--   If no stack, return function which requires stack
--   extract:
--     simple extract if popped from stack (no match)
--     else function which requires stack -> matched


-- | A small demonstration of the power of `treeF`
-- toTreeF :: (a -> Bool) -> (a -> Bool) -> Fold a (FreeT Identity [] a)
-- toTreeF px py = treeF px py $ Fold
--   (\x y -> case y of
--              Left y'  -> x <> [Pure           y' ]
--              Right y' -> x <> [Free (Identity y')]
--   )
--   []
--   FreeT

printFreeT :: FreeT Identity [] String -> IO ()
printFreeT (FreeT xs) = Data.Foldable.mapM_ printFreeF xs

printFreeF :: FreeF Identity String (FreeT Identity [] String) -> IO ()
printFreeF (Pure str) = putStrLn str
printFreeF (Free (Identity xs)) = printFreeT (fmap ("  "<>) xs)


enumF :: Enum i => Fold (i, a) b -> Fold a b
enumF f = (`purely` f) $ \stp ini ext ->
  Fold
    (\(i, x) y -> (succ i, stp x (i, y)))
    (toEnum 0, ini)
    (ext . snd)

enumF' :: Enum i => Fold (i, a) b -> Fold a b
enumF' = preFold countF

countF :: Enum i => Fold a i
countF = Fold (const . succ) (toEnum 0) id

-- | pre-fold, pass the results of the first Fold as a an argument to the second fold (like a scan):
--
-- @
--  preFold fx fy == fold . scanl (fmap fx . join (,))
-- @
--
preFold :: Fold a b -> Fold (b, a) c -> Fold a c
preFold fx fy =
  (`purely` fx) $ \stpx inix extx ->
  (`purely` fy) $ \stpy iniy exty ->
  Fold
    (\(~(stx, sty)) y ->
      let stx' = stpx stx y
      in
      (stx', stpy sty (extx stx', y))
    )
    (inix, iniy)
    (exty . snd)


newtype Fold1 a b = Fold1 { runFold1 :: ReaderT a (Fold a) b }


-- Modify the above to match
-- Benchmark the differences (above might be faster since stx, sty, can be lazily accessed

-- | Fold into groups using a monadic action, see `groupByF`
groupByFM :: Monad m => (a -> a -> m Bool) -> FoldM m a b -> FoldM m b c -> FoldM m a c
groupByFM p fx fy =
  (`impurely` fx) $ \stpx inix extx ->
  (`impurely` fy) $ \stpy iniy exty ->
  FoldM
    (\x y -> Just <$> case x of
               Nothing -> do
                 stx' <- inix >>= flip stpx y
                 sty' <- iniy
                 return (stx', sty', p y)
               ~(Just (stx, sty, p')) -> do
                 py <- p' y
                 if py
                    then do
                      stx' <- stpx stx y
                      return (stx', sty , p')
                    else do
                      stx' <- inix >>= flip stpx y
                      sty' <- extx stx >>= stpy sty
                      return (stx', sty', p y)
    )
    (return Nothing)
    (maybe (iniy >>= exty) (exty . snd3))

groupByFM' :: Monad m => (a -> a -> m Bool) -> FoldM m a b -> FoldM m b c -> FoldM m a c
groupByFM' p fx fy =
  (`impurely` fx) $ \stpx inix extx ->
  (`impurely` fy) $ \stpy iniy exty ->
  FoldM
    (\(~(stx, sty, p')) y -> do
      py <- p' y
      if py
        then do
          stx' <- stpx stx y
          return (stx', sty , p')
        else do
          stx' <- inix >>= flip stpx y
          sty' <- extx stx >>= stpy sty
          return (stx', sty', p y)
    )
    (liftM2 (,, const (return False)) inix iniy)
    (exty . snd3)



snd3 :: (a, b, c) -> b
{-# INLINE snd3 #-}
snd3 ~(_, y, _) = y


-- | Fold using the first Fold until False, then pass the result to the second Fold and continue
-- spanF :: (a -> Bool) -> Fold a b -> (b -> Fold a c) -> Fold a c


-- if empty, exty iniy
-- else let (x, y) = span (p first) xs

-- else fx until False
--   then update fy
--   and continue



-- -- filterEnum :: (a -> Bool) -> Fold a b -> Fold (Either i a) b
-- filterEnum p (Fold stp ini extr) = Fold (_ stp) ini (extr .
-- Fold (_ stp) ini extr





-- newtype Cofold n a m b = Cofold { runCofold :: Cofree (ReaderT (Vector n a, b) m) b }

-- -- cofold :: Cofree ((->) (a, b)) b -> Fold a b
-- -- cofold = flip (Fold (\(x :< xs) y -> curry xs y x)) extract


-- Want to compare (benchmark) Cofree folding (passing a continuation function) vs. Maybe folding (Just prev or Nothing)

-- prodPrevCofree :: Num a => Cofree ((->) (a, a)) a
-- {-# INLINE prodPrevCofree #-}
-- prodPrevCofree = 0 :< (\(_, x) -> x :< fix (\lp x' (y, z) -> (y + x' * z) :< lp z) x)

-- cofreeProd :: (Num a, Foldable t) => t a -> a
-- cofreeProd = foldCofree prodPrevCofree

-- foldlProd :: (Num a, Foldable t) => t a -> a
-- foldlProd = fst . foldl' (\(x, y) z -> maybe (z, Just z) (\y' -> (x + y' * z, Just z)) y) (0, Nothing)

-- The results (for lists) are surprising:
--   cofreeProd seems to take around 2 seconds/1e5
--   foldlProd seems to take around 1 seconds/1e9

-- The function(s) used to benchmark:
-- someFunc = do
--   n <- (`asTypeOf` (_ :: Int)) . read . Prelude.head <$> getArgs
--   -- print $ cofreeProd [1..n]
--   print $ foldlProd [1..n]
--

--   Why the huge difference?
--     Apparently unpacking the boxed Cofree function and applying it takes a lot longer than unpacking a Maybe.
--     Additionally, branch prediction might kick in, predicting (Just _) quite quickly as it's true for all after the first.

-- time ./cofree-foldl-utf8-exe 10000
-- 333333330001
-- ./cofree-foldl-utf8-exe 10000  0.00s user 0.01s system 67% cpu 0.021 total
-- time ./cofree-foldl-utf8-exe 100000
-- 333333333300001
-- ./cofree-foldl-utf8-exe 100000  0.05s user 0.14s system 350% cpu 0.055 total
-- time ./cofree-foldl-utf8-exe 1000000
-- 333333333333000001
-- ./cofree-foldl-utf8-exe 1000000  0.70s user 1.79s system 449% cpu 0.553 total
-- time ./cofree-foldl-utf8-exe 10000000
-- 1291940006558070913
-- ./cofree-foldl-utf8-exe 10000000  7.64s user 20.65s system 455% cpu 6.213 total

-- time ./cofree-foldl-utf8-exe 10000
-- 333333330001
-- ./cofree-foldl-utf8-exe 10000  0.00s user 0.01s system 51% cpu 0.020 total
-- time ./cofree-foldl-utf8-exe 100000
-- 333333333300001
-- ./cofree-foldl-utf8-exe 100000  0.00s user 0.01s system 42% cpu 0.019 total
-- time ./cofree-foldl-utf8-exe 1000000
-- 333333333333000001
-- ./cofree-foldl-utf8-exe 1000000  0.00s user 0.01s system 49% cpu 0.019 total
-- time ./cofree-foldl-utf8-exe 10000000
-- 1291940006558070913
-- ./cofree-foldl-utf8-exe 10000000  0.01s user 0.01s system 79% cpu 0.019 total
-- time ./cofree-foldl-utf8-exe 100000000
-- 667921401702298881
-- ./cofree-foldl-utf8-exe 100000000  0.06s user 0.01s system 94% cpu 0.077 total
-- time ./cofree-foldl-utf8-exe 1000000000
-- 3838615081755021825
-- ./cofree-foldl-utf8-exe 1000000000  2.16s user 0.41s system 347% cpu 0.740 total
-- time ./cofree-foldl-utf8-exe 10000000000
-- 1692314753435087873
-- ./cofree-foldl-utf8-exe 10000000000  41.04s user 8.83s system 537% cpu 9.285 total



foldCofree :: Foldable t => Cofree ((->) (b, a)) b -> t a -> b
{-# INLINE foldCofree #-}
foldCofree z = extract . foldl' (\(x :< xs) y -> xs (x, y)) z




fold2 :: Foldable t => (b -> a -> b) -> (b -> (a, a) -> b) -> b -> t a -> b
fold2 f g x = fst . foldl (\(y, z) w -> (maybe (f y w) (\q -> g y (q, w)) z, Just w)) (x, Nothing)

fold2Cofree :: Foldable t => b -> (a -> b) -> (b -> a -> a -> b) -> t a -> b
fold2Cofree x f g = foldCofree $ x :< (\(~(_, y)) -> (f y :< (fix (\lp p (z, w) -> (g z p w :< lp w)) y)))

fold3Cofree :: Foldable t => b -> (a -> b) -> (a -> a -> b) -> (b -> a -> a -> a -> b) -> t a -> b
fold3Cofree x f g h = foldCofree $ x :< (\(~(_, y)) -> (f y :< (\(~(_, z)) -> (g y z :< (fix (\lp s t (u, v) -> (h u s t v :< lp t v)) y z)))))


-- FoldN 0 a b = b -> t a -> b
-- FoldN 1 a b = b -> (a -> b) -> t a -> b
-- FoldN 2 a b = b -> (a -> b) -> (a -> a -> b) -> t a -> b
-- FoldN 3 a b = b -> (a -> b) -> (a -> a -> b) -> (b -> a -> a -> a -> b)
-- FoldN 4 a b = b -> (a -> b) -> (a -> a -> b) -> (a -> a -> a -> b) -> (b -> a -> a -> a -> a -> b)

-- FoldN 1 a b = b -> (b -> VecN 1 a -> b) -> t a -> b
-- FoldN 2 a b = b -> (b -> VecN 1 a -> b) -> (b -> VecN 2 a -> b) -> t a -> b

-- type FolderN n a b = b -> Vector n a -> b

-- data FoldN (n :: Nat) a b where
--   FoldN1 :: Fold a b -> FoldN 1 a b
--   FoldN  :: FoldN n a b -> (b -> Vector (n+1) a -> b) -> FoldN (n+1) a b


-- foldNDepth :: FoldN n a b -> Proxy n
-- foldNDepth _ = Proxy


-- foldN :: (Foldable t, KnownNat n) => FoldN n a b -> t a -> b
-- foldN (FoldN1 f) = fold f
-- foldN f@(FoldN fn fdr) =

-- if 2
--   fold2Cofree, f provided by


-- Want to generalize to foldN :: (VecN 0 a -> b) -> (VecN 1 a -> b) ->


-- how many previous?
--   zero:
--   one+

-- if end with zero,
-- there are zero in foldable


-- b :< (b -> a -> b :< (b -> a -> b ..

-- (b -> (a, a) -> b) -> b -> t a -> b

-- Fold a
-- liftA2 :: (b -> c -> d) -> Fold a b -> Fold a c -> Fold a d
-- liftA2 (,) :: Fold a b -> Fold a c -> Fold a (b, c)




-- foldl :: (a -> Char -> a) -> a -> Text -> a

someFunc :: IO ()
someFunc = putStrLn "someFunc"




