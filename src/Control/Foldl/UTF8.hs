{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveFunctor #-}

module Control.Foldl.UTF8 where


import Control.Applicative
import Control.Comonad
import Control.Comonad.Cofree
import Control.Comonad.Env
import Control.Comonad.Env.Class
import Control.Foldl
import Control.Monad hiding (fail)
import Control.Monad.Fail
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe
-- import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Control.Monad.Trans.Writer
import Data.ByteString (ByteString)
import Data.Char
import Data.Trie (Trie)
import Data.Word
import qualified Control.Foldl as F
import qualified Data.ByteString as B
import qualified Data.ByteString.UTF8 as UTF8
import qualified Data.ByteString.Unsafe as BU
import qualified Data.Trie as Tr
import Prelude hiding (fail)
import Data.Monoid


import Data.Range
import Control.Comonad.CofreeF
import Control.Foldl.Except

iterateCofree :: Functor f => i -> (i -> i) -> Cofree f a -> Cofree f (i, a)
iterateCofree x0 f (x :< xs) = (x0, x) :< (fmap (iterateCofree (f x0) f) xs)

enumCofree :: (Enum i, Functor f) => Cofree f a -> Cofree f (i, a)
enumCofree = iterateCofree (toEnum 0) succ


-- ByteString -> Lines -> Parse
--   String literals
--     Includes:
--       Line number
--       Initial character index
--       Character length
--       Byte length
--   Character literals
--   Comments
--   Indentation
--   Numeric literals
--   Alpha vars (isAlpha, liftM2 (||) isAlpha isDigit)
--   Symbolic vars (`elem` "~!@#$%^&*-=_+|:<>./?")
--     reserved Symbolic vars: '\'', '`', ',' ';'
--       prefix '\'' -> var '\''
--       postfix AlphaVar '\'' -> AlphaVar <> pure '\''
--       prefix '`' x -> case after x of
--                         '`' -> infix x
--                         _   -> (var '`') x
--       postfix '`' -> term (var '`')
--       ';' -> end sub-block
--   Lambdas: '\\'
--     (\x y z -> expr) -> lambdaN 3 'x 'y 'z (expr :: 'x -> 'y -> 'z -> expr')
--     So \ is an n-ary prefix function
--     and (->) is a binary infix function taking the result of the n-ary \ and applying it to its left argument.
--     It desugars to:
--     \(patt x) -> expr x
--     \((patt ('x :: a)) :: b) :: b -> (('x :: a) -> c) -> c
--       patt :: b -> a
--     (\) :: (b -> a) -> b -> (('x :: a) -> c) -> c
--     (->) :: (b -> (('x :: a) -> c) -> c) -> (('x :: a) -> c) -> b -> c
--     \x -> x
--     ((\) 'x) -> 'x
--     \(x, y) -> x + y
--     uncurry $ ((\) 'x) -> ((\) 'y -> (+) 'x 'y

--   Matched symbols: (), [], {}
--     () -> tupleN 0
--     (x) -> x
--     (x,y) -> tupleN 2 x y
--     (x,y,z) -> tupleN 3 x y z
--     (f x | x <- y, p x, let z = g x, p z) -> tupleComprehension f 'x (tupleN 4 ('x <- y) (let 'z = g 'x) (p 'z)
--       (y >>= \x -> p x >> let z = g x in z >>= p >> f x)
--     [] -> listN 0
--     [x] -> listN 1 x
--     [x..y] -> listRangeNM 1 1 [x] [y]
--     [x,y..z] -> listRange 2 1 [x,y] z
--     [f x | x <- y, p x]
--     (y >>= \x -> p x >> f x)
--       In essence, for tuple, list, set comprehension, we desugar to (do{} :: Applicative m => MaybeT m a),
--         In general, we lift the predicates using filterMaybeT and lift the extractions using lift
--         to get the final monadic value.

--         In some cases, we may be able to resolve certain m's to identity and provide the
--         user with user with a pure value even though we're using Applicative or Monad comprehension.

--         where pure (Bool) predicates and
--           pure m's (e.g. m = Identity, probably also Cofree?)
--           Foldable m's
--           Set-Foldable m's (e.g. Maybe, a set, range, etc.)
--         resp. are resolved to:
--           Maybe a = MaybeT Identity a
--           [a]
--           {a}
--         otherwise, we get:
--           MaybeT m a
--           m [a]
--           m {a}
--       MaybeT m a
--       filterMaybeT :: Monad m => (a -> m Bool) -> a -> MaybeT m a
--       filterMaybeT p x = MaybeT $ do
--         p' <- p x
--         if p'
--            then return (Just x)
--            else return Nothing

--       lift :: Monad m => m a -> MaybeT m a


sizedUncons :: ByteString -> Maybe (Char, Int, ByteString)
sizedUncons bs = do
  (c, sz) <- UTF8.decode bs
  return (c, sz, BU.unsafeDrop sz bs)

unfoldUncons :: (Enum i, Monad m) => ByteString -> CofreeF (MaybeT m) (Char, i, Int)
unfoldUncons = CofreeF . loop (toEnum 0) 0
  where
    loop i j cs = do
      (d, sz', cs') <- MaybeT . return . sizedUncons $ cs
      let sz'' = sz' + j
      return ((d, i, sz'') :< loop (succ i) sz'' cs')



data StringLit = StringLit { strBytes :: !ByteString
                           , strRange :: !(Range Pos)
                           } deriving (Eq, Ord, Show)

emptyStringLit :: StringLit
emptyStringLit = StringLit mempty mempty

unsafeSelect :: Range Int -> ByteString -> ByteString
unsafeSelect Range0 = mempty
unsafeSelect (Range1 x) = B.singleton . flip BU.unsafeIndex x
unsafeSelect (Range2 x y) = B.copy . BU.unsafeTake (1 + y - x) . BU.unsafeDrop x

toStringLit :: ByteString -> Range Pos -> StringLit
toStringLit = join . flip (fmap StringLit . unsafeSelect . fmap byteNum)



data Pos = Pos { charNum :: !Int
               , byteNum :: !Int
               } deriving (Eq, Ord, Show, Read)


unfoldUnconsC :: Monad m => ByteString -> CofreeF (MaybeT m) (Env Pos Char)
unfoldUnconsC = fmap (\(~(c, i, n)) -> EnvT (Pos i n) (return c)) . unfoldUncons

parseStringE :: Monad m => ByteString -> FoldE (Env Pos Char) m (Maybe StringLit)
parseStringE bs = parseStringWith (\x y -> return (toStringLit bs (pure (ask x) <> pure (ask y))))




-- newtype PosT m a = PosT { runPosT :: ReaderT (Range Pos) m a } deriving (Functor)

-- instance Applicative m => Applicative (PosT m) where
--   pure = PosT . pure
--   PosT f <*> PosT x = PosT (f <*> x)

-- instance Monad m => Monad (PosT m) where
--   PosT x >>= f = PosT (x >>= (runPosT . f))

-- instance MonadTrans PosT where
--   lift = PosT . lift

-- toPosT :: Monad m => CofreeF (MaybeT m) (Char, Int, Int) -> CofreeF (PosT (MaybeT m)) Char
-- toPosT = CofreeF . PosT . WriterT . fmap loop . runCofreeF
--   where
--     loop ~((c, i, sz) :< xs) = (c :< runCofreeF (toPosT (CofreeF xs)), pure (Pos i sz))

-- toPosT' :: Monad m => CofreeF (MaybeT m) (Char, Int, Int) -> CofreeF (PosT (MaybeT m)) Char
-- toPosT' = CofreeF . PosT . WriterT . fmap loop . runCofreeF
--   where
--     loop ~((c, i, sz) :< xs) = (c :< runCofreeF (toPosT (CofreeF xs)), pure (Pos i sz))


-- -- | `PosT` allows us to lift `Pos`ition info into the `CofreeF` context, exposing a cleaner and more specialized interface.
-- unfoldUnconsPos :: Monad m => ByteString -> CofreeF (PosT (MaybeT m)) Char
-- unfoldUnconsPos = toPosT . unfoldUncons




type Line = Int

newtype LineT m a = LineT { runLineT :: WriterT Line m a }


-- -- | When the first returns (Left), switch to the second. when it returns (Left), advance the third fold, switch to the first
-- -- (third_fold_context, Either (Either b first_context) (b, Either c second_context))
-- --
-- switchF :: FoldM (Either b) a b -> FoldM (Either c) a c -> Fold (b, c) d -> Fold a d
-- switchF f g h = (_ f g h)
-- switchF f g h = (`impurely` f) $ \stpx inix extx ->
--                 (`impurely` g) $ \stpy iniy exty ->
--                 (`purely` h)   $ \stpz iniz extz ->
--   Fold
--     (\(x, y) z -> case y of
--                     Left y' -> _ y'
--                     Right y' -> _ y'
--     )
--     (iniz, Left (Right inix))
--     (\(x, y) -> extz (either (either _ (\z -> (extx z, exty iniy))) (either _ _) y)
--     )




joinEither :: Either a a -> a
joinEither = either id id


prefixF :: (a -> Bool) -> Fold a b -> Fold (a, b) c -> Fold a (c, b)
prefixF p f g = (`purely` f) $ \stpx inix extx ->
                (`purely` g) $ \stpy iniy exty ->
  Fold
    (\(~(x, y)) z -> if p z
                        then (stpx x z, y)
                        else (inix, stpy y (z, extx x))
    )
    (inix, iniy)
    (\(~(x, y)) -> (exty y, extx x))

prefixFM :: Monad m => (a -> Bool) -> FoldM m a b -> FoldM m (a, b) c -> FoldM m a (c, b)
prefixFM p f g = (`impurely` f) $ \stpx inix extx ->
                 (`impurely` g) $ \stpy iniy exty ->
  FoldM
    (\(~(x, y)) z -> if p z
                        then do
                          x' <- stpx x z
                          return (x', y)
                        else do
                          inix' <- inix
                          x'    <- extx x
                          y'    <- stpy y (z, x')
                          return (inix', y')
    )
    (liftM2 (,) inix iniy)
    (\(~(x, y)) -> liftM2 (,) (exty y) (extx x))

-- | Example use of prefixF
spacedF :: Enum spaces => Fold (Char, spaces) a -> Fold Char (a, spaces)
spacedF = prefixF isSpace enumF

-- | Example use of prefixFM
spacedFM :: (Enum spaces, Monad m) => FoldM m (Char, spaces) a -> FoldM m Char (a, spaces)
spacedFM = prefixFM isSpace (generalize enumF)


enumF :: Enum i => Fold a i
enumF = Fold (\x _ -> succ x) (toEnum 0) id

chunkF :: (a -> Bool) -> Fold a b -> Fold b c -> Fold a c
chunkF p f g = (`purely` f) $ \stpx inix extx ->
               (`purely` g) $ \stpy iniy exty ->
  Fold
    (\(~(x, y)) z -> if p z
                        then (inix, stpy y (extx x))
                        else (stpx x z, y)
    )
    (inix, iniy)
    (\(~(_, y)) -> exty y)

chunkFM :: Monad m => (a -> Bool) -> FoldM m a b -> FoldM m b c -> FoldM m a c
chunkFM p f g = (`impurely` f) $ \stpx inix extx ->
                 (`impurely` g) $ \stpy iniy exty ->
  FoldM
    (\(~(x, y)) z -> if p z
                        then do
                          inix' <- inix
                          x'    <- extx x
                          y'    <- stpy y x'
                          return (inix', y')
                        else do
                          x'    <- stpx x z
                          return (x', y)
    )
    (liftM2 (,) inix iniy)
    (\(~(_, y)) -> exty y)

-- | Example usage of chunkF
linesF :: Fold Char b -> Fold b c -> Fold Char c
linesF = chunkF (== '\n')

-- | Example usage of chunkFM
linesFM :: Monad m => FoldM m Char b -> FoldM m b c -> FoldM m Char c
linesFM = chunkFM (== '\n')




-- enumUnfoldUncons :: Enum i => ByteString -> Maybe (Cofree Maybe (i, (Char, Int, ByteString)))
-- enumUnfoldUncons = fmap enumCofree . unfoldUncons



