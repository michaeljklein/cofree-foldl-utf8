module Data.Token where


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
import Control.Monad.Trans.Reader
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


-- (Enum i, Monad m) => ByteString -> CofreeF  (Char, i)

newtype TokenStateT i m a = TokenStateT { runTokenStateT :: StateT (Fold ByteString (TokenState i)) (ReaderT ByteString m) a }

data TokenState i = TokenState { thisToken :: !(Token i)
                               , lastToken :: !(Token i)
                               , tokenTrie :: Trie i
                               }


type Token i = i

foldTrie :: Enum i => Fold ByteString (TokenState i)
foldTrie =
  Fold
    (\(TokenState _ i t) x -> case Tr.lookup x t of
      Nothing -> let i' = succ i in
                   TokenState i' i' (Tr.insert x i' t)
      ~(Just j) -> TokenState j i t
    )
    (TokenState (toEnum 0) (toEnum 0) Tr.empty)
    id

foldTrieM :: (Enum i, Monad m) => FoldM m ByteString (TokenState i)
foldTrieM = generalize foldTrie

fst3 :: (a, b, c) -> a
fst3 ~(x, _, _) = x

