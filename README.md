# cofree-foldl-utf8

[`Cofree`](http://hackage.haskell.org/package/free-5.0.2/docs/Control-Comonad-Cofree.html)
and [`Fold`](https://hackage.haskell.org/package/foldl-1.4.0/docs/Control-Foldl.html#t:Fold)
based parsers and combinators for `UTF8` [`ByteString`](http://hackage.haskell.org/package/bytestring)
input.


## Contents

- Input streams are modeled using `CofreeF`: `Control.Comonad.CofreeF`

```haskell
newtype CofreeF f a = CofreeF { runCofreeF :: f (Cofree f a) }
```


- Early result parsing (e.g. `takeWhile1`) is implemented using `FoldE`: `Control.Foldl.Except`

```haskell
newtype FoldE a m b = FoldE { runFoldE :: FoldM (ExceptT b m) a b }
```


- Conversion from UTF8 `ByteString`s to `Monad`ic `CofreeF` streams of `Char`s: `Control.Foldl.UTF8`
  + Streams with source locations
  + Prefixes (by predicate)
    * Counting prefix spaces in an input stream
  + Chunking input
    * Lines


- Utilities for `Fold`, `FoldM`: `Control.Foldl.Utils`

- Pure and `Monad`ic left folds over non-empty inputs: `Control.Foldl1`

- Possibly empty strict ranges: `Data.Range`

- Tokenization of input using a `ByteString` `Trie` and folds: `Data.Token`
  + Tokens are provided through an `Enum` instance

- Another tokenization implementation and a number of combinators for parsing with `Fold`, `FoldM`: `Lib`


## Docs

Haddock-generated documentation is available at:
https://michaeljklein.github.io/cofree-foldl-utf8/

