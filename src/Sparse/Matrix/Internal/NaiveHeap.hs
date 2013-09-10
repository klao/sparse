{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2013 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Naive non-empty pairing heaps
--
-- <https://www.fpcomplete.com/user/edwardk/revisiting-matrix-multiplication/part-5>
-----------------------------------------------------------------------------
module Sparse.Matrix.Internal.NaiveHeap
  ( Heap(..)
  , mix
  , singleton
  , head
  , tail
  , fromList
  , streamHeapWith
  , streamHeapWith0
  ) where

import Control.Applicative
import Control.Lens
import Data.Foldable
import Data.Monoid
import Data.Vector.Fusion.Stream.Monadic hiding (singleton, fromList, head, tail)
import Data.Vector.Fusion.Stream.Size
import Sparse.Matrix.Internal.Key
import Prelude hiding (head, tail)

data Heap a = Heap {-# UNPACK #-} !Key a [Heap a]
  deriving (Show,Read)

-- | Append two heaps where we know every key in the first occurs before every key in the second
--
-- >>> head $ singleton (Key 1 1) 1 `fby` singleton (Key 2 2) 2
-- (Key 1 1,1)
-- TODO(klao): _this_ is the operation that's missing from the naive approach
-- fby :: Heap a -> Heap a -> Heap a
-- fby = mix

-- | Interleave two heaps making a new 'Heap'
--
-- >>> head $ singleton (Key 1 1) 1 `mix` singleton (Key 2 2) 2
-- (Key 1 1,1)
mix :: Heap a -> Heap a -> Heap a
mix x@(Heap i a as) y@(Heap j b bs)
  | i <= j    = Heap i a (y:as)
  | otherwise = Heap j b (x:bs)

-- | Interleave a non-empty list of heaps making a new 'Heap'
--
-- This is the basic operation from which the pairing heaps got their
-- name.
mixAll :: [Heap a] -> Heap a
mixAll [x] = x
mixAll [x, y] = mix x y
mixAll (x:y:ys) = mix (mix x y) (mixAll ys)
mixAll [] = error "empty list of heaps"

-- |
-- >>> head $ singleton (Key 1 1) 1
-- (Key 1 1,1)
head :: Heap a -> (Key, a)
head (Heap i a _) = (i, a)

-- |
-- >>> tail $ singleton (Key 1 1) 1
-- Nothing
tail :: Heap a -> Maybe (Heap a)
tail (Heap _ _ xs) = pop xs

pop :: [Heap a] -> Maybe (Heap a)
pop [] = Nothing
pop xs = Just $ mixAll xs

-- |
-- >>> singleton (Key 1 1) 1
-- Heap (Key 1 1) 1 []
singleton :: Key -> a -> Heap a
singleton k v = Heap k v []

-- | Build a 'Heap' from a jumbled up list of elements.
fromList :: [(Key,a)] -> Heap a
fromList [] = error "empty Heap"
fromList xs = mixAll $ Prelude.map (uncurry singleton) xs


-- | Build a 'Heap' from an list of elements that must be in strictly ascending Morton order.
-- TODO(klao): again, here we can't do anything smart here
-- fromAscList :: [(Key,a)] -> Heap a
-- fromAscList ((k0,v0):xs) = Prelude.foldr (\(k,v) r -> fby (singleton k v) r) (singleton k0 v0) xs
-- fromAscList [] = error "empty Heap"

-- * Instances

instance Functor Heap where
  fmap f (Heap k a xs) = Heap k (f a) (fmap f <$> xs)

instance FunctorWithIndex Key Heap where
  imap f (Heap k a xs) = Heap k (f k a) (imap f <$> xs)

instance Foldable Heap where
  foldMap f = go where
    go (Heap _ a xs) = case pop xs of
      Nothing -> f a
      Just h  -> f a `mappend` go h
  {-# INLINE foldMap #-}

instance FoldableWithIndex Key Heap where
  ifoldMap f = go where
    go (Heap i a xs) = case pop xs of
      Nothing -> f i a
      Just h  -> f i a `mappend` go h
  {-# INLINE ifoldMap #-}

instance Traversable Heap where
  traverse f xs = fromList <$> traverse (traverse f) (itoList xs)
  {-# INLINE traverse #-}

instance TraversableWithIndex Key Heap where
  itraverse f xs = fromList <$> traverse (\(k,v) -> (,) k <$> f k v) (itoList xs)
  {-# INLINE itraverse #-}

-- * Streaming

data HeapState a
  = Start !(Heap a)
  | Ready {-# UNPACK #-} !Key a !(Heap a)
  | Final {-# UNPACK #-} !Key a
  | Finished

-- | Convert a 'Heap' into a 'Stream' folding together values with identical keys using the supplied
-- addition operator.
streamHeapWith :: Monad m => (a -> a -> a) -> Maybe (Heap a) -> Stream m (Key, a)
streamHeapWith f h0 = Stream step (maybe Finished Start h0) Unknown where
  step (Start (Heap i a xs)) = return $ Skip $ maybe (Final i a) (Ready i a) $ pop xs
  step (Ready i a (Heap j b xs)) = return $ case compare i j of
    LT -> Yield (i, a)      $ maybe (Final j b) (Ready j b) $ pop xs
    EQ | c <- f a b -> Skip $ maybe (Final i c) (Ready i c) $ pop xs
    GT -> Yield (j, b)      $ maybe (Final i a) (Ready i a) $ pop xs
  step (Final i a) = return $ Yield (i,a) Finished
  step Finished    = return Done
  {-# INLINE [1] step #-}
{-# INLINE [0] streamHeapWith #-}

-- | Convert a 'Heap' into a 'Stream' folding together values with identical keys using the supplied
-- addition operator that is allowed to return a sparse 0, by returning 'Nothing'.
streamHeapWith0 :: Monad m => (a -> a -> Maybe a) -> Maybe (Heap a) -> Stream m (Key, a)
streamHeapWith0 f h0 = Stream step (maybe Finished Start h0) Unknown where
  step (Start (Heap i a xs))     = return $ Skip $ maybe (Final i a) (Ready i a) $ pop xs
  step (Ready i a (Heap j b xs)) = return $ case compare i j of
    LT -> Yield (i, a) $ maybe (Final j b) (Ready j b) $ pop xs
    EQ -> case f a b of
      Nothing -> Skip  $ maybe Finished Start $ pop xs
      Just c  -> Skip  $ maybe (Final i c) (Ready i c) $ pop xs
    GT -> Yield (j, b) $ maybe (Final i a) (Ready i a) $ pop xs
  step (Final i a) = return $ Yield (i,a) Finished
  step Finished = return Done
  {-# INLINE [1] step #-}
{-# INLINE [0] streamHeapWith0 #-}
