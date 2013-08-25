{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}

-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2013 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Keys in Morton order
--
-- This module provides combinators for shuffling together the bits of two
-- key components to get a key that is based on their interleaved bits.
--
-- See <http://en.wikipedia.org/wiki/Z-order_curve> for more information
-- about Morton order.
--
----------------------------------------------------------------------------

module Sparse.Matrix.Key
  ( Key(..)
  , compares
  , lts, les, eqs, nes, ges, gts
  , U.MVector(..)
  , U.Vector(..)
  ) where

import Data.Bits
import Control.Monad
import Control.Lens
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Unboxed as U
import Data.Word

-- * Morton Order

-- | @key i j@ interleaves the bits of the keys @i@ and @j@.
--
-- Keys are then just values sorted in \"Morton Order\".
data Key = Key {-# UNPACK #-} !Word32 {-# UNPACK #-} !Word32
  deriving (Show, Read, Eq)

instance Ord Key where
  Key a b `compare` Key c d
    | ab < cd && ab < xor ab cd = compare b d
    | otherwise = compare a c
    where ab = xor a b
          cd = xor c d

instance (a ~ Word32, b ~ Word32) => Field1 Key Key a b where
  _1 f (Key i j) = indexed f (0 :: Int) i <&> (Key ?? j)
  {-# INLINE _1 #-}

instance (a ~ Word32, b ~ Word32) => Field2 Key Key a b where
  _2 f (Key i j) = indexed f (1 :: Int) j <&> Key i
  {-# INLINE _2 #-}

instance U.Unbox Key

data instance U.MVector s Key = MV_Key {-# UNPACK #-} !Int !(U.MVector s Word32) !(U.MVector s Word32)
data instance U.Vector    Key = V_Key  {-# UNPACK #-} !Int !(U.Vector Word32) !(U.Vector Word32)

instance GM.MVector U.MVector Key where
  {-# INLINE basicLength #-}
  {-# INLINE basicUnsafeSlice #-}
  {-# INLINE basicOverlaps #-}
  {-# INLINE basicUnsafeNew #-}
  {-# INLINE basicUnsafeReplicate #-}
  {-# INLINE basicUnsafeRead #-}
  {-# INLINE basicUnsafeWrite #-}
  {-# INLINE basicClear #-}
  {-# INLINE basicSet #-}
  {-# INLINE basicUnsafeCopy #-}
  {-# INLINE basicUnsafeGrow #-}
  basicLength (MV_Key l _ _) = l
  basicUnsafeSlice i n (MV_Key _ u v)               = MV_Key n (GM.basicUnsafeSlice i n u) (GM.basicUnsafeSlice i n v)
  basicOverlaps (MV_Key _ u1 v1) (MV_Key _ u2 v2)   = GM.basicOverlaps u1 u2 || GM.basicOverlaps v1 v2
  basicUnsafeNew n                                  = liftM2 (MV_Key n) (GM.basicUnsafeNew n) (GM.basicUnsafeNew n)
  basicUnsafeReplicate n (Key x y)                  = liftM2 (MV_Key n) (GM.basicUnsafeReplicate n x) (GM.basicUnsafeReplicate n y)
  basicUnsafeRead (MV_Key _ u v) i                  = liftM2 Key (GM.basicUnsafeRead u i) (GM.basicUnsafeRead v i)
  basicUnsafeWrite (MV_Key _ u v) i (Key x y)       = GM.basicUnsafeWrite u i x >> GM.basicUnsafeWrite v i y
  basicClear (MV_Key _ u v)                         = GM.basicClear u >> GM.basicClear v
  basicSet (MV_Key _ u v) (Key x y)                 = GM.basicSet u x >> GM.basicSet v y
  basicUnsafeCopy (MV_Key _ u1 v1) (MV_Key _ u2 v2) = GM.basicUnsafeCopy u1 u2 >> GM.basicUnsafeCopy v1 v2
  basicUnsafeMove (MV_Key _ u1 v1) (MV_Key _ u2 v2) = GM.basicUnsafeMove u1 u2 >> GM.basicUnsafeMove v1 v2
  basicUnsafeGrow (MV_Key _ u v) n                  = liftM2 (MV_Key n) (GM.basicUnsafeGrow u n) (GM.basicUnsafeGrow v n)

instance G.Vector U.Vector Key where
  {-# INLINE basicLength #-}
  {-# INLINE basicUnsafeFreeze #-}
  {-# INLINE basicUnsafeThaw #-}
  {-# INLINE basicUnsafeSlice #-}
  {-# INLINE basicUnsafeIndexM #-}
  {-# INLINE elemseq #-}
  basicLength (V_Key v _ _) = v
  basicUnsafeFreeze (MV_Key n u v)               = liftM2 (V_Key n) (G.basicUnsafeFreeze u) (G.basicUnsafeFreeze v)
  basicUnsafeThaw (V_Key n u v)                  = liftM2 (MV_Key n) (G.basicUnsafeThaw u) (G.basicUnsafeThaw v)
  basicUnsafeSlice i n (V_Key _ u v)             = V_Key n (G.basicUnsafeSlice i n u) (G.basicUnsafeSlice i n v)
  basicUnsafeIndexM (V_Key _ u v) i              = liftM2 Key (G.basicUnsafeIndexM u i) (G.basicUnsafeIndexM v i)
  basicUnsafeCopy (MV_Key _ mu mv) (V_Key _ u v) = G.basicUnsafeCopy mu u >> G.basicUnsafeCopy mv v
  elemseq _ (Key x y) z = G.elemseq (undefined :: U.Vector Word32) x
                        $ G.elemseq (undefined :: U.Vector Word32) y z

compares :: Word32 -> Word32 -> Ordering
compares a b = case compare a b of
  LT | a < xor a b -> LT
  GT | b < xor a b -> GT
  _ -> EQ
{-# INLINE compares #-}

lts :: Word32 -> Word32 -> Bool
lts a b = a < b && a < xor a b
{-# INLINE lts #-}

les :: Word32 -> Word32 -> Bool
les a b = a <= b || xor a b <= b
{-# INLINE les #-}

eqs :: Word32 -> Word32 -> Bool
eqs a b = compares a b == EQ
{-# INLINE eqs #-}

nes :: Word32 -> Word32 -> Bool
nes a b = compares a b /= EQ
{-# INLINE nes #-}

gts :: Word32 -> Word32 -> Bool
gts a b = a > b && xor a b > b
{-# INLINE gts #-}

ges :: Word32 -> Word32 -> Bool
ges a b = a >= b || a >= xor a b
{-# INLINE ges #-}
