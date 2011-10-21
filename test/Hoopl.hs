{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE NoImplicitPrelude          #-}

module Hoopl where

data Fuel = Fuel

data Pair a b = Pair a b

class Monad m where
  bind :: m a -> (a -> m b) -> m b
  return :: a -> m a

class Monad m => CheckpointMonad m where
  type Checkpoint m
  checkpoint :: m (Checkpoint m)

newtype CheckingFuelMonad m a = FM { unFM :: Fuel -> m (Pair a Fuel) }
instance Monad m => Monad (CheckingFuelMonad m)

instance CheckpointMonad m => CheckpointMonad (CheckingFuelMonad m) where
  type Checkpoint (CheckingFuelMonad m) = Pair Fuel (Checkpoint m)
  checkpoint = FM (\f -> bind checkpoint (\s -> return (Pair (Pair f s) f)))
