{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE MagicHash                  #-}

module KindsTest1 where

--import GHC.Prim

--------------------------------------------------------------------------------
-- Type-level peano naturals
--------------------------------------------------------------------------------

data Nat = Ze | Su Nat

data List a = Nil | Cons a (List a)

data Vec :: * -> Nat -> * where
  VNil  :: Vec a Ze
  VCons :: a -> Vec a n -> Vec a (Su n)

vec1 :: Vec Nat (Su Ze)
vec1 = VCons Ze VNil

-- Correctly fails to kind-check
{-
vec2 :: Vec Nat Nat
vec2 = vec2
-}

--------------------------------------------------------------------------------
-- Phantom types
--------------------------------------------------------------------------------

data Proxy t = Proxy

data Phantom a = Phantom Nat

myPhantom2 :: Phantom a -> Nat
myPhantom2 (Phantom x) = x

testPhantom2 = myPhantom2 (Phantom Ze)

--------------------------------------------------------------------------------
-- Rewrite rules
--------------------------------------------------------------------------------

{-# RULES

"rule1" forall x . 
          myPhantom2 (Phantom x) = x

 #-}

--------------------------------------------------------------------------------
-- Classes
--------------------------------------------------------------------------------

data TypeRep = TypeRep -- somewhat simplified...

class MyTypeable t where
  myTypeOf :: Proxy t -> TypeRep

instance MyTypeable Nat  where myTypeOf _ = TypeRep
instance MyTypeable List where myTypeOf _ = TypeRep

--------------------------------------------------------------------------------
-- T5481
--------------------------------------------------------------------------------
{-
class Foo a b where
  type X a

instance Foo a b where
  type X a = b -- Doesn't work if put on the class declaration as default
-}
-- Also, even the code above alone already generates invalid interface files

--------------------------------------------------------------------------------
-- Existentials
--------------------------------------------------------------------------------

data Ex where
  Ex :: a -> (a -> Nat) -> Ex

readEx :: Ex -> Nat
readEx (Ex a f) = f a

const :: a -> b -> a
const a b = a

writeEx :: Ex
writeEx = Ex Ze (const (Su Ze))

--------------------------------------------------------------------------------
-- T1123 (-dcore-lint error)
--------------------------------------------------------------------------------

data A s = A { unA :: Nat }

runA1 :: (forall s. A s) -> Nat -- Uncomment for error
runA1 a = unA a

--------------------------------------------------------------------------------
-- Stuff below here depends on (some) libraries being present
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Unboxed stuff
--------------------------------------------------------------------------------
{-
testUnbox :: Int# -> a -> a
testUnbox n a = a
-}
