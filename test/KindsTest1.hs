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
{-# LANGUAGE MagicHash                  #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -fenable-rewrite-rules  #-}

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

-- type family T a b :: *
-- type instance T Nat = Phantom   -- must fail: too few args

--------------------------------------------------------------------------------
-- Rewrite rules
--------------------------------------------------------------------------------

{-# RULES

"rule1" forall x . 
          myPhantom2 (Phantom x) = x

 #-}

--------------------------------------------------------------------------------
-- castBin
--------------------------------------------------------------------------------

newtype Bin a = BinPtr Nat -- deriving (Eq, Ord, Show, Bounded)

castBin :: Bin a -> Bin b
castBin (BinPtr i) = BinPtr i

returnP :: a -> Proxy a
returnP = undefined

fmapP :: (a -> b) -> Proxy a -> Proxy b
fmapP = undefined

putNat :: Nat -> Proxy (Bin Nat)
putNat n = returnP (BinPtr n)

data Whatever
data HasNat = HasNat Nat Whatever

put :: HasNat -> Proxy (Bin HasNat)
put (HasNat n _) = fmapP castBin (putNat n)

--------------------------------------------------------------------------------
-- DPH Vector
--------------------------------------------------------------------------------

class DT a where -- forall k:BOX a:k. Constraint
  data Dist a -- forall k:BOX. k -> *

-- class Star (a :: *)

instance {- (Star a) => -} DT (Proxy a) where -- forall k:BOX a:k. DT * (Proxy k a)
  data Dist (Proxy a) = DProxy

-- data DistProxy a = DProxy    -- Source
-- Gives rise to:
--    DistProxy :: forall k1:BOX. k1 -> *
--    DProxy    :: forall k1. forall (a:k1). DistProxy k1 a
--    ax7 k1 a  :: DispProxy k1 a ~ Dist * (Proxy k1 a)
-- $WDVector :: forall (k1:BOX). forall (a:k1). Dist * (Proxy k1 a)
-- $WDVector k1 a = (DProxy k1 a) |> ax7 k1 a

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

writeEx :: Ex
writeEx = Ex Ze (const (Su Ze))

--------------------------------------------------------------------------------
-- T1123 (-dcore-lint error)
--------------------------------------------------------------------------------

data A s = A { unA :: Nat }

runA1 :: (forall s. A s) -> Nat -- Uncomment for error
runA1 a = unA a

--------------------------------------------------------------------------------
-- ContT
--------------------------------------------------------------------------------

newtype ContT r m a = ContT { runContT :: (a -> m r) -> m r }

mapContT :: (m r -> m r) -> ContT r m a -> ContT r m a
mapContT f m = ContT $ f . runContT m

--------------------------------------------------------------------------------
-- doaitse
--------------------------------------------------------------------------------
{-
data Exists f = forall a . Exists (f a)

data Ref env a where
  Zero :: Ref (a,env') a -- Comment this line for a bonus

f1 :: forall env. (Exists (Ref env)) -> Nat
f1 (Exists (ref1 :: Ref env b)) = Ze
-}
--------------------------------------------------------------------------------
-- gadt9
--------------------------------------------------------------------------------
{-
data X a b where
    X :: X a a

data Y x a b where
    Y :: x a b -> x b c -> Y x a c

doy :: Y X a b -> Y X a b
doy (Y X X) = Y X X
-}
--------------------------------------------------------------------------------
-- gadt11
--------------------------------------------------------------------------------
{-
data X f = X (f ())

data B a where
  B1 :: X []
  B2 :: B [Nat]
-}
--------------------------------------------------------------------------------
-- scoped
--------------------------------------------------------------------------------
{-
data C x y where -- * -> * -> *
     C :: a -> C a a

data D x y where -- k -> * -> *
     D :: C b c -> D a c

g3 :: forall x y . D x y -> ()
g3 (D (C (p :: y))) = ()
-}
--------------------------------------------------------------------------------
-- GEq1
--------------------------------------------------------------------------------
{-
class GEq' f where
  geq' :: f a -> f a -> Nat

class Generic a where 
  type Rep a :: * -> *
  from :: a -> Rep a a

class GEq a where 
  geq :: (Generic a, GEq' (Rep a)) => a -> a -> Nat
  geq x y = geq' (from x) (from y)
-}
--------------------------------------------------------------------------------
-- GADT1
--------------------------------------------------------------------------------

type family Id n
type instance Id n = n

--------------------------------------------------------------------------------
-- SimpleFail4
--------------------------------------------------------------------------------

class C2 a where
  type S2 a :: *
{-
instance C2 a where
  type S2 Nat = Nat
-}

--------------------------------------------------------------------------------
-- T2677
--------------------------------------------------------------------------------

type family A1 (x :: *) :: *
type instance A1 a = a
type instance A1 a = a -- just works!... but shouldn't.

--------------------------------------------------------------------------------
-- read056
--------------------------------------------------------------------------------
{-
class C a
instance C Nat

newtype Foo = Foo Nat
    deriving C
-}
--------------------------------------------------------------------------------
-- T303
--------------------------------------------------------------------------------
-- Fails with commented out "ret", without the comment, and both failures seem
-- still independent from the original T303 failure.
{-
class IxMonad m where
    ret :: a -> m i i a

data T a b c = T
instance IxMonad T where
    --ret _ = T
-}
--------------------------------------------------------------------------------
-- rule2
--------------------------------------------------------------------------------

foo :: (forall m. m a -> m b) -> m a -> m b
foo f = f

blip = foo (\x -> x)

--------------------------------------------------------------------------------
-- T2478
--------------------------------------------------------------------------------
-- Lack of zonking?
{-
data TrafoE t = forall env2 . TrafoE Nat t
trafo () = TrafoE
-}
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
