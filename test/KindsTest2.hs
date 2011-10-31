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
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE PolyKinds                  #-}

module KindsTest2 where

--------------------------------------------------------------------------------
-- Type-level peano naturals
--------------------------------------------------------------------------------
data Nat = Ze | Su Nat

data Vec :: * -> Nat -> * where
  VNil  :: Vec a Ze
  VCons :: a -> Vec a n -> Vec a (Su n)

vec1 :: Vec Nat (Su Ze)
vec1 = VCons Ze VNil

-- Correctly fails to kind-check
{-
vec2 :: Vec Nat Nat
vec2 = undefined
-}

--------------------------------------------------------------------------------
-- Phantom types
--------------------------------------------------------------------------------

data Phantom a = Phantom Int

myPhantom1 :: Monad m => Phantom m -> m Int
myPhantom1 (Phantom x) = return x

myPhantom2 :: Phantom a -> Int
myPhantom2 (Phantom x) = x

testPhantom1 = myPhantom1 (Phantom 2 :: Phantom [])
testPhantom2 = myPhantom2 (Phantom 2)

--------------------------------------------------------------------------------
-- I think this fails in UHC (should test; see EHC\test\regress\99\KindSig2.hs)
--------------------------------------------------------------------------------

data UU a = UU

instance Functor UU where fmap f UU = UU
instance (Show a) => Show (UU a) where show UU = ""

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
  Ex :: a -> (a -> String) -> Ex

readEx :: Ex -> String
readEx (Ex a f) = f a

writeEx :: Ex
writeEx = Ex 2 show

--------------------------------------------------------------------------------
-- T1123 (-dcore-lint error)
--------------------------------------------------------------------------------

data A s = A { unA :: () }

--runA1 :: (forall s. A s) -> () -- Uncomment for error
runA1 a = unA a

--------------------------------------------------------------------------------
-- Simple generic programming (instant-generics-like library)
--------------------------------------------------------------------------------

data U a = UNIT | SUM (U a) (U a) | PRODUCT (U a) (U a) | REC a

-- GADT interpretation
data I :: U * -> * where
  Unit          :: I UNIT
  Inl           :: I a -> I (SUM a b)
  Inr           :: I b -> I (SUM a b)
  Product       :: I a -> I b -> I (PRODUCT a b)
  Rec           :: a -> I (REC a)

{-
-- Data family interpretation
-- Note that we cannot use a type family due to lack of injectivity
data family   I (a :: U *)     :: *
data instance I  UNIT           = Unit
data instance I (SUM a b)       = Inl (I a) | Inr (I b)
data instance I (PRODUCT a b)   = Product (I a) (I b)
data instance I (REC a)         = Rec a
-}

{-
size :: I rep -> Int
size Unit = 0
size (Inl a) = size a
size (Inr b) = size b
size (Product a b) = size a + size b
-- size (Rec x) = 1 + size x -- how should we do this?...
-}

-- Class embedding types and their generic representation
class Generic (a :: *) where
  type Rep a :: U *
  from :: a -> I (Rep a)
  to   :: I (Rep a) -> a

-- Generic size on representations
class GSize (a :: U *) where
  gsize :: I a -> Int

instance GSize UNIT where
  gsize Unit = 0

instance (GSize a, GSize b) => GSize (SUM a b) where
  gsize (Inl x) = gsize x
  gsize (Inr x) = gsize x

instance (GSize a, GSize b) => GSize (PRODUCT a b) where
  gsize (Product a b) = gsize a + gsize b

instance (Size a) => GSize (REC a) where
  gsize (Rec x) = 1 + size x

-- Size on datatypes
class Size (a :: *) where
  size :: a -> Int
  default size :: (Generic a, GSize (Rep a)) => a -> Int
  size = gsize . from

instance (Size a) => Size [a] -- default
instance Size Char where size _ = 1 -- adhoc

-- Example encoding: lists
instance Generic [a] where
  type Rep [a] = SUM UNIT (PRODUCT (REC a) (REC [a]))
  from []    = Inl Unit
  from (h:t) = Inr (Product (Rec h) (Rec t))
  to (Inl Unit)                      = []
  to (Inr (Product (Rec h) (Rec t))) = h:t

-- Testing size
test1 = size "abc"

--------------------------------------------------------------------------------
-- Indexed functors (didn't get very far, lacking explicit kind polymorphism)
--------------------------------------------------------------------------------

{-
--infixr 5 :+:
infixr 6 :*:

data PLUS a b = Inl a | Inr b
--data (:*:) a b = a :*: b

data IndFun i o = UNIT | IN i | TAG o (IndFun i o)
                | SUM  (IndFun i o) (IndFun i o)
                | PROD (IndFun i o) (IndFun i o)
                | FIX  (IndFun (PLUS i o) o)

data Interprt (f :: IndFun Nat Nat) (i :: Nat -> *) (o :: Nat) :: * where
  Unit  :: Interprt UNIT r o
  I     :: r i -> Interprt (IN i) r o
  Tag   :: Interprt f r o -> Interprt (TAG o f) r o
  L     :: Interprt f r o -> Interprt (SUM f g) r o
  R     :: Interprt g r o -> Interprt (SUM f g) r o
  (:*:) :: Interprt f r o -> Interprt f r o -> Interprt (PROD f g) r o
  --Mu    :: Interprt f (r :/: Interprt (FIX f) r) o -> Interprt (FIX f) r o
  --Mu    :: Fix f r o -> Interprt (FIX f) r o
  --Mu    :: f (r :/: Interprt f r) o -> Interprt (FIX f) r o

data InterprtFix :: IndFun (PLUS Nat Nat) Nat -> (Nat -> *) -> Nat -> * where
  Mu    :: InterprtFix f (r :/: InterprtFix f r) o -> InterprtFix f r o

{-
data Fix :: (IndFun (PLUS Nat Nat) Nat)
         -> ((Nat -> *) -> (Nat -> *)) where
  FixV :: Interprt f (r :/: Fix f r) ix -> Fix f r ix
-}
-- data Fix f r ix = FixV (f (r :/: Fix f r) ix)

-- (:/:) :: (i1 -> *) -> (i2 -> *) -> (Either i1 i2 -> *)
data (:/:) :: (Nat -> *) -> (Nat -> *) -> (PLUS Nat Nat) -> * where
  JL :: f ix1 -> (f :/: g) (Inl ix1)
  JR :: g ix2 -> (f :/: g) (Inr ix2)
-}

--------------------------------------------------------------------------------
-- MultiP (currently fails but shouldn't!)
--------------------------------------------------------------------------------
{-
type T0 = Ze
type T1 = Su T0
type T2 = Su T1

-- (!) at the type level
type family El (n :: Nat) (l :: [*]) :: *
type instance El Ze     (h ': t) = h
type instance El (Su n) (h ': t) = El n t

{-
-- The following might be useful, but are not used at the moment
-- ($) at the type level (well, not quite ($), in fact...)
class Apply (fs :: [*]) (es :: [*]) where
  type ApplyT (fs :: [*]) (es :: [*]) :: [*]
  apply :: ListV fs -> ListV es -> ListV (ApplyT fs es)

instance Apply '[] '[] where
  type ApplyT '[] '[] = '[]
  apply NilV NilV = NilV

instance (Apply fs es) => Apply ((e1 -> e2) ': fs) (e1 ': es) where
  type ApplyT ((e1 -> e2) ': fs) (e1 ': es) = e2 ': ApplyT fs es
  apply (ConsV f fs) (ConsV e es) = ConsV (f e) (apply fs es)
-}

-- Value mirror for the list kind
data ListV :: [*] -> * where
  NilV  :: ListV '[]
  ConsV :: a -> ListV t -> ListV (a ': t)

-- Value mirror for the Nat kind
data NatV :: Nat -> * where
  ZeW :: NatV Ze
  SuW :: NatV n -> NatV (Su n)

-- Generic universe
data MultiP x = UNIT
              | KK x -- wish I could just write * instead of x
              | SUM  (MultiP x) (MultiP x)
              | PROD (MultiP x) (MultiP x)
              | PAR Nat
              | REC

-- Universe interpretation
data Interprt :: MultiP * -> [*] -> * -> * where
  Unit  :: Interprt UNIT lp r
  K     :: x -> Interprt (KK x) lp r
  L     :: Interprt a lp r -> Interprt (SUM a b) lp r
  R     :: Interprt b lp r -> Interprt (SUM a b) lp r
  Prod  :: Interprt a lp r -> Interprt b lp r -> Interprt (PROD a b) lp r
  Par   :: NatV n -> El n lp -> Interprt (PAR n) lp r
  Rec   :: r -> Interprt REC lp r

-- Embedding values into the universe
class Generic a where
  type Rep a :: MultiP *
  type Es a  :: [*]
  from :: a -> Interprt (Rep a) (Es a) a
  to   :: Interprt (Rep a) (Es a) a -> a

-- Parameter map over the universe
class PMap (rep :: MultiP *) where
  pmap :: (forall n. NatV n -> El n lp1 -> El n lp2)
       -> (r -> s) -> Interprt rep lp1 r -> Interprt rep lp2 s

instance PMap UNIT where
  pmap _ _ Unit = Unit

instance PMap (KK x) where
  pmap _ _ (K x) = K x

instance (PMap a, PMap b) => PMap (SUM a b) where
  pmap f g (L x) = L (pmap f g x)
  pmap f g (R x) = R (pmap f g x)

instance (PMap a, PMap b) => PMap (PROD a b) where
  pmap f g (Prod x y) = Prod (pmap f g x) (pmap f g y)

instance PMap (PAR p) where
  pmap f _ (Par n p) = Par n (f n p)

instance PMap REC where
  pmap _ g (Rec p) = Rec (g p)

-- User-facing function
pmapu :: (Generic a, Generic b, PMap (Rep a), Rep a ~ Rep b)
      => (forall n. NatV n -> El n (Es a)-> El n (Es b)) -> a -> b
pmapu f = to . pmap f (pmapu f). from


-- Example: lists
instance Generic [a] where
  type Rep [a] = SUM UNIT (PROD (PAR T0) REC)
  type Es  [a] = a ': '[]
  from [] = L Unit
  from (h:t) = R (Prod (Par ZeW h) (Rec t))
  to (L Unit) = []
  to (R (Prod (Par ZeW h) (Rec t))) = h:t

-- Map on lists: we can define an auxiliary function with the usual type...
pmapList :: forall a b. (a -> b) -> [a] -> [b]
pmapList f l = pmapu g l where
  g :: forall n. NatV n -> El n (Es [a]) -> El n (Es [b])
  g ZeW x = f x

-- ... or use pmapu directly
pmapExample1 :: [String]
pmapExample1 = pmapu f [1..10::Int] where
  f :: forall n. NatV n -> El n (Es [Int]) -> El n (Es [String])
  f ZeW = show

-- Example: Either
instance Generic (Either a b) where
  type Rep (Either a b) = SUM (PAR T0) (PAR T1)
  type Es  (Either a b) = a ': b ': '[]
  from (Left  a) = L (Par ZeW a)
  from (Right b) = R (Par (SuW ZeW) b)
  to (L (Par ZeW a)) = Left a
  to (R (Par (SuW ZeW) b)) = Right b

pmapEither :: forall a1 a2 b1 b2.
              (a1 -> a2) -> (b1 -> b2) -> Either a1 b1 -> Either a2 b2
pmapEither f g = pmapu h where
  h :: forall n. NatV n -> El n (Es (Either a1 b1)) -> El n (Es (Either a2 b2))
  h ZeW = f
  h (SuW ZeW) = g
-}