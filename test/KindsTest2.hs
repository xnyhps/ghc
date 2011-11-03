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

data ListV :: [*] -> * where
  NilV  :: ListV '[]
  -- ConsV  :: a -> ListV t -> ListV (a ': t)

{-
data List a = Nil | Cons a (List a)

data ListV :: List * -> * where
  NilV  :: ListV Nil
-}
{-
data PairV :: (*,*) -> * where
  PairV :: a -> b -> PairV '(a,b)
-}