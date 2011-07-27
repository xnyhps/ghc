%
% (c) The University of Glasgow 2006
% (c) The GRASP/AQUA Project, Glasgow University, 1992-1998
%
\section[Demand]{@Demand@: the amount of demand on a value}

\begin{code}
module Demand(
	DemandP(..), Demand,
	topDmd, lazyDmd, seqDmd, evalDmd, errDmd, isStrictDmd, 
	isTop, isAbsent, seqDemand,

	DmdTypeP(..), DmdType, 
        topDmdType, botDmdType, mkDmdType, 
        mkTopDmdType, dmdTypeDepth, seqDmdType,

	DmdResultP(..), DmdResult,
        retCPR, isBotRes, returnsCPR, resTypeArgDmd,

	DmdEnv, emptyDmdEnv,
	
	DemandPs(..), Demands, mapDmds, zipWithDmds, allTop, seqDemands,

	StrictSig(..), mkStrictSig, topSig, botSig, cprSig,
        isTopSig, isTopTopSig, pprStrictSig, pprDmdType,
	splitStrictSig, increaseStrictSigArity,
	appIsBottom, isBottomingSig, seqStrictSig,
     ) where

#include "HsVersions.h"

import {-# SOURCE #-} DataCon (DataCon)
import StaticFlags
import BasicTypes
import VarEnv
import UniqFM
import Util
import Outputable
\end{code}


%************************************************************************
%*									*
\subsection{Demands}
%*									*
%************************************************************************

\begin{code}
type DmdType   = DmdTypeP DataCon
type DmdResult = DmdResultP DataCon
type Demand    = DemandP DataCon
type Demands   = DemandPs DataCon

data DemandP con
  = Top			  -- T; used for unlifted types too, so that
			  --	A `lub` T = T
  | Abs			  -- A

  | Call (DemandP con)	  -- C(d)

  | Eval (DemandPs con)	  -- U(ds)

  | Defer (DemandPs con)  -- D(ds)

  | Box (DemandP con)     -- B(d)

  | Bot			  -- B
  deriving( Eq )
	-- Equality needed for fixpoints in DmdAnal

data DemandPs con
  = Poly (DemandP con)      -- Polymorphic case
  | Prod con [DemandP con]  -- "Product" case. Actually says that we demanded 
                            -- components of this *particular* DataCon
  deriving( Eq )

allTop :: Demands -> Bool
allTop (Poly d)    = isTop d
allTop (Prod _ ds) = all isTop ds

isTop :: Demand -> Bool
isTop Top = True
isTop _   = False 

isAbsent :: Demand -> Bool
isAbsent Abs = True
isAbsent _   = False 

mapDmds :: (Demand -> Demand) -> Demands -> Demands
mapDmds f (Poly d)     = Poly (f d)
mapDmds f (Prod dc ds) = Prod dc (map f ds)

zipWithDmds :: (Demand -> Demand -> Demand)
	    -> Demands -> Demands -> Demands
zipWithDmds f (Poly d1)  (Poly d2)      = Poly (d1 `f` d2)
zipWithDmds f (Prod dc1 ds1) (Poly d2)  = Prod dc1 [d1 `f` d2 | d1 <- ds1]
zipWithDmds f (Poly d1)  (Prod dc2 ds2) = Prod dc2 [d1 `f` d2 | d2 <- ds2]
zipWithDmds f (Prod dc1 ds1) (Prod dc2 ds2) 
  | dc1 == dc2
  , length ds1 == length ds2 = Prod dc1 (zipWithEqual "zipWithDmds" f ds1 ds2)
  | otherwise		     = Poly topDmd
	-- This really can happen with polymorphism
	-- \f. case f x of (a,b) -> ...
	--     case f y of (a,b,c) -> ...
	-- Here the two demands on f are C(LL) and C(LLL)!

topDmd, lazyDmd, seqDmd, evalDmd, errDmd :: Demand
topDmd  = Top			-- The most uninformative demand
lazyDmd = Box Abs
seqDmd  = Eval (Poly Abs)	-- Polymorphic seq demand
evalDmd = Box seqDmd		-- Evaluate and return
errDmd  = Box Bot		-- This used to be called X

isStrictDmd :: Demand -> Bool
isStrictDmd Bot      = True
isStrictDmd (Eval _) = True
isStrictDmd (Call _) = True
isStrictDmd (Box d)  = isStrictDmd d
isStrictDmd _        = False

seqDemand :: Demand -> ()
seqDemand (Call d)   = seqDemand d
seqDemand (Eval ds)  = seqDemands ds
seqDemand (Defer ds) = seqDemands ds
seqDemand (Box d)    = seqDemand d
seqDemand _          = ()

seqDemands :: Demands -> ()
seqDemands (Poly d)     = seqDemand d
seqDemands (Prod dc ds) = dc `seq` seqDemandList ds

seqDemandList :: [Demand] -> ()
seqDemandList [] = ()
seqDemandList (d:ds) = seqDemand d `seq` seqDemandList ds

instance Outputable con => Outputable (DemandP con) where
    ppr Top  = char 'T'
    ppr Abs  = char 'A'
    ppr Bot  = char 'B'

    ppr (Defer ds)      = char 'D' <> ppr ds
    ppr (Eval ds)       = char 'U' <> ppr ds
				      
    ppr (Box (Eval ds)) = char 'S' <> ppr ds
    ppr (Box Abs)	= char 'L'
    ppr (Box Bot)	= char 'X'
    ppr d@(Box _)	= pprPanic "ppr: Bad boxed demand" (ppr d)

    ppr (Call d)	= char 'C' <> parens (ppr d)


instance Outputable con => Outputable (DemandPs con) where
    ppr (Poly Abs)   = empty
    ppr (Poly d)     = parens (ppr d <> char '*')
    ppr (Prod _ ds)  = parens (hcat (map ppr ds))
	-- At one time I printed U(AAA) as U, but that
	-- confuses (Poly Abs) with (Prod AAA), and the
	-- worker/wrapper generation differs slightly for these two
	-- [Reason: in the latter case we can avoid passing the arg;
	--  see notes with WwLib.mkWWstr_one.]
\end{code}


%************************************************************************
%*									*
\subsection{Demand types}
%*									*
%************************************************************************

\begin{code}
data DmdTypeP con 
  = DmdType 
	DmdEnv	-- Demand on explicitly-mentioned 
		-- free variables
	[DemandP con]	  -- Demand on arguments
	(DmdResultP con)  -- Nature of result

	-- 		IMPORTANT INVARIANT
	-- The default demand on free variables not in the DmdEnv is:
	-- DmdResult = BotRes        <=>  Bot
	-- DmdResult = TopRes/ResCPR <=>  Abs

	-- 		ANOTHER IMPORTANT INVARIANT
	-- The Demands in the argument list are never
	--	Bot, Defer d
	-- Handwavey reason: these don't correspond to calling conventions
	-- See DmdAnal.funArgDemand for details


-- This guy lets us switch off CPR analysis
-- by making sure that everything uses TopRes instead of RetCPR
-- Assuming, of course, that they don't mention RetCPR by name.
-- They should only use retCPR
retCPR :: DataCon -> DmdResult
retCPR dc | opt_CprOff = TopRes
          | otherwise  = RetCPR dc

seqDmdType :: DmdType -> ()
seqDmdType (DmdType _env ds res) = 
  {- ??? env `seq` -} seqDemandList ds `seq` res `seq` ()

type DmdEnv = VarEnv Demand

data DmdResultP con 
  = TopRes      -- Nothing known	

  | RetCPR con  -- Returns constructed data, built with dc.
  	        -- Because we record the actual constructor that we
	        -- construct, we can actually optimise sum-types as
	        -- well, as long as the function only returns one of
	        -- the possible constructors

  | BotRes      -- Diverges or errors
  deriving( Eq, Show )
	-- Equality for fixpoints
	-- Show needed for Show in Lex.Token (sigh)

-- Equality needed for fixpoints in DmdAnal
instance Eq DmdType where
  (==) (DmdType fv1 ds1 res1)
       (DmdType fv2 ds2 res2) =  ufmToList fv1 == ufmToList fv2
			      && ds1 == ds2 && res1 == res2

instance Outputable con => Outputable (DmdTypeP con) where
  ppr dmd_ty = text "DmdType" <+> pprDmdType dmd_ty
	    
pprDmdType :: Outputable con => DmdTypeP con -> SDoc
pprDmdType (DmdType fv ds res) 
    = hsep [hcat (map ppr ds) <> ppr res,
	    if null fv_elts then empty
	    else braces (fsep (map pp_elt fv_elts))]
    where
      pp_elt (uniq, dmd) = ppr uniq <> text "->" <> ppr dmd
      fv_elts = ufmToList fv

instance Outputable con => Outputable (DmdResultP con) where
  ppr TopRes      = empty	       -- Keep these distinct from Demand letters
  ppr (RetCPR dc) = brackets (ppr dc)  -- so that we can print strictness sigs as
  ppr BotRes      = char 'b'           --    dddr
	                               -- without ambiguity

emptyDmdEnv :: VarEnv Demand
emptyDmdEnv = emptyVarEnv

topDmdType, botDmdType :: DmdType
cprDmdType :: DataCon -> DmdType
topDmdType = DmdType emptyDmdEnv [] TopRes
botDmdType = DmdType emptyDmdEnv [] BotRes
cprDmdType dc = DmdType emptyVarEnv [] (retCPR dc)

isBotRes :: DmdResult -> Bool
isBotRes BotRes = True
isBotRes _      = False

resTypeArgDmd :: DmdResult -> Demand
-- TopRes and BotRes are polymorphic, so that
--	BotRes = Bot -> BotRes
--	TopRes = Top -> TopRes
-- This function makes that concrete
-- We can get a RetCPR, because of the way in which we are (now)
-- giving CPR info to strict arguments.  On the first pass, when
-- nothing has demand info, we optimistically give CPR info or RetCPR to all args
resTypeArgDmd TopRes     = Top
resTypeArgDmd (RetCPR _) = Top
resTypeArgDmd BotRes     = Bot

returnsCPR :: DmdResult -> Bool
returnsCPR (RetCPR _) = True
returnsCPR _          = False

mkDmdType :: DmdEnv -> [Demand] -> DmdResult -> DmdType
mkDmdType fv ds res = DmdType fv ds res

mkTopDmdType :: [Demand] -> DmdResult -> DmdType
mkTopDmdType ds res = DmdType emptyDmdEnv ds res

dmdTypeDepth :: DmdType -> Arity
dmdTypeDepth (DmdType _ ds _) = length ds
\end{code}


%************************************************************************
%*									*
\subsection{Strictness signature
%*									*
%************************************************************************

In a let-bound Id we record its strictness info.  
In principle, this strictness info is a demand transformer, mapping
a demand on the Id into a DmdType, which gives
	a) the free vars of the Id's value
	b) the Id's arguments
	c) an indication of the result of applying 
	   the Id to its arguments

However, in fact we store in the Id an extremely emascuated demand transfomer,
namely 
		a single DmdType
(Nevertheless we dignify StrictSig as a distinct type.)

This DmdType gives the demands unleashed by the Id when it is applied
to as many arguments as are given in by the arg demands in the DmdType.

For example, the demand transformer described by the DmdType
		DmdType {x -> U(LL)} [V,A] Top
says that when the function is applied to two arguments, it
unleashes demand U(LL) on the free var x, V on the first arg,
and A on the second.  

If this same function is applied to one arg, all we can say is
that it uses x with U*(LL), and its arg with demand L.

\begin{code}
newtype StrictSig = StrictSig DmdType
		  deriving( Eq )

instance Outputable StrictSig where
   ppr = pprStrictSig

instance Show StrictSig where
   show (StrictSig ty) = showSDoc (ppr ty)

pprStrictSig :: StrictSig -> SDoc
pprStrictSig (StrictSig dmd_ty) = pprDmdType dmd_ty

mkStrictSig :: DmdType -> StrictSig
mkStrictSig dmd_ty = StrictSig dmd_ty

splitStrictSig :: StrictSig -> ([Demand], DmdResult)
splitStrictSig (StrictSig (DmdType _ dmds res)) = (dmds, res)

increaseStrictSigArity :: Int -> StrictSig -> StrictSig
-- Add extra arguments to a strictness signature
increaseStrictSigArity arity_increase (StrictSig (DmdType env dmds res))
  = StrictSig (DmdType env (replicate arity_increase topDmd ++ dmds) res)

isTopTopSig :: StrictSig -> Bool
-- Only used on top-level signatures, hence the assert
isTopTopSig (StrictSig (DmdType env [] TopRes)) = ASSERT( isEmptyVarEnv env) True	
isTopTopSig _                       = False

isTopSig :: StrictSig -> Bool
-- Can be used on any signature, nested or not
isTopSig (StrictSig (DmdType env [] TopRes)) = isEmptyVarEnv env
isTopSig _                                   = False


topSig, botSig :: StrictSig
cprSig :: DataCon -> StrictSig
topSig = StrictSig topDmdType
botSig = StrictSig botDmdType
cprSig dc = StrictSig (cprDmdType dc)
	

-- appIsBottom returns true if an application to n args would diverge
appIsBottom :: StrictSig -> Int -> Bool
appIsBottom (StrictSig (DmdType _ ds BotRes)) n = listLengthCmp ds n /= GT
appIsBottom _				      _ = False

isBottomingSig :: StrictSig -> Bool
isBottomingSig (StrictSig (DmdType _ _ BotRes)) = True
isBottomingSig _				= False

seqStrictSig :: StrictSig -> ()
seqStrictSig (StrictSig ty) = seqDmdType ty
\end{code}
    

