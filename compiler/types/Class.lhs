%
% (c) The University of Glasgow 2006
% (c) The GRASP/AQUA Project, Glasgow University, 1992-1998
%

The @Class@ datatype

\begin{code}
{-# OPTIONS -fno-warn-tabs #-}
-- The above warning supression flag is a temporary kludge.
-- While working on this module you are encouraged to remove it and
-- detab the module (please do the detabbing in a separate patch). See
--     http://hackage.haskell.org/trac/ghc/wiki/Commentary/CodingStyle#TabsvsSpaces
-- for details

module Class (
	Class,
        ClassOpItem, DefMeth (..),
        ClassATItem, ATDefault (..),
	defMethSpecOfDefMeth,

	FunDep,	pprFundeps, pprFunDep,

	mkClass, classTyVars, classArity, 
	classKey, className, classATs, classATItems, classTyCon, classMethods,
	classOpItems, classBigSig, classExtraBigSig, classTvsFds, classSCTheta,
        classAllSelIds, classSCSelId
    ) where

#include "Typeable.h"
#include "HsVersions.h"

import {-# SOURCE #-} TyCon	( TyCon, tyConName, tyConUnique )
import {-# SOURCE #-} TypeRep	( Type, PredType )

import Var
import Name
import BasicTypes
import Unique
import Util
import Outputable
import SrcLoc
import FastString

import Data.Typeable (Typeable)
import qualified Data.Data as Data
\end{code}

%************************************************************************
%*									*
\subsection[Class-basic]{@Class@: basic definition}
%*									*
%************************************************************************

A @Class@ corresponds to a Greek kappa in the static semantics:

\begin{code}
data Class
  = Class {
	classTyCon :: TyCon,	-- The data type constructor for
				-- dictionaries of this class
                                -- See Note [ATyCon for classes] in TypeRep

	className :: Name,              -- Just the cached name of the TyCon
	classKey  :: Unique,		-- Cached unique of TyCon
	
	classTyVars  :: [TyVar],	-- The class kind and type variables;
		     			-- identical to those of the TyCon

	classFunDeps :: [FunDep TyVar],	-- The functional dependencies

	-- Superclasses: eg: (F a ~ b, F b ~ G a, Eq a, Show b)
        -- We need value-level selectors for both the dictionary 
	-- superclasses and the equality superclasses
	classSCTheta :: [PredType],	-- Immediate superclasses, 
	classSCSels  :: [Id],		-- Selector functions to extract the
		     			--   superclasses from a 
					--   dictionary of this class
	-- Associated types
        classATStuff :: [ClassATItem],	-- Associated type families

        -- Class operations (methods, not superclasses)
	classOpStuff :: [ClassOpItem]	-- Ordered by tag
     }
  deriving Typeable

type FunDep a = ([a],[a])  --  e.g. class C a b c | a b -> c, a c -> b where...
			   --  Here fun-deps are [([a,b],[c]), ([a,c],[b])]

type ClassOpItem = (Id, DefMeth)
        -- Selector function; contains unfolding
	-- Default-method info

data DefMeth = NoDefMeth 		-- No default method
	     | DefMeth Name  		-- A polymorphic default method
	     | GenDefMeth Name 		-- A generic default method
             deriving Eq

type ClassATItem = (TyCon,           -- See Note [Associated type tyvar names]
                    [ATDefault])     -- Default associated types from these templates 
  -- We can have more than one default per type; see
  -- Note [Associated type defaults] in TcTyClsDecls

-- Each associated type default template is a quad of:
data ATDefault = ATD { -- TyVars of the RHS and family arguments 
                       -- (including, but perhaps more than, the class TVs)
                       atDefaultTys     :: [TyVar],
                       -- The instantiated family arguments
                       atDefaultPats    :: [Type],
                       -- The RHS of the synonym
                       atDefaultRhs     :: Type,
                       -- The source location of the synonym
                       atDefaultSrcSpan :: SrcSpan }

-- | Convert a `DefMethSpec` to a `DefMeth`, which discards the name field in
--   the `DefMeth` constructor of the `DefMeth`.
defMethSpecOfDefMeth :: DefMeth -> DefMethSpec
defMethSpecOfDefMeth meth
 = case meth of
	NoDefMeth	-> NoDM
	DefMeth _	-> VanillaDM
	GenDefMeth _	-> GenericDM

\end{code}

The @mkClass@ function fills in the indirect superclasses.

\begin{code}
mkClass :: [TyVar]
	-> [([TyVar], [TyVar])]
	-> [PredType] -> [Id]
	-> [ClassATItem]
	-> [ClassOpItem]
	-> TyCon
	-> Class

mkClass tyvars fds super_classes superdict_sels at_stuff
	op_stuff tycon
  = Class {	classKey     = tyConUnique tycon, 
		className    = tyConName tycon,
		classTyVars  = tyvars,
		classFunDeps = fds,
		classSCTheta = super_classes,
		classSCSels  = superdict_sels,
		classATStuff = at_stuff,
		classOpStuff = op_stuff,
		classTyCon   = tycon }
\end{code}

Note [Associated type tyvar names]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The TyCon of an associated type should use the same variable names as its
parent class. Thus
    class C a b where
      type F b x a :: *
We make F use the same Name for 'a' as C does, and similary 'b'.

The only reason for this is when checking instances it's easier to match 
them up, to ensure they match.  Eg
    instance C Int [d] where
      type F [d] x Int = ....
we should make sure that the first and third args match the instance
header.

This is the reason we use the Name and TyVar from the parent declaration,
in both class and instance decls: just to make this check easier.


%************************************************************************
%*									*
\subsection[Class-selectors]{@Class@: simple selectors}
%*									*
%************************************************************************

The rest of these functions are just simple selectors.

\begin{code}
classArity :: Class -> Arity
classArity clas = length (classTyVars clas)
	-- Could memoise this

classAllSelIds :: Class -> [Id]
-- Both superclass-dictionary and method selectors
classAllSelIds c@(Class {classSCSels = sc_sels})
  = sc_sels ++ classMethods c

classSCSelId :: Class -> Int -> Id
-- Get the n'th superclass selector Id
-- where n is 0-indexed, and counts 
--    *all* superclasses including equalities
classSCSelId (Class { classSCSels = sc_sels }) n
  = ASSERT( n >= 0 && n < length sc_sels )
    sc_sels !! n

classMethods :: Class -> [Id]
classMethods (Class {classOpStuff = op_stuff})
  = [op_sel | (op_sel, _) <- op_stuff]

classOpItems :: Class -> [ClassOpItem]
classOpItems = classOpStuff

classATs :: Class -> [TyCon]
classATs (Class { classATStuff = at_stuff })
  = [tc | (tc, _) <- at_stuff]

classATItems :: Class -> [ClassATItem]
classATItems = classATStuff

classTvsFds :: Class -> ([TyVar], [FunDep TyVar])
classTvsFds c
  = (classTyVars c, classFunDeps c)

classBigSig :: Class -> ([TyVar], [PredType], [Id], [ClassOpItem])
classBigSig (Class {classTyVars = tyvars, classSCTheta = sc_theta, 
	 	    classSCSels = sc_sels, classOpStuff = op_stuff})
  = (tyvars, sc_theta, sc_sels, op_stuff)

classExtraBigSig :: Class -> ([TyVar], [FunDep TyVar], [PredType], [Id], [ClassATItem], [ClassOpItem])
classExtraBigSig (Class {classTyVars = tyvars, classFunDeps = fundeps,
			 classSCTheta = sc_theta, classSCSels = sc_sels,
			 classATStuff = ats, classOpStuff = op_stuff})
  = (tyvars, fundeps, sc_theta, sc_sels, ats, op_stuff)
\end{code}


%************************************************************************
%*									*
\subsection[Class-instances]{Instance declarations for @Class@}
%*									*
%************************************************************************

We compare @Classes@ by their keys (which include @Uniques@).

\begin{code}
instance Eq Class where
    c1 == c2 = classKey c1 == classKey c2
    c1 /= c2 = classKey c1 /= classKey c2

instance Ord Class where
    c1 <= c2 = classKey c1 <= classKey c2
    c1 <  c2 = classKey c1 <  classKey c2
    c1 >= c2 = classKey c1 >= classKey c2
    c1 >  c2 = classKey c1 >  classKey c2
    compare c1 c2 = classKey c1 `compare` classKey c2
\end{code}

\begin{code}
instance Uniquable Class where
    getUnique c = classKey c

instance NamedThing Class where
    getName clas = className clas

instance Outputable Class where
    ppr c = ppr (getName c)

instance Outputable DefMeth where
    ppr (DefMeth n)    =  ptext (sLit "Default method") <+> ppr n
    ppr (GenDefMeth n) =  ptext (sLit "Generic default method") <+> ppr n
    ppr NoDefMeth      =  empty   -- No default method

pprFundeps :: Outputable a => [FunDep a] -> SDoc
pprFundeps []  = empty
pprFundeps fds = hsep (ptext (sLit "|") : punctuate comma (map pprFunDep fds))

pprFunDep :: Outputable a => FunDep a -> SDoc
pprFunDep (us, vs) = hsep [interppSP us, ptext (sLit "->"), interppSP vs]

instance Data.Data Class where
    -- don't traverse?
    toConstr _   = abstractConstr "Class"
    gunfold _ _  = error "gunfold"
    dataTypeOf _ = mkNoRepType "Class"
\end{code}
