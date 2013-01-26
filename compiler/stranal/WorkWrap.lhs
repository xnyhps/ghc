%
% (c) The GRASP/AQUA Project, Glasgow University, 1993-1998
%
\section[WorkWrap]{Worker/wrapper-generating back-end of strictness analyser}

\begin{code}
{-# OPTIONS -fno-warn-tabs #-}
-- The above warning supression flag is a temporary kludge.
-- While working on this module you are encouraged to remove it and
-- detab the module (please do the detabbing in a separate patch). See
--     http://hackage.haskell.org/trac/ghc/wiki/Commentary/CodingStyle#TabsvsSpaces
-- for details

module WorkWrap ( wwTopBinds, mkWrapper ) where

import CoreSyn
import CoreUnfold	( certainlyWillInline, mkInlineUnfolding, mkWwInlineRule )
import CoreUtils	( exprType, exprIsHNF )
import CoreArity	( exprArity )
import Var
import Id
import Type		( Type )
import IdInfo
import UniqSupply
import BasicTypes
import DynFlags
import VarEnv		( isEmptyVarEnv )
import Demand
import WwLib
import Util
import Outputable
import MonadUtils

#include "HsVersions.h"
\end{code}

We take Core bindings whose binders have:

\begin{enumerate}

\item Strictness attached (by the front-end of the strictness
analyser), and / or

\item Constructed Product Result information attached by the CPR
analysis pass.

\end{enumerate}

and we return some ``plain'' bindings which have been
worker/wrapper-ified, meaning: 

\begin{enumerate} 

\item Functions have been split into workers and wrappers where
appropriate.  If a function has both strictness and CPR properties
then only one worker/wrapper doing both transformations is produced;

\item Binders' @IdInfos@ have been updated to reflect the existence of
these workers/wrappers (this is where we get STRICTNESS and CPR pragma
info for exported values).
\end{enumerate}

\begin{code}
wwTopBinds :: DynFlags -> UniqSupply -> CoreProgram -> CoreProgram

wwTopBinds dflags us top_binds
  = initUs_ us $ do
    top_binds' <- mapM (wwBind dflags) top_binds
    return (concat top_binds')
\end{code}

%************************************************************************
%*									*
\subsection[wwBind-wwExpr]{@wwBind@ and @wwExpr@}
%*									*
%************************************************************************

@wwBind@ works on a binding, trying each \tr{(binder, expr)} pair in
turn.  Non-recursive case first, then recursive...

\begin{code}
wwBind  :: DynFlags
        -> CoreBind
	-> UniqSM [CoreBind]	-- returns a WwBinding intermediate form;
				-- the caller will convert to Expr/Binding,
				-- as appropriate.

wwBind dflags (NonRec binder rhs) = do
    new_rhs <- wwExpr dflags rhs
    new_pairs <- tryWW dflags NonRecursive binder new_rhs
    return [NonRec b e | (b,e) <- new_pairs]
      -- Generated bindings must be non-recursive
      -- because the original binding was.

wwBind dflags (Rec pairs)
  = return . Rec <$> concatMapM do_one pairs
  where
    do_one (binder, rhs) = do new_rhs <- wwExpr dflags rhs
                              tryWW dflags Recursive binder new_rhs
\end{code}

@wwExpr@ basically just walks the tree, looking for appropriate
annotations that can be used. Remember it is @wwBind@ that does the
matching by looking for strict arguments of the correct type.
@wwExpr@ is a version that just returns the ``Plain'' Tree.

\begin{code}
wwExpr :: DynFlags -> CoreExpr -> UniqSM CoreExpr

wwExpr _      e@(Type {}) = return e
wwExpr _      e@(Coercion {}) = return e
wwExpr _      e@(Lit  {}) = return e
wwExpr _      e@(Var  {}) = return e

wwExpr dflags (Lam binder expr)
  = Lam binder <$> wwExpr dflags expr

wwExpr dflags (App f a)
  = App <$> wwExpr dflags f <*> wwExpr dflags a

wwExpr dflags (Tick note expr)
  = Tick note <$> wwExpr dflags expr

wwExpr dflags (Cast expr co) = do
    new_expr <- wwExpr dflags expr
    return (Cast new_expr co)

wwExpr dflags (Let bind expr)
  = mkLets <$> wwBind dflags bind <*> wwExpr dflags expr

wwExpr dflags (Case expr binder ty alts) = do
    new_expr <- wwExpr dflags expr
    new_alts <- mapM ww_alt alts
    return (Case new_expr binder ty new_alts)
  where
    ww_alt (con, binders, rhs) = do
        new_rhs <- wwExpr dflags rhs
        return (con, binders, new_rhs)
\end{code}

%************************************************************************
%*									*
\subsection[tryWW]{@tryWW@: attempt a worker/wrapper pair}
%*									*
%************************************************************************

@tryWW@ just accumulates arguments, converts strictness info from the
front-end into the proper form, then calls @mkWwBodies@ to do
the business.

The only reason this is monadised is for the unique supply.

Note [Don't w/w INLINE things]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
It's very important to refrain from w/w-ing an INLINE function (ie one
with an InlineRule) because the wrapper will then overwrite the
InlineRule unfolding.

Furthermore, if the programmer has marked something as INLINE, 
we may lose by w/w'ing it.

If the strictness analyser is run twice, this test also prevents
wrappers (which are INLINEd) from being re-done.  (You can end up with
several liked-named Ids bouncing around at the same time---absolute
mischief.)  

Notice that we refrain from w/w'ing an INLINE function even if it is
in a recursive group.  It might not be the loop breaker.  (We could
test for loop-breaker-hood, but I'm not sure that ever matters.)

Note [Don't w/w INLINABLE things]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
If we have
  {-# INLINABLE f #-}
  f x y = ....
then in principle we might get a more efficient loop by w/w'ing f.
But that would make a new unfolding which would overwrite the old
one.  So we leave INLINABLE things alone too.

This is a slight infelicity really, because it means that adding
an INLINABLE pragma could make a program a bit less efficient,
because you lose the worker/wrapper stuff.  But I don't see a way 
to avoid that.

Note [Don't w/w inline small non-loop-breaker things]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
In general, we refrain from w/w-ing *small* functions, which are not
loop breakers, because they'll inline anyway.  But we must take care:
it may look small now, but get to be big later after other inlining
has happened.  So we take the precaution of adding an INLINE pragma to
any such functions.

I made this change when I observed a big function at the end of
compilation with a useful strictness signature but no w-w.  (It was
small during demand analysis, we refrained from w/w, and then got big
when something was inlined in its rhs.) When I measured it on nofib,
it didn't make much difference; just a few percent improved allocation
on one benchmark (bspt/Euclid.space).  But nothing got worse.

There is an infelicity though.  We may get something like
      f = g val
==>
      g x = case gw x of r -> I# r

      f {- InlineStable, Template = g val -}
      f = case gw x of r -> I# r

The code for f duplicates that for g, without any real benefit. It
won't really be executed, because calls to f will go via the inlining.

Note [Wrapper activation]
~~~~~~~~~~~~~~~~~~~~~~~~~
When should the wrapper inlining be active?  It must not be active
earlier than the current Activation of the Id (eg it might have a
NOINLINE pragma).  But in fact strictness analysis happens fairly
late in the pipeline, and we want to prioritise specialisations over
strictness.  Eg if we have 
  module Foo where
    f :: Num a => a -> Int -> a
    f n 0 = n  	       	   -- Strict in the Int, hence wrapper
    f n x = f (n+n) (x-1)

    g :: Int -> Int
    g x = f x x		   -- Provokes a specialisation for f

  module Bsr where
    import Foo

    h :: Int -> Int
    h x = f 3 x

Then we want the specialisation for 'f' to kick in before the wrapper does.

Now in fact the 'gentle' simplification pass encourages this, by
having rules on, but inlinings off.  But that's kind of lucky. It seems 
more robust to give the wrapper an Activation of (ActiveAfter 0),
so that it becomes active in an importing module at the same time that
it appears in the first place in the defining module.

\begin{code}
tryWW   :: DynFlags
        -> RecFlag
	-> Id				-- The fn binder
	-> CoreExpr			-- The bound rhs; its innards
					--   are already ww'd
	-> UniqSM [(Id, CoreExpr)]	-- either *one* or *two* pairs;
					-- if one, then no worker (only
					-- the orig "wrapper" lives on);
					-- if two, then a worker and a
					-- wrapper.
tryWW dflags is_rec fn_id rhs
  | isNeverActive inline_act
	-- No point in worker/wrappering if the thing is never inlined!
	-- Because the no-inline prag will prevent the wrapper ever
	-- being inlined at a call site. 
	-- 
	-- Furthermore, don't even expose strictness info
  = return [ (fn_id, rhs) ]

  | is_thunk && worthSplittingThunk fn_dmd res_info
  	-- See Note [Thunk splitting]
  = ASSERT2( isNonRec is_rec, ppr new_fn_id )	-- The thunk must be non-recursive
    checkSize dflags new_fn_id rhs $ 
    splitThunk dflags new_fn_id rhs

  | is_fun && worthSplittingFun wrap_dmds res_info
  = checkSize dflags new_fn_id rhs $
    splitFun dflags new_fn_id fn_info wrap_dmds res_info rhs

  | otherwise
  = return [ (new_fn_id, rhs) ]

  where
    fn_info   	 = idInfo fn_id
    fn_dmd       = demandInfo fn_info
    inline_act   = inlinePragmaActivation (inlinePragInfo fn_info)

	-- In practice it always will have a strictness 
	-- signature, even if it's a uninformative one
    strict_sig  = strictnessInfo fn_info
    StrictSig (DmdType env wrap_dmds res_info) = strict_sig

	-- new_fn_id has the DmdEnv zapped.  
	--	(a) it is never used again
	--	(b) it wastes space
	--	(c) it becomes incorrect as things are cloned, because
	--	    we don't push the substitution into it
    new_fn_id | isEmptyVarEnv env = fn_id
	      | otherwise	  = fn_id `setIdStrictness` 
				     StrictSig (mkTopDmdType wrap_dmds res_info)

    is_fun    = notNull wrap_dmds
    is_thunk  = not is_fun && not (exprIsHNF rhs)

---------------------
checkSize :: DynFlags -> Id -> CoreExpr
	  -> UniqSM [(Id,CoreExpr)] -> UniqSM [(Id,CoreExpr)]
checkSize dflags fn_id rhs thing_inside
  | isStableUnfolding (realIdUnfolding fn_id)
  = return [ (fn_id, rhs) ]
      -- See Note [Don't w/w INLINE things]
      -- and Note [Don't w/w INLINABLE things]
      -- NB: use realIdUnfolding because we want to see the unfolding
      --     even if it's a loop breaker!

  | certainlyWillInline dflags (idUnfolding fn_id)
  = return [ (fn_id `setIdUnfolding` inline_rule, rhs) ]
	-- Note [Don't w/w inline small non-loop-breaker things]
	-- NB: use idUnfolding because we don't want to apply
	--     this criterion to a loop breaker!

  | otherwise = thing_inside
  where
    inline_rule = mkInlineUnfolding Nothing rhs

---------------------
splitFun :: DynFlags -> Id -> IdInfo -> [Demand] -> DmdResult -> Expr Var
         -> UniqSM [(Id, CoreExpr)]
splitFun dflags fn_id fn_info wrap_dmds res_info rhs
  = WARN( not (wrap_dmds `lengthIs` arity), ppr fn_id <+> (ppr arity $$ ppr wrap_dmds $$ ppr res_info) ) 
    (do {
	-- The arity should match the signature
      (work_demands, wrap_fn, work_fn) <- mkWwBodies dflags fun_ty wrap_dmds res_info one_shots
    ; work_uniq <- getUniqueM
    ; let
	work_rhs = work_fn rhs
	work_id  = mkWorkerId work_uniq fn_id (exprType work_rhs) 
		        `setIdOccInfo` occInfo fn_info
				-- Copy over occurrence info from parent
				-- Notably whether it's a loop breaker
				-- Doesn't matter much, since we will simplify next, but
				-- seems right-er to do so

			`setInlineActivation` (inlinePragmaActivation inl_prag)
				-- Any inline activation (which sets when inlining is active) 
				-- on the original function is duplicated on the worker
				-- It *matters* that the pragma stays on the wrapper
				-- It seems sensible to have it on the worker too, although we
				-- can't think of a compelling reason. (In ptic, INLINE things are 
				-- not w/wd). However, the RuleMatchInfo is not transferred since
                                -- it does not make sense for workers to be constructorlike.

			`setIdStrictness` StrictSig (mkTopDmdType work_demands work_res_info)
				-- Even though we may not be at top level, 
				-- it's ok to give it an empty DmdEnv

                        `setIdArity` (exprArity work_rhs)
                                -- Set the arity so that the Core Lint check that the 
                                -- arity is consistent with the demand type goes through

	wrap_rhs  = wrap_fn work_id
	wrap_prag = InlinePragma { inl_inline = Inline
                                 , inl_sat    = Nothing
                                 , inl_act    = ActiveAfter 0
                                 , inl_rule   = rule_match_info }
		-- See Note [Wrapper activation]
		-- The RuleMatchInfo is (and must be) unaffected
		-- The inl_inline is bound to be False, else we would not be
		--    making a wrapper

	wrap_id   = fn_id `setIdUnfolding` mkWwInlineRule work_id wrap_rhs arity
			  `setInlinePragma` wrap_prag
		          `setIdOccInfo` NoOccInfo
			        -- Zap any loop-breaker-ness, to avoid bleating from Lint
				-- about a loop breaker with an INLINE rule

    ; return ([(work_id, work_rhs), (wrap_id, wrap_rhs)]) })
	-- Worker first, because wrapper mentions it
	-- mkWwBodies has already built a wrap_rhs with an INLINE pragma wrapped around it
  where
    fun_ty          = idType fn_id
    inl_prag        = inlinePragInfo fn_info
    rule_match_info = inlinePragmaRuleMatchInfo inl_prag
    arity           = arityInfo fn_info	
    		    -- The arity is set by the simplifier using exprEtaExpandArity
		    -- So it may be more than the number of top-level-visible lambdas

    work_res_info | isBotRes res_info = botRes	-- Cpr stuff done by wrapper
		  | otherwise	      = topRes

    one_shots = get_one_shots rhs

-- If the original function has one-shot arguments, it is important to
-- make the wrapper and worker have corresponding one-shot arguments too.
-- Otherwise we spuriously float stuff out of case-expression join points,
-- which is very annoying.
get_one_shots :: Expr Var -> [Bool]
get_one_shots (Lam b e)
  | isId b    = isOneShotLambda b : get_one_shots e
  | otherwise = get_one_shots e
get_one_shots (Tick _ e) = get_one_shots e
get_one_shots _    	 = noOneShotInfo
\end{code}

Note [Thunk splitting]
~~~~~~~~~~~~~~~~~~~~~~
Suppose x is used strictly (never mind whether it has the CPR
property).  

      let
	x* = x-rhs
      in body

splitThunk transforms like this:

      let
	x* = case x-rhs of { I# a -> I# a }
      in body

Now simplifier will transform to

      case x-rhs of 
	I# a ->	let x* = I# a 
	        in body

which is what we want. Now suppose x-rhs is itself a case:

	x-rhs = case e of { T -> I# a; F -> I# b }

The join point will abstract over a, rather than over (which is
what would have happened before) which is fine.

Notice that x certainly has the CPR property now!

In fact, splitThunk uses the function argument w/w splitting 
function, so that if x's demand is deeper (say U(U(L,L),L))
then the splitting will go deeper too.

\begin{code}
-- See Note [Thunk splitting]
-- splitThunk converts the *non-recursive* binding
--	x = e
-- into
--	x = let x = e
--	    in case x of 
--		 I# y -> let x = I# y in x }
-- See comments above. Is it not beautifully short?
-- Moreover, it works just as well when there are
-- several binders, and if the binders are lifted
-- E.g.     x = e
--     -->  x = let x = e in
--              case x of (a,b) -> let x = (a,b)  in x

splitThunk :: DynFlags -> Var -> Expr Var -> UniqSM [(Var, Expr Var)]
splitThunk dflags fn_id rhs = do
    (_, wrap_fn, work_fn) <- mkWWstr dflags [fn_id]
    return [ (fn_id, Let (NonRec fn_id rhs) (wrap_fn (work_fn (Var fn_id)))) ]
\end{code}


%************************************************************************
%*									*
\subsection{The worker wrapper core}
%*									*
%************************************************************************

@mkWrapper@ is called when importing a function.  We have the type of 
the function and the name of its worker, and we want to make its body (the wrapper).

\begin{code}
mkWrapper :: DynFlags
          -> Type		-- Wrapper type
	  -> StrictSig		-- Wrapper strictness info
	  -> UniqSM (Id -> CoreExpr)	-- Wrapper body, missing worker Id

mkWrapper dflags fun_ty (StrictSig (DmdType _ demands res_info)) = do
    (_, wrap_fn, _) <- mkWwBodies dflags fun_ty demands res_info noOneShotInfo
    return wrap_fn

noOneShotInfo :: [Bool]
noOneShotInfo = repeat False
\end{code}
