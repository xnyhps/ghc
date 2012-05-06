module TcTypeNatsRules where

-- From other GHC locations
import Name     ( Name )
import Var      ( Var, EvVar )
import TyCon    ( TyCon, tyConName )
import Coercion ( TypeNatCoAxiom (..) )
import Type     ( isNumLitTy, getTyVar_maybe )
import PrelNames( typeNatLeqTyFamName
                , typeNatAddTyFamName
                , typeNatMulTyFamName
                , typeNatExpTyFamName
                )
import Panic    ( panic )

-- From type checker
import TcRnTypes      ( Xi, Ct(..), ctId )
import TcTypeNatsEval ( minus, divide, logExact, rootExact )

-- From base libraries
import Data.Maybe ( fromMaybe, maybeToList )
import Data.List  ( nub, sort )
import qualified Data.IntMap as IMap
import Control.Monad ( msum )


type TVar   = Int           -- ^ Names a term
type PVar   = Int           -- ^ Names a proof

data Term   = Var  !TVar    -- ^ Matches anything
            | Num  !Integer -- ^ Matches the given number constant
            | Bool !Bool    -- ^ Matches the given boolean constant
            | Con  !Var     -- ^ Matches a GHC variable (uninterpreted constant)
              deriving Eq

-- For functions, the result comes first:
-- For example `x ~ a + b` or `Prop Add [x,a,b]`
data Prop   = Prop Op [Term]
data Op     = Leq | Add | Mul | Exp

data Rule   = Rule [(PVar,Prop)]    -- ^ Named assumptions of the rule
                   Conc             -- ^ Conclusion of the rule
                   Proof            -- ^ Proof of conclusion (uses assumptions)

data Conc   = CProp Prop
            | CEq Term Term

data Proof  = By TypeNatCoAxiom [Term] [ Proof ]
            | Proved EvVar
            | Assumed PVar


--------------------------------------------------------------------------------
fromXi :: Xi -> Maybe Term
fromXi t = msum [ Con `fmap` getTyVar_maybe t, Num `fmap` isNumLitTy t ]

opName :: Op -> Name
opName Leq = typeNatLeqTyFamName
opName Add = typeNatAddTyFamName
opName Mul = typeNatMulTyFamName
opName Exp = typeNatExpTyFamName

opAxiom :: Op -> Integer -> Integer -> TypeNatCoAxiom
opAxiom Leq = TnLeqDef
opAxiom Add = TnAddDef
opAxiom Mul = TnMulDef
opAxiom Exp = TnExpDef
--------------------------------------------------------------------------------



--------------------------------------------------------------------------------

-- XXX: We should be able to also cope with rules that have only Leq constraints
simpleRules :: [Rule]
simpleRules = map (uncurry simpleRule)
  [ (TnLeq0    , Prop Leq [ t, o, a ])
  , (TnLeqRefl , Prop Leq [ t, a, a ])

  , (TnAdd0L   , Prop Add [ a, o, a ])
  , (TnAdd0R   , Prop Add [ a, a, o ])

  , (TnMul0L   , Prop Mul [ o, o, a ])
  , (TnMul0R   , Prop Mul [ o, a, o ])
  , (TnMul1L   , Prop Mul [ a, i, a ])
  , (TnMul1R   , Prop Mul [ a, a, i ])

  -- TnExp0L
  , (TnExp0R   , Prop Exp [ i, a, o ])
  , (TnExp1L   , Prop Exp [ i, i, a ])
  , (TnExp1R   , Prop Exp [ a, a, i ])
  ]
  where a = Var 0
        t = Bool True
        o = Num 0
        i = Num 1





-- | A smart constructor for easier rule constrction.
rule :: TypeNatCoAxiom -> [Prop] -> Conc -> Rule
rule ax asmps conc
  | wellFormed = Rule as conc $ By ax (map Var vs) $ map (Assumed . fst) as
  | otherwise  = panic "Malformed rule."
  where
  as                    = zip [ 0 .. ] asmps
  vs                    = sort $ nub $ concatMap propVars asmps

  wellFormed            = all (`elem` vs) (concVars conc)

  concVars (CProp p)    = propVars p
  concVars (CEq s t)    = termVars s ++ termVars t

  propVars (Prop _ ts)  = concatMap termVars ts

  termVars (Var x)      = [x]
  termVars (Con _)      = panic "Unineterpreted constant in rule."
  termVars (Num _)      = []
  termVars (Bool _)     = []

simpleRule :: TypeNatCoAxiom -> Prop -> Rule
simpleRule ax p = rule ax [] (CProp p)
--------------------------------------------------------------------------------



--------------------------------------------------------------------------------
matchTermXi :: Term -> Xi -> Maybe Subst
matchTermXi term xi = matchTermTerm term =<< fromXi xi

matchTermTerm :: Term -> Term -> Maybe Subst
matchTermTerm t1 t2 | t1 == t2  = return IMap.empty
matchTermTerm (Var a) t         = return (IMap.singleton a t)
matchTermTerm t (Var a)         = return (IMap.singleton a t)
matchTermTerm _ _               = panic "matchTermTerm: unreachable"

matchTerms :: [Term] -> [Xi] -> Maybe Subst
matchTerms [] [] = return IMap.empty
matchTerms (t : ts) (xi : xis) =
  do su1 <- matchTermXi t xi
     su2 <- matchTerms (apSubst su1 ts) xis
     return (IMap.union su1 su2)
matchTerms _ _ = Nothing


--------------------------------------------------------------------------------


-- | Try to satisfy a rule assumption with an existing constraint.
byAsmp :: Prop -> Ct -> Maybe (Subst, Proof)
byAsmp (Prop op ts) ct
  | tyConName (cc_fun ct) == opName op =
      do su <- matchTerms ts (cc_rhs ct : cc_tyargs ct)
         return (su, Proved (ctId ct))
byAsmp _ _ = Nothing


-- | Try to stisfy a rule assumption with an axiom.
byAxiom :: Prop -> Maybe (Subst, Proof)

byAxiom (Prop op [r, Num a, Num b]) =
  do su <- matchTermTerm r $
           case op of
             Add -> Num (a + b)
             Mul -> Num (a * b)
             Exp -> Num (a ^ b)
             Leq -> Bool (a <= b)

     return (su, By (opAxiom op a b) [] [])

byAxiom (Prop op [Num r, a, Num b]) =
  do na <- case op of
             Add -> minus r b
             Mul -> divide r b
             Exp -> rootExact r b
             Leq -> Nothing

     su <- matchTermTerm a (Num na)
     return (su, By (opAxiom op na b) [] [])

byAxiom (Prop op [Num r, Num a, b]) =
  do nb <- case op of
             Add -> minus r a
             Mul -> divide r a
             Exp -> logExact r a
             Leq -> Nothing

     su <- matchTermTerm b (Num nb)
     return (su, By (opAxiom op a nb) [] [])

byAxiom _ = Nothing



-- XXX: By simple rule

{-
matchAxiom (Prop Add [r, Num 0, b]) = matchTermTerm r b
matchAxiom (Prop Add [r, a, Num 0]) = matchTermTerm r a

matchAxiom (Prop Mul [r, Num 0, _]) = matchTermTerm r $ Num 0
matchAxiom (Prop Mul [r, _, Num 0]) = matchTermTerm r $ Num 0
matchAxiom (Prop Mul [r, Num 1, b]) = matchTermTerm r b
matchAxiom (Prop Mul [r, a, Num 1]) = matchTermTerm r a



-- (only if 1 <= b)
-- matchAxiom (Prop Exp [r, Num 0, b]) = matchTermTerm r $ Num 0

matchAxiom (Prop Exp [r, _, Num 0]) = matchTermTerm r $ Num 1
matchAxiom (Prop Exp [r, Num 1, _]) = matchTermTerm r $ Num 1
matchAxiom (Prop Exp [r, a, Num 1]) = matchTermTerm r a
-}


specRule :: Rule -> (Prop -> Maybe (Subst, Proof)) -> [Rule]
specRule (Rule as c proof) tactic =
  do ((n,p), rest) <- choose as
     (su, aP) <- maybeToList (tactic p)
     return $ apSubst su $ Rule rest c $ define n aP proof




--------------------------------------------------------------------------------
type Subst  = IMap.IntMap Term  -- ^ Maps TVars to Terms

class ApSubst t where
  apSubst :: Subst -> t -> t

instance ApSubst t => ApSubst [t] where
  apSubst su ts             = map (apSubst su) ts

instance ApSubst Term where
  apSubst su term           = case term of
                                Var a -> fromMaybe term (IMap.lookup a su)
                                _     -> term

instance ApSubst Prop where
  apSubst su (Prop op ts)   = Prop op (apSubst su ts)

instance ApSubst Conc where
  apSubst su (CProp p)      = CProp (apSubst su p)
  apSubst su (CEq t1 t2)    = CEq (apSubst su t1) (apSubst su t2)

instance ApSubst Rule where
  apSubst su (Rule as c p)  = Rule [ (n, apSubst su a) | (n,a) <- as ]
                                   (apSubst su c) (apSubst su p)

instance ApSubst Proof where
  apSubst su (By ax ts ps)  = By ax (apSubst su ts) (apSubst su ps)
  apSubst _ (Proved v)      = Proved v
  apSubst _ (Assumed n)     = Assumed n


-- | Define an assumption paramater in the proof of a rule.
define :: PVar -> Proof -> Proof -> Proof
define n p (Assumed m) | n == m   = p
define n p (By ax ts ps)          = By ax ts (map (define n p) ps)
define _ _ p                      = p


-- Consider each element of the list (and the rest)
choose :: [a] -> [(a,[a])]
choose []       = []
choose (a : as) = (a, as) : [ (b, a : bs) | (b,bs) <- choose as ]



