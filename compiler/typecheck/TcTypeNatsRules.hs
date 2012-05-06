module TcTypeNatsRules where

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

import TcRnTypes      ( Xi, Ct(..), ctId )
import TcTypeNatsEval ( minus, divide, logExact, rootExact )

import Data.Maybe ( fromMaybe, maybeToList )
import Data.List  ( nub, sort )
import qualified Data.IntMap as IMap
import Control.Monad ( msum )

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


--------------------------------------------------------------------------------

type TVar   = Int               -- ^ Names a term
type PVar   = Int               -- ^ Names a proof

data Term   = Var  !TVar    -- ^ Matches anything
            | Num  !Integer -- ^ Matches the given number constant
            | Bool !Bool    -- ^ Matches the given boolean constant
            | Con  !Var     -- ^ Matches a GHC variable (uninterpreted constant)
              deriving Eq

fromXi :: Xi -> Maybe Term
fromXi t = msum [ Con `fmap` getTyVar_maybe t, Num `fmap` isNumLitTy t ]

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

-- For functions, the result comes first:
-- For example `x ~ a + b` or `Prop Add [x,a,b]`
data Prop = Prop Op [Term]
data Op   = Leq | Add | Mul | Exp

opName :: Op -> Name
opName Leq = typeNatLeqTyFamName
opName Add = typeNatAddTyFamName
opName Mul = typeNatMulTyFamName
opName Exp = typeNatExpTyFamName

matchProp :: Prop -> Ct -> Maybe Subst
matchProp (Prop op ts) (CFunEqCan { cc_fun = tc, cc_tyargs = xis, cc_rhs = xi})
  | tyConName tc == opName op = matchTerms ts (xi : xis)

matchProp _ _ = Nothing

matchAxiom :: Prop -> Maybe Subst -- XXX: Also proof

matchAxiom (Prop op [r, Num a, Num b]) = matchTermTerm r val
  where
  val = case op of
          Add -> Num  $ a + b
          Mul -> Num  $ a * b
          Exp -> Num  $ a ^ b
          Leq -> Bool $ a <= b

matchAxiom (Prop op [Num r, a, Num b]) = matchTermTerm a =<< val
  where
  val = case op of
          Add -> Num `fmap` minus r b
          Mul -> Num `fmap` divide r b
          Exp -> Num `fmap` rootExact r b
          Leq -> Nothing

matchAxiom (Prop op [Num r, Num a, b]) = matchTermTerm b =<< val
  where
  val = case op of
          Add -> Num `fmap` minus r a
          Mul -> Num `fmap` divide r a
          Exp -> Num `fmap` logExact r a
          Leq -> Nothing

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

matchAxiom _ = Nothing


data Rule   = Rule [(PVar,Prop)] Conc Proof

data Conc   = CProp Prop | CEq Term Term

data Proof  = By TypeNatCoAxiom [Term] [ Proof ]
            | Proved EvVar
            | Assumed PVar



-- | A smart constructor for easier rule constrction.
rule :: TypeNatCoAxiom -> [Prop] -> Conc -> Rule
rule ax asmps conc
  | wellFormed = Rule as conc $ By ax (map Var vs) $ map (Assumed . fst) as
  | otherwise  = panic "Malfored rule."
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


{- Try to use the given constraint to satisfy one of the assumptoins
for a rule.  We return a list because the consraint may be used to
satisfy multiple (or none) of the assumptions. -}

specRuleCt :: Rule -> Ct -> [Rule]
specRuleCt (Rule as c proof) ct =
  do ((n,p), rest) <- choose as
     su <- maybeToList (matchProp p ct)
     return $ apSubst su $ Rule rest c $ define n (Proved (ctId ct)) proof

define :: PVar -> Proof -> Proof -> Proof
define n p (Assumed m) | n == m   = p
define n p (By ax ts ps)          = By ax ts (map (define n p) ps)
define _ _ p                      = p


-- Consider each element of the list (and the rest)
choose :: [a] -> [(a,[a])]
choose []       = []
choose (a : as) = (a, as) : [ (b, a : bs) | (b,bs) <- choose as ]


-- (a + b = x, b + c = y, a + y = z) => (x + c = z)


-- (?a + ?b = ?x, ?b + ?c = ?y, ?a + ?y = ?z) => (?x + ?c = ?z)

-- givens ( 5 + c = y, 2 + y = z )


-- (?a + ?b = ?x) | (?b + ?c = ?y, ?a + ?y = ?z) => (?x + ?c = ?z)

-- (?a + 5 = ?x) | (5 + c = y, ?a + y = ?z) => (?x + c = ?z)

-- (2 + 5 = ?x) | (5 + c = y, 2 + y = z) => (?x + c = z)
-- (5 + c = y, 2 + y = z) => (7 + c = z)




-- (2 + 5 = 7, 5 + c = y, 2 + y = z) => (7 + c = z)


-- (?a + ?b1 ~ ?c, ?a + ?b2 ~ ?c) => (?b1 ~ ?b2)
-- (0 + x ~ y)

-- (0 + x ~ y, 0 + ?b2 ~ y) => (x ~ ?b2)

