module TcTypeNatsRules where

import Name     ( Name )
import Var      ( Var )
import TyCon    ( TyCon, tyConName )
import Type     ( isNumLitTy, getTyVar_maybe )
import PrelNames( typeNatLeqTyFamName
                , typeNatAddTyFamName
                , typeNatMulTyFamName
                , typeNatExpTyFamName
                )
import Panic    ( panic )

import TcRnTypes      ( Xi, Ct(..) )
import TcTypeNatsEval ( minus, divide, logExact, rootExact )

import Data.Maybe ( fromMaybe )
import qualified Data.IntMap as IMap
import Control.Monad ( msum )

type RVar   = Int
type Subst  = IMap.IntMap Term

data Term   = Var !RVar     -- ^ Matches anything
            | Num !Integer  -- ^ Matches the given literal constant
            | Bool !Bool    -- ^ Matches the given boolean constant
            | Con !Var      -- ^ Matches a GHC variable (uninterpreted constant)
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

specTerm :: Subst -> Term -> Term
specTerm su term =
  case term of
    Var a -> fromMaybe term (IMap.lookup a su)
    _     -> term

matchTerms :: [Term] -> [Xi] -> Maybe Subst
matchTerms [] [] = return IMap.empty
matchTerms (t : ts) (xi : xis) =
  do su1 <- matchTermXi t xi
     su2 <- matchTerms (map (specTerm su1) ts) xis
     return (IMap.union su1 su2)
matchTerms _ _ = Nothing

-- For functions, the result comes first:
-- For example `x ~ a + b` or `Prop addCon [x,a,b]`
data Prop = Prop { pOp :: Op , pTerms :: [Term] }
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



{-
              deriving Eq

              deriving (Eq,Ord,Show)

data Proof  = By String [Term] [Proof]   -- Using an existing fact
            | DefAx Op Term Term        -- Definitional axiom
            | ByAsmp String

data Rule   = Rule { rForall  :: [String]
                   , rAsmps   :: [(String,Prop)]  -- named assumptions
                   , rSides   :: [Prop]           -- no variables here
                   , rConc    :: Prop
                   , rProof   :: [(String,Term)]    -- inst. for terms
                              -> [(String,Proof)]   -- inst. for asmps
                              -> Proof
                   }
-}
-- (a + b1 ~ c, a + b2 ~ c) => (b1 ~ b2)

-- (2 + b1 ~ 5, 2 + b2 ~ 5) =>



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

