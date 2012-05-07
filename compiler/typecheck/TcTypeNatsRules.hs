module TcTypeNatsRules where

-- From other GHC locations
import Name     ( Name )
import Var      ( Var, EqVar )
import TyCon    ( TyCon, tyConName )
import Coercion ( TypeNatCoAxiom (..) )
import Type     ( isNumLitTy, getTyVar_maybe, mkTyVarTy, mkNumLitTy )
import PrelNames( typeNatLeqTyFamName
                , typeNatAddTyFamName
                , typeNatMulTyFamName
                , typeNatExpTyFamName
                )
import Panic    ( panic )

-- From type checker
import TcRnTypes      ( Xi, Ct(..), ctId )
import TcTypeNatsEval ( minus, divide, logExact, rootExact )
import TcEvidence     ( TcCoercion (TcTypeNatCo)
                      , mkTcSymCo, mkTcTransCo, mkTcCoVarCo )

-- From base libraries
import Prelude hiding ( exp )
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
-- For example `a + b ~ x` is represented as `Prop Add [x,a,b]`
-- XXX: This makes matching bellow a bit simpler, but maybe it is more confusing
-- than helpful?
data Prop   = Prop Op [Term]
data Op     = Leq | Add | Mul | Exp

data Rule   = Rule [(PVar,Prop)]    -- ^ Named assumptions of the rule
                   Conc             -- ^ Conclusion of the rule
                   Proof            -- ^ Proof of conclusion (uses assumptions)

data Conc   = CProp Prop
            | CEq Term Term

data Proof  = By TypeNatCoAxiom [Term] [ Proof ]
            | Assumed PVar
            | Proved EqVar
            | Sym Proof | Trans Proof Proof   -- used in `funRule`


leq :: Term -> Term -> Prop
leq x y = Prop Leq [ Bool True, x, y ]

add :: Term -> Term -> Term -> Prop
add x y z = Prop Add [ z, x, y ]

mul :: Term -> Term -> Term -> Prop
mul x y z = Prop Mul [ z, x, y ]

exp :: Term -> Term -> Term -> Prop
exp x y z = Prop Exp [ z, x, y ]


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


toCoercion :: Proof -> TcCoercion
toCoercion proof  =
  case proof of
    By ax ts ps -> TcTypeNatCo ax (map toXi ts) (map toCoercion ps)
    Sym p       -> mkTcSymCo (toCoercion p)
    Trans p q   -> mkTcTransCo (toCoercion p) (toCoercion q)
    Proved ev   -> mkTcCoVarCo ev
    Assumed _   -> panic "Incomplete proof"

toXi :: Term -> Xi
toXi term =
  case term of
    Var _  -> panic "Incomplete term"
    Bool _ -> panic "XXX: Make boolean literal"
    Num n  -> mkNumLitTy n
    Con c  -> mkTyVarTy c


--------------------------------------------------------------------------------



--------------------------------------------------------------------------------

-- XXX: We should be able to cope with some assumptions in backward
-- reasoning too.
bRules :: [Rule]
bRules = map (uncurry simpleRule)
  [ (TnLeq0    , leq n0 a)
  , (TnLeqRefl , leq a a)

  , (TnAdd0L   , add n0 a a)
  , (TnAdd0R   , add a n0 a)

  , (TnMul0L   , mul n0 a n0)
  , (TnMul0R   , mul a n0 n0)
  , (TnMul1L   , mul n1 a a)
  , (TnMul1R   , mul a n1 a)

  -- TnExp0L
  , (TnExp0R   , exp a n0 n1)
  , (TnExp1L   , exp n1 a n1)
  , (TnExp1R   , exp a n1 a)
  ]
  where a  = Var 0
        n0 = Num 0
        n1 = Num 1


fRules :: [Rule]
fRules =
  map funRule [ Add, Mul, Exp, Leq ]
  ++
  [ rule TnLeqASym    [ leq a b, leq b a ] $ CEq a b
  , rule TnLeqTrans   [ leq a b, leq b c ] $ CProp $ leq a c

  , rule TnAddComm    [ add a b c ] $ CProp $ add b a c
  , rule TnMulComm    [ mul a b c ] $ CProp $ mul b a c

  , rule TnAddCancelL [           add a b1 c, add a b2 c ] $ CEq b1 b2
  , rule TnMulCancelL [ leq n1 a, mul a b1 c, mul a b2 c ] $ CEq b1 b2
  , rule TnExpCancelL [ leq n2 a, exp a b1 c, exp a b2 c ] $ CEq b1 b2

  , rule TnAddCancelR [           add a1 b c, add a2 b c ] $ CEq a1 a2
  , rule TnMulCancelR [ leq n1 b, mul a1 b c, mul a2 b c ] $ CEq a1 a2
  , rule TnExpCancelR [ leq n1 b, exp a1 b c, exp a2 b c ] $ CEq a1 a2
  ]
  where
  a : a1 : a2 : b : b1 : b2 : c : _ = map Var [ 0 .. ]
  n1 = Num 1
  n2 = Num 2




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

{- This slightly duplicates the functionality of GHC's solver but
we have it here so that it can react with axioms.
For example, the following is justified using a fun-rule and an axiom:

(5 + 3 ~ x) => (x ~ 8)
like this:
(5 + 3 ~ x, 5 + 3 ~ 8) => (x ~ 8)
-}

-- p: a + b ~ c1, q: a + b ~ c2
-- sym p `trans` q
funRule :: Op -> Rule
funRule op = Rule [ (p, Prop op [ c1, a, b]), (q, Prop op [ c2, a, b ]) ]
                  (CEq c1 c2)
                  (Trans (Sym (Assumed p)) (Assumed q))
  where a : b : c1 : c2 : _ = map Var [ 0 .. ]
        p : q : _           = [ 0 .. ]


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
byAsmp :: Ct -> Prop -> Maybe (Subst, Proof)
byAsmp ct (Prop op ts)
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
  apSubst su (Sym p)        = Sym (apSubst su p)
  apSubst su (Trans p q)    = Trans (apSubst su p) (apSubst su q)


-- | Define an assumption paramater in the proof of a rule.
define :: PVar -> Proof -> Proof -> Proof
define n p (Assumed m) | n == m   = p
define n p (By ax ts ps)          = By ax ts (map (define n p) ps)
define n p (Sym q)                = Sym (define n p q)
define n p (Trans q r)            = Trans (define n p q) (define n p r)
define _ _ p                      = p


-- Consider each element of the list (and the rest)
choose :: [a] -> [(a,[a])]
choose []       = []
choose (a : as) = (a, as) : [ (b, a : bs) | (b,bs) <- choose as ]



