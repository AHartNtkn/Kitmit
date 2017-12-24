module Main where

import qualified Data.Map.Strict as Map
import Control.Monad.State
import Control.Monad.Identity
import Data.List hiding (union, insert)
import Data.Set hiding (map, foldr)
import Control.Monad.Except

main :: IO ()
main = return ()

-- ========== Level 0 : Used for Debuging ==========

data Hole = Hole

-- ========== Level 1 : Including types and a prototype *, without anything else ==========
-- Note: This level is used exclusivly in coherences.

-- The level-1 proof environment monad.
type Proof1 = Except String

-- Basic terms for level-1 types. In this case, it's just string variables which may be bound.
data Term1 = Var1 String
           deriving (Show, Eq)

-- Basic data types with nothing else.
-- The bool in Cell1 represents whether it's invertable.
data Type1 = Star1
           | Cell1 Bool Type1 Term1 Term1
           deriving (Show, Eq)

-- A context of level-1 types.
type Ctx1 = [(String, Type1)]

-- Calculate the dimention of a type
typeDim1 :: Type1 -> Int
typeDim1 Star1 = 0 
typeDim1 (Cell1 b a x y) = 1 + typeDim1 a

-- Calculate the dimention of a context
ctxDim :: Ctx1 -> Int
ctxDim ((x, a) : gam) = max (typeDim1 a) (ctxDim gam)

-- Substitutions into level-1 contexts.
type Sub1 = [Term1]

-- Substitute a substitution into a term.
subTerm1 :: Term1 -> Ctx1 -> Sub1 -> Term1
subTerm1 (Var1 x) ((s, t) : gam) (ss : sub) =
  if x == s
  then ss
  else subTerm1 (Var1 x) gam sub
subTerm1 (Var1 x) _ _ = Var1 x
-- Note, the substitution and context should run out at the same time.
-- Running checkSub1 prevents this from going wrong.

-- Substitute a substitution into a type.
subType1 :: Type1 -> Ctx1 -> Sub1 -> Type1
subType1 Star1 _ _ = Star1
subType1 (Cell1 b ty tr1 tr2) gam sub
  = Cell1 b (subType1 ty gam sub) (subTerm1 tr1 gam sub) (subTerm1 tr2 gam sub)

-- Check if a substitution is well defined modulo a context.
-- That is, we're checking if Delta |- sub : Gamma
checkSub1 :: Ctx1 -> Ctx1 -> Sub1 -> Proof1 ()
checkSub1 del [] [] = return ()
checkSub1 del ((s, ty) : gam) (t : sub) =
  checkCtxType1 gam ty >> -- Is this actually neccessary? This is already done by checkCtx1.
  checkCtxTerm1 del t (subType1 ty gam sub) >>
  checkSub1 del gam sub

-- Check if a context only has fresh variables.
freshContext1Q :: Ctx1 -> Proof1 ()
freshContext1Q gam = go where
  gam' = map fst gam

  go = if gam' == nub gam' -- Check if any variables are repeated.
       then return ()
       else throwError $ "The context " ++ show gam' ++ " has repeated variables."

-- Check if Gamma |- A type
checkCtxType1 :: Ctx1 -> Type1 -> Proof1 ()
checkCtxType1 gam Star1 = return ()
checkCtxType1 gam (Cell1 b ty st1 st2) =
  checkCtxType1 gam ty >>
  checkCtxTerm1 gam st1 ty >>
  checkCtxTerm1 gam st2 ty

-- Check if Gamma |- a : A
checkCtxTerm1 :: Ctx1 -> Term1 -> Type1 -> Proof1 ()
checkCtxTerm1 gam (Var1 s) t =
  if elem (s, t) gam
  then return ()
  else throwError (show s ++ " does not appear with type " ++ show t ++ " in the context " ++ show gam ++ ".")

-- Check that a level-1 context is well formed
checkCtx1 :: Ctx1 -> Proof1 ()
checkCtx1 gam = freshContext1Q gam >> go gam where
  go ((s, ty) : gam') = checkCtxType1 gam' ty >> go gam'

-- Get a list of free-variables in a term
fvTerm1 :: Term1 -> Set String
fvTerm1 (Var1 x) = singleton x

-- Get a list of free-variables in a type
fvType1 :: Type1 -> Set String
fvType1 Star1 = empty
fvType1 (Cell1 b ty tr1 tr2) = fvType1 ty `union` fvTerm1 tr1 `union` fvTerm1 tr2

-- Get the free variables of a context
fvCtx1 :: Ctx1 -> Set String
fvCtx1 gam = fromList $ map fst gam

-- Check if a context only mentions invertable morphisms.
invctxQ :: Ctx1 -> Bool
invctxQ [] = True
invctxQ ((_, Star1) : gam) = invctxQ gam
invctxQ ((_, Cell1 False ty tr1 tr2) : gam) = False
invctxQ ((_, Cell1 True ty tr1 tr2) : gam) = invctxQ gam

-- Get a list of all the variables pointed from by a type 
typeSources :: Type1 -> [(String, Type1)]
typeSources Star1 = []
typeSources (Cell1 b ty (Var1 x) tr2) = (x, ty) : typeSources ty

-- Get a list of all the variables pointed to by a type 
typeTargets :: Type1 -> [(String, Type1)]
typeTargets Star1 = []
typeTargets (Cell1 b ty tr1 (Var1 y)) = (y, ty) : typeTargets ty

-- Check if a context is a well-formed pasting scheme
psQ :: Ctx1 -> Proof1 ()
psQ [] = throwError "A pasting scheme cannot be empty."
psQ gam@((s, ty) : _) = go gam s ty where
  go :: [(String, Type1)] -> String -> Type1 -> Proof1 ()
  go ((s, Star1) : []) s' ty
    | ty /= Star1 = throwError (show ty ++ " was not of type * when checking that "
                          ++ show ((s, Star1) : []) ++ " is a pasting scheme.")
    | s /= s'     = throwError (s ++ " did not match " ++ s' ++ " when checking that "
                          ++ show ((s, Star1) : []) ++ " is a pasting scheme.")
    | otherwise   = return ()
  go g@((s, Star1) : _) s' ty = throwError ("Hanging *, " ++ s ++ ", when checking that " ++ show g
                                            ++ " is a pasting scheme")
  go ((s, Cell1 b ty (Var1 x) (Var1 y)) : (y', ty') : gam) s' (Cell1 b' ty'' tr1 tr2)
    | b /= b'    = throwError ("Invertability missmatch when when checking that "
                         ++ show ((s, Cell1 b ty (Var1 x) (Var1 y)) : (y', ty') : gam) ++ " is a pasting scheme.")
    | s /= s'    = throwError (s ++ " did not match " ++ s' ++ " when checking that "
                         ++ show ((s, Cell1 b ty (Var1 x) (Var1 y)) : (y', ty') : gam) ++ " is a pasting scheme.")
    | y /= y'    = throwError (y ++ " did not match " ++ y' ++ " when checking that "
                         ++ show ((s, Cell1 b ty (Var1 x) (Var1 y)) : (y', ty') : gam) ++ " is a pasting scheme.")
    | ty /= ty'  = throwError (show ty ++ " b did not match " ++ show ty' ++ " when checking that "
                         ++ show ((s, Cell1 b ty (Var1 x) (Var1 y)) : (y', ty') : gam) ++ " is a pasting scheme.")
    | ty /= ty'' = throwError (show ty ++ " did not match " ++ show ty'' ++ " when checking that "
                         ++ show ((s, Cell1 b ty (Var1 x) (Var1 y)) : (y', ty') : gam) ++ " is a pasting scheme.")
    | otherwise  = go gam x ty
  go ((s, Cell1 b ty tr1 tr2) : gam) x a
    | elem (x, a) (typeTargets $ Cell1 b ty tr1 tr2) = go ((s, Cell1 b ty tr1 tr2) : gam) s (Cell1 b ty tr1 tr2)
    | otherwise = throwError (x ++ " of type " ++ show a ++ " does not appear as a target of " ++ show (Cell1 b ty tr1 tr2)
                        ++ " when checking that " ++ show ((s, Cell1 b ty tr1 tr2) : gam) ++ " is a pasting scheme.")

-- Calculate the source of a pasting scheme
pssource' :: Int -> Ctx1 -> Ctx1
pssource' i ((x, Star1) : []) = (x, Star1) : []
pssource' i ((f, Cell1 b a x y) : (y' , a') : gam)
  | typeDim1 a >= i = pssource' i gam
  | otherwise = (f, Cell1 b a x y) : (y' , a') : pssource' i gam

pssource :: Ctx1 -> Ctx1
pssource gam = pssource' (ctxDim gam - 1) gam

-- Calculate the target of a pasting scheme
pstarget' :: Int -> Ctx1 -> Ctx1
pstarget' i ((x, Star1) : []) = (x, Star1) : []
pstarget' i ((f, Cell1 b a x y) : (y' , a') : gam)
  | typeDim1 a > i  = pstarget' i gam
  | typeDim1 a == i = (y' , a') : tail (pstarget' i gam)
  | otherwise = (f, Cell1 b a x y) : (y' , a') : pstarget' i gam

pstarget :: Ctx1 -> Ctx1
pstarget gam = pstarget' (ctxDim gam - 1) gam

-- ========== Level 2 : Including types and a prototype *, with composition/coherences ==========

-- The level-2 proof environment monad.
-- Contains errors and a context of defined coherences.
type Proof2 = ExceptT String (State (Map.Map String (Ctx1, Type2)))

liftProof12 :: Proof1 a -> Proof2 a
liftProof12 (ExceptT (Identity (Left s))) = ExceptT (StateT (\m -> Identity (Left s, m)))
liftProof12 (ExceptT (Identity (Right a))) = ExceptT (StateT (\m -> Identity (Right a, m)))

-- Terms for level-2 types, which including composition.
data Term2 = Var2 String
           | App2 String Sub2
           deriving (Show, Eq)

-- Data types, including compositions.
data Type2 = Star2
           | Cell2 Bool Type2 Term2 Term2
           deriving (Show, Eq)

typeDim2 :: Type2 -> Int
typeDim2 Star2 = 0 
typeDim2 (Cell2 b a x y) = 1 + typeDim2 a

-- A context of level-2 types.
type Ctx2 = [(String, Type2)]

-- Substitutions into level-2 contexts.
type Sub2 = [Term2]

-- ------- Translate from level 1 to level 2 ----------
liftTerm12 :: Term1 -> Term2
liftTerm12 (Var1 x) = Var2 x

liftType12 :: Type1 -> Type2
liftType12 Star1 = Star2
liftType12 (Cell1 i a b c) = Cell2 i (liftType12 a) (liftTerm12 b) (liftTerm12 c)

liftCtx12 :: Ctx1 -> Ctx2
liftCtx12 gam = map (\(s, x) -> (s, liftType12 x)) gam

liftSub12 :: Sub1 -> Sub2
liftSub12 gam = map liftTerm12 gam
-- ------- ---------------------------------- ----------

-- Substitute a substitution into a term.
subTerm2 :: Term2 -> Ctx2 -> Sub2 -> Term2
subTerm2 (Var2 x) ((s, t) : gam) (ss : sub) =
  if x == s
  then ss
  else subTerm2 (Var2 x) gam sub
subTerm2 (Var2 x) _ _ = Var2 x
subTerm2 (App2 s y) gam sub = App2 s $ map (\y -> subTerm2 y gam sub) y
-- Note, the substitution and context should run out at the same time.
-- Running checkSub2 prevents this from going wrong.

-- Substitute a substitution into a type.
subType2 :: Type2 -> Ctx2 -> Sub2 -> Type2
subType2 Star2 _ _ = Star2
subType2 (Cell2 b ty tr1 tr2) gam sub
  = Cell2 b (subType2 ty gam sub) (subTerm2 tr1 gam sub) (subTerm2 tr2 gam sub)

-- Check if a substitution is well defined modulo a context.
-- That is, we're checking if Delta |- sub : Gamma
checkSub2 :: Ctx2 -> Ctx2 -> Sub2 -> Proof2 ()
checkSub2 del [] [] = return ()
checkSub2 del ((s, ty) : gam) (t : sub) =
  checkCtxType2 gam ty >> -- Is this actually neccessary? This is already done by checkCtx2.
  checkCtxTerm2 del t (subType2 ty gam sub) >>
  checkSub2 del gam sub

-- Check if a context only has fresh variables.
freshContext2Q :: Ctx2 -> Proof2 ()
freshContext2Q gam = go where
  gam' = map fst gam

  go = if gam' == nub gam' -- Check if any variables are repeated.
       then return ()
       else throwError $ "The context " ++ show gam' ++ " has repeated variables."

-- Check if Gamma |- A type
checkCtxType2 :: Ctx2 -> Type2 -> Proof2 ()
checkCtxType2 gam Star2 = return ()
checkCtxType2 gam (Cell2 b ty st1 st2) =
  checkCtxType2 gam ty >>
  checkCtxTerm2 gam st1 ty >>
  checkCtxTerm2 gam st2 ty

-- Check if Gamma |- a : A
checkCtxTerm2 :: Ctx2 -> Term2 -> Type2 -> Proof2 ()
checkCtxTerm2 gam (Var2 s) t =
  if elem (s, t) gam
  then return ()
  else throwError (show s ++ " does not appear with type " ++ show t ++ " in the context " ++ show gam ++ ".")
checkCtxTerm2 gam (App2 s r) t = do
  cohr <- get
  let (sgam, sty) = cohr Map.! s
  checkSub2 gam (liftCtx12 sgam) r -- Make sure r is a valid substitution
  let rety = subType2 sty (liftCtx12 sgam) r
  if rety == t
  then return ()
  else throwError (show (App2 s r) ++ " of type " ++ show rety ++ " is not of type " ++ show t
                   ++ " when checking in context " ++ show gam ++ ".")

-- Check that a level-1 context is well formed
checkCtx2 :: Ctx2 -> Proof2 ()
checkCtx2 gam = freshContext2Q gam >> go gam where
  go ((s, ty) : gam') = checkCtxType2 gam' ty >> go gam'

-- Get a list of free-variables in a term
fvTerm2 :: Term2 -> Set String
fvTerm2 (Var2 x) = singleton x
fvTerm2 (App2 s r) = fvSub2 r

-- Get a list of free-variables in a type
fvType2 :: Type2 -> Set String
fvType2 Star2 = empty
fvType2 (Cell2 b ty tr1 tr2) = fvType2 ty `union` fvTerm2 tr1 `union` fvTerm2 tr2

-- Get the free variables of an (assumed well-formed) context
fvCtx2 :: Ctx2 -> Set String
fvCtx2 gam = fromList $ map fst gam

-- Get the free variables of the type of a free variable (not including the variable itself)
fvVarTyCtx2 :: Ctx2 -> String -> Set String
fvVarTyCtx2 [] v = empty
fvVarTyCtx2 ((v', ty) : gam) v = if v == v' then fvType2 ty else fvVarTyCtx2 gam v

-- Get the free variables of a substitution
fvSub2 :: Sub2 -> Set String
fvSub2 sub = unions $ map fvTerm2 sub

-- Check that a context leads correctly to a particular coherence.
checkCoh :: Ctx1 -> Type2 -> Proof2 ()
checkCoh gam ty = liftProof12 (psQ gam) >> go where
  go :: Proof2 ()
  go
   -- If gam is completly invertable, then all well-formed types are inhabited.
   | invctxQ gam = checkCtxType2 (liftCtx12 gam) ty
   -- If All free variables of the type appear in the context, then the type is inhabited.
   | fvCtx1 gam == fvType2 ty = checkCtxType2 (liftCtx12 gam) ty
   | otherwise = checkCtxType2 (liftCtx12 gam) ty >> goc gam ty

  -- If the source and target of the type align with the context, then the type is inhabited.
  goc gam (Cell2 b a s t) = checkCtxTerm2 (liftCtx12 $ pssource gam) s a >>
                          checkCtxTerm2 (liftCtx12 $ pstarget gam) t a
  goc gam _ = throwError ("Type is not coherent modulo context when checking that "
                          ++ show ty ++ " is coherent from " ++ show gam ++ ".")

-- ========== Level F : Morphisms Between Contexts ==========
-- A morphism between a context is simply a series of cells pointing between
-- contexts viewed as disconnected diagrams.

-- This section developes the machinery neccessary to check such a thing.
data CtxType = CtxStar
             | CtxCell Bool CtxType Ctx2 Ctx2

data CtxFunctor = CtxFunctor Ctx2 [(Ctx2, Ctx2)]

-- Get the context represented by a functor;
functorCtx :: CtxFunctor -> Ctx2
functorCtx (CtxFunctor c f) = c ++ foldr (\(a, b) r -> a ++ b ++ r) [] f

-- Count how many free occurences of a variable there are;
countTermFV :: String -> Term2 -> Int
countTermFV v (Var2 v') = if v == v' then 1 else 0
countTermFV v (App2 s sub) = countSubFV v sub

countTypeFV :: String -> Type2 -> Int
countTypeFV v Star2 = 0
countTypeFV v (Cell2 b ty tr1 tr2) = countTypeFV v ty + countTermFV v tr1 + countTermFV v tr2

countSubFV :: String -> Sub2 -> Int
countSubFV v [] = 0
countSubFV v (f : sub) = countTermFV v f + countSubFV v sub

-- Convert a context with its type into a functor for further proccessing
toFunctor' :: CtxType -> [(Ctx2, Ctx2)]
toFunctor' CtxStar = []
toFunctor' (CtxCell b ty c1 c2) = (c1, c2):toFunctor' ty

toFunctor :: Ctx2 -> CtxType -> CtxFunctor
toFunctor c ty = CtxFunctor c $ reverse $ toFunctor' ty

-- Check that a functor is made up entirely of well-formed contexts.
checkFunctor :: CtxFunctor -> Proof2 ()
checkFunctor fu@(CtxFunctor f g@((c1, c2) : k)) = do
  checkCtx2 $ functorCtx fu
  checkCtx2 $ functorCtx $ CtxFunctor c2 k
  checkFunctor (CtxFunctor c2 k)

-- Calculate the shape of a context as the dimentions of the individual components
ctxShape :: Ctx2 -> [Int]
ctxShape = map (typeDim2 . snd)

-- Make sure the shapes of the contexts are comparable
compareShapes :: Ctx2 -> Ctx2 -> Ctx2 -> Proof2 ()
compareShapes fun gam gam'
  | ctxShape gam /= ctxShape gam'
     = throwError ("Shape missmatch between " ++ show gam ++ " and " ++ show gam' ++ ".")
  | ctxShape fun /= map (+1) (ctxShape gam')
     = throwError ("Shape missmatch between " ++ show fun ++ " and " ++ show gam ++ ".")
  | otherwise = return ()

-- Make sure a functor consists only of contexts with similar shapes;
checkFunctorShape :: CtxFunctor -> Proof2 ()
checkFunctorShape (CtxFunctor fun ((gam, del) : [])) = compareShapes fun gam del
checkFunctorShape (CtxFunctor fun ((gam, del) : g)) = do
  compareShapes fun gam del
  checkFunctorShape (CtxFunctor gam g)

-- Check that a functor of arbitrary dimention is well-formed
-- Note: This assumes the shapes of the functor contexts have already been compared
checkCtxDisk' :: Ctx2 -> Ctx2 -> Ctx2 -> Ctx2 -> Proof2 ()
checkCtxDisk' res [] [] [] = return ()
checkCtxDisk' res fu@((fn, fty) : g1) gam@((sn, sty) : g2) gam'@((tn, tty) : g3) =
  case fty of
    Star2 -> throwError (fn ++ "of type * cannot be used as a cell within a functor.")
    Cell2 b fty' s t -> cel2 where
      cel2
        | countTermFV sn s /= 1
           = throwError ("There should be precicly one reference to source name " ++ sn ++ " in the expression "
                         ++ show s ++ " when checking that " ++ show (Cell2 b fty' s t) ++
                         " is an appropriate cell type out of " ++ sn ++ " and " ++ tn ++ ".")
        | countTermFV tn t /= 1
           = throwError ("There should be precicly one reference to target name " ++ tn ++ " in the expression "
                         ++ show t ++ " when checking that " ++ show (Cell2 b fty' s t) ++
                         " is an appropriate cell type between of " ++ sn ++ " and " ++ tn ++ ".")
        | fvTerm2 s `difference` fvType2 sty
                    `difference` fvCtx2 g1
                    `difference` fvCtx2 res
                    `difference` unions (map (fvVarTyCtx2 g1) (toList $ fvTerm2 s))
             /= singleton sn
           = throwError ("Source " ++ show s ++ " should only mention variables from " ++ show sty ++ " and/or "
                         ++ show g1 ++ " when checking that " ++ show (Cell2 b fty' s t) ++
                         " is an appropriate cell type out of " ++ sn ++ ".")
        | fvTerm2 t `difference` fvType2 tty
                    `difference` fvCtx2 g1
                    `difference` fvCtx2 res
                    `difference` unions (map (fvVarTyCtx2 g1) (toList $ fvTerm2 t))
             /= singleton tn
           = throwError ("Target " ++ show t ++ " should only mention variables from " ++ show tty ++ " and/or "
                         ++ show g1 ++ " when checking that " ++ show (Cell2 b fty' s t) ++
                         " is an appropriate cell type out of " ++ tn ++ ".")
        | otherwise = checkCtxType2 (g1 ++ gam ++ gam' ++ res) fty >> checkCtxDisk' res g1 g2 g3

checkCtxDisk :: CtxFunctor -> Proof2 ()
checkCtxDisk (CtxFunctor f []) = return ()
checkCtxDisk (CtxFunctor fu ((g1, g2) : g))  = do
  checkCtxDisk' (foldr (\(a, b) r -> a ++ b ++ r) [] g) fu g1 g2
  -- Note: This leads to an exponential explosion. How to organize so that doesn't happen???
  checkCtxDisk (CtxFunctor g1 g)
  checkCtxDisk (CtxFunctor g2 g)

-- Check that a context is a subcontext of another;
subCtxCheck :: Ctx2 -> Ctx2 -> Proof2 ()
subCtxCheck [] del = return ()
subCtxCheck ((a, ty) : gam) del = do
  checkCtxTerm2 del (Var2 a) ty
  subCtxCheck gam del

-- ========== Level 3.1 : Including types, composition, and colimits ==========

-- The level-3 proof environment monad.
-- Contains errors and a context of defined coherences.
-- Contains errors and a context of defined and defined colimits.
type Proof31 = ExceptT String (StateT (Map.Map String (Ctx1, Type2)) (State (Map.Map String (Ctx2, Type31))))

getCoh31 :: Proof31 (Map.Map String (Ctx1, Type2))
getCoh31 = ExceptT $ StateT $ \m -> StateT $ \m' -> Identity ((Right m, m), m')

getCol31 :: Proof31 (Map.Map String (Ctx2, Type31))
getCol31 = ExceptT $ StateT $ \m -> StateT $ \m' -> Identity ((Right m', m), m')

liftProof231 :: Proof2 a -> Proof31 a
liftProof231 (ExceptT (StateT r)) = ExceptT $ StateT $ \m -> StateT $ \m' -> r m >>= \res -> return (res, m')

liftProof131 :: Proof1 a -> Proof31 a
liftProof131 = liftProof231 . liftProof12

-- Terms for level-3 types, which including composition and colimits.
data Term31 = Var31 String
           | App31 String Sub31 -- Application into coherence
           | Appc31 String [String] -- Application into colimit
           deriving (Show, Eq)

-- Data types, including compositions and colimits.
data Type31 = Star31
            | Cell31 Bool Type31 Term31 Term31
            deriving (Show, Eq)

-- A context of level-31 types.
type Ctx31 = [(String, Type31)]

-- Substitutions into level-31 contexts.
type Sub31 = [Term31]

type SSub31 = [String]

-- ------- Translate from level 2 to level 31.1 ----------
liftTerm231 :: Term2 -> Term31
liftTerm231 (Var2 x) = Var31 x
liftTerm231 (App2 s r) = App31 s (liftSub231 r)

liftTerm131 :: Term1 -> Term31
liftTerm131 = liftTerm231 . liftTerm12

liftType231 :: Type2 -> Type31
liftType231 Star2 = Star31
liftType231 (Cell2 i a b c) = Cell31 i (liftType231 a) (liftTerm231 b) (liftTerm231 c)

liftType131 :: Type1 -> Type31
liftType131 = liftType231 . liftType12

liftCtx231 :: Ctx2 -> Ctx31
liftCtx231 gam = map (\(s, x) -> (s, liftType231 x)) gam

liftCtx131 :: Ctx1 -> Ctx31
liftCtx131 = liftCtx231 . liftCtx12

liftSub231 :: Sub2 -> Sub31
liftSub231 gam = map liftTerm231 gam

liftSub131 :: Sub1 -> Sub31
liftSub131 = liftSub231 . liftSub12
-- ------- ---------------------------------- ----------

-- Substitute a substitution into a term.
subTerm31 :: Term31 -> Ctx31 -> Sub31 -> Term31
subTerm31 (Var31 x) ((s, t) : gam) (ss : sub) =
  if x == s
  then ss
  else subTerm31 (Var31 x) gam sub
subTerm31 (Var31 x) _ _ = Var31 x
subTerm31 (App31 s y) gam sub = App31 s $ map (\y -> subTerm31 y gam sub) y
subTerm31 (Appc31 s y) gam sub = Appc31 s y -- This is all that I can really do, but it may make
                                            -- more sense to make y a Sub31 and have a check to make sure it 
                                            -- only contains variables, instead of enforcing it with grammar.
-- Note, the substitution and context should run out at the same time.
-- Running checkSub31 prevents this from going wrong.

-- Substitute a substitution into a type.
subType31 :: Type31 -> Ctx31 -> Sub31 -> Type31
subType31 Star31 _ _ = Star31
subType31 (Cell31 b ty tr1 tr2) gam sub
  = Cell31 b (subType31 ty gam sub) (subTerm31 tr1 gam sub) (subTerm31 tr2 gam sub)

-- Check if a substitution is well defined modulo a context.
-- That is, we're checking if Delta |- sub : Gamma
checkSub31 :: Ctx31 -> Ctx31 -> Sub31 -> Proof31 ()
checkSub31 del [] [] = return ()
checkSub31 del ((s, ty) : gam) (t : sub) =
  checkCtxType31 gam ty >> -- Is this actually neccessary? This is already done by checkCtx31.
  checkCtxTerm31 del t (subType31 ty gam sub) >>
  checkSub31 del gam sub

-- Substitute a substitution into a term.
ssubTerm31 :: Term31 -> Ctx31 -> SSub31 -> Term31
ssubTerm31 (Var31 x) ((s, t) : gam) (ss : sub) =
  if x == s
  then Var31 ss
  else ssubTerm31 (Var31 x) gam sub
ssubTerm31 (Var31 x) _ _ = Var31 x
ssubTerm31 (App31 s y) gam sub = App31 s $ map (\y -> ssubTerm31 y gam sub) y
ssubTerm31 (Appc31 s y) gam sub = Appc31 s y -- This is all that I can really do, but it may make
                                            -- more sense to make y a Sub31 and have a check to make sure it 
                                            -- only contains variables, instead of enforcing it with grammar.
-- Note, the substitution and context should run out at the same time.
-- Running checkSub31 prevents this from going wrong.

-- Substitute a substitution into a type.
ssubType31 :: Type31 -> Ctx31 -> SSub31 -> Type31
ssubType31 Star31 _ _ = Star31
ssubType31 (Cell31 b ty tr1 tr2) gam sub
  = Cell31 b (ssubType31 ty gam sub) (ssubTerm31 tr1 gam sub) (ssubTerm31 tr2 gam sub)

-- Check if a context only has fresh variables.
freshContext31Q :: Ctx31 -> Proof31 ()
freshContext31Q gam = go where
  gam' = map fst gam

  go = if gam' == nub gam' -- Check if any variables are repeated.
       then return ()
       else throwError $ "The context " ++ show gam' ++ " has repeated variables."

-- Check if Gamma |- A type
checkCtxType31 :: Ctx31 -> Type31 -> Proof31 ()
checkCtxType31 gam Star31 = return ()
checkCtxType31 gam (Cell31 b ty st1 st2) =
  checkCtxType31 gam ty >>
  checkCtxTerm31 gam st1 ty >>
  checkCtxTerm31 gam st2 ty

-- Check if Gamma |- a : A
checkCtxTerm31 :: Ctx31 -> Term31 -> Type31 -> Proof31 ()
checkCtxTerm31 gam (Var31 s) t =
  if elem (s, t) gam
  then return ()
  else throwError (show s ++ " does not appear with type " ++ show t ++ " in the context " ++ show gam ++ ".")
checkCtxTerm31 gam (App31 s r) t = do
  cohr <- getCoh31
  let (sgam, sty) = cohr Map.! s
  checkSub31 gam (liftCtx131 sgam) r -- Make sure r is a valid substitution
  let rety = subType31 (liftType231 sty) (liftCtx131 sgam) r
  if rety == t
  then return ()
  else throwError (show (App31 s r) ++ " of type " ++ show rety ++ " is not of type " ++ show t
                   ++ " when checking in context " ++ show gam ++ ".")
checkCtxTerm31 gam (Appc31 s r) t = do
  col <- getCol31
  let (sgam, sty) = col Map.! s
  -- NOTE: This isn't quite right. I should substitute r into the sgam and make sure it's
  --  1. A well-formed context and
  --  2. A subcontext of gam
  let rety = subType31 sty (liftCtx231 sgam) (map Var31 r)
  if rety == t
  then return ()
  else throwError (show (Appc31 s r) ++ " of type " ++ show rety ++ " is not of type " ++ show t
                   ++ " when checking in context " ++ show gam ++ ".")

-- Check that a level-1 context is well formed
checkCtx31 :: Ctx31 -> Proof31 ()
checkCtx31 gam = freshContext31Q gam >> go gam where
  go ((s, ty) : gam') = checkCtxType31 gam' ty >> go gam'

-- Get a list of free-variables in a term
fvTerm31 :: Term31 -> Set String
fvTerm31 (Var31 x) = singleton x
fvTerm31 (App31 s r) = fvSub31 r
fvTerm31 (Appc31 s r) = fromList r

-- Get a list of free-variables in a type
fvType31 :: Type31 -> Set String
fvType31 Star31 = empty
fvType31 (Cell31 b ty tr1 tr31) = fvType31 ty `union` fvTerm31 tr1 `union` fvTerm31 tr31

-- Get the free variables of an (assumed well-formed) context
fvCtx31 :: Ctx31 -> Set String
fvCtx31 gam = fromList $ map fst gam

-- Get the free variables of a substitution
fvSub31 :: Sub31 -> Set String
fvSub31 sub = unions $ map fvTerm31 sub


-- ========== Level 3.2 : Including types, composition, and limits ==========


-- ========== Level 4 : Including witnesses of functoriality ==========



-- ========== Level n : Including the type of types and functions as types (top-level) ==========






