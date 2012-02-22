% ProgGen
% jason,mfn,colin
% 21/11/11

+ > module ProgGen where

Notes & Gotchas
===============

+   Traversal orders are important. A normal order property will 
bypass an in-order validation. Consider generics to avoid?
+   Flag (HavaAGo) monad instead of Maybe preserves laziness.
+   There's a depth difference because we tuple alternatives
    instead of listing them. Zero depth cost.
+   noDeadCode was too strict. Fixed now. e.g This passed
    f x y = case x of {A -> B; B -> y}
    g x y = case x of {A -> f B y}
    > f A (g A B)
+   We have CAFs!
+   Can't have length' on its own as it throws away data.
+   Do not want ordered arities for functions!

Introduction
============

This is a library that uses LazySmallCheck to generate canonical 
first-order functional programs programs.

> import Test.LazySmallCheck

> import Criterion.Main
> import Control.Applicative
> import Control.Monad (foldM, guard, MonadPlus(..))
> import Control.Monad.Writer.Lazy hiding ((>=>), lift)
> import Data.Function
> import Data.List
> import Data.Maybe
> import System.IO

Small sequences
---------------

These will be useful later on.

> newtype Seq0'2 a = Seq0'2 [a] deriving (Ord,Eq)
> 
> instance Show a => Show (Seq0'2 a) where
>   show (Seq0'2 xs) = show xs
> 
> instance Serial a => Serial (Seq0'2 a) where
>   series = (cons Seq0'2 >< children0'2) . (+1)
> 
> children0'2 d = list (min 2 d)
>   where
>     list = cons []
>         \/ cons (:) >< const (series (d-1)) >< list

Our Language
============

Our language can be represented as follows.

> newtype Id = Id Char
> 
> data Pro = Pro (Seq1 ConDef) Exp (Seq RedDef)
> 
> data ConDef = Id :# Nat        -- Constructor definitions
> 
> data RedDef = Seq1 Id := Bod   -- Function definitions
> 
> data Bod = Solo Exp
>          | Case Exp (Seq1 Alt)
> data Exp = Var VarId           -- Variables
>          | App DecId (Seq Exp) -- Applications
> data VarId = Arg Id
>            | Pat Id
> 
> data DecId = Con Id
>            | Red Id
> 
> data Alt = Seq1 Id :--> Exp    -- Case alternatives

And we can have a pretty printer associated with it.

> instance Show Pro where
>   show (Pro (Seq1 cons) m (Seq eqns))
>     = unlines $ ("data D = " ++ show cons) 
>       : map show eqns ++ ["> " ++ show m ]
> 
> instance Show ConDef where
>    show (c :# N arity) = concat $ 
>     show (Con c) : [' ' | arity > 0] 
>     : intersperse " " (replicate arity "D")
>    showList xs = (++) $ intercalate " | " (map show xs)
> 
> 
> instance Show RedDef where
>  show (Seq1 (f:xs) := rhs) 
>    = intercalate " " (show (Red f) 
>                       : map (show . Arg) xs) ++ " = " ++ show rhs
> 
> instance Show Bod where
>   show (Solo e) = show e
>   show (Case s (Seq1 alts)) = "case " ++ showArg s 
>                                ++ " of {" ++ show alts ++ "}"
> 
> instance Show Exp where
>  show (Var v)  = show v
>  show (App d (Seq xs)) = intercalate " " (show d : map showArg xs)
> 
> class Show a => ShowArg a where
>   showArg :: a -> String
> 
> instance ShowArg Exp where
>   showArg x@(Var _)       = show x
>   showArg x@(App _ (Seq xs)) = if null xs then show x
>                                else "(" ++ show x ++ ")"
> 
> instance Show Alt where
>   show (Seq1 (c:xs) :--> e) = intercalate " " (show (Con c) 
>                  : map (show . Pat) xs) ++ " -> " ++ show e
>   showList xs tail = (intercalate "; " . map show) xs ++ tail
> 
> niceChr c x = toEnum (fromEnum c + fromEnum x - fromEnum '0')
> 
> instance Show VarId where
>   show (Arg (Id v)) = [niceChr 'x' v]
>   show (Pat (Id v)) = [niceChr 'p' v]
>   
> instance Show DecId where
>   show (Con (Id d)) = [niceChr 'A' d]
>   show (Red (Id d)) = [niceChr 'f' d]
> 
> instance Show Id where
>  show (Id x) = [x]
>  showList xs tail = intersperse ' ' [ x | Id x <- xs ] ++ tail

Intermediate Form: Positional
=============================

We have an intermediate form which uses positional naming, 
represented by integers.

> data ProP = ProP (Seq1 Nat) ExpP (Seq RedDefP)
> 
> data RedDefP = Nat :=: BodP   -- Function definitions
> 
> data BodP = SoloP ExpP
>           | CaseP ExpP (Seq1 AltP)
> 
> data ExpP = VarP VarIdP           -- Variables
>           | AppP DecIdP (Seq ExpP) -- Applications
> 
> data VarIdP = ArgP Nat
>             | PatP Nat
> 
> data DecIdP = ConP Nat
>             | RedP Nat
> 
> data AltP = Nat :-->: ExpP    -- Case alternatives

And translate this form into our original.

> nameProP :: ProP -> Pro
> nameProP prog@(ProP (Seq1 cons) m (Seq eqns)) 
>   = Pro (Seq1 (zipWith (:#) digits cons)) 
>         (npe m)
>         (Seq [ Seq1 (f : take a digits)
>                := npb e
>              | (f, N a :=: e) <- zip digits eqns ])
>   where
>     digits = map Id ['0'..'9']
>     npb (SoloP e) = Solo (npe e)
>     npb (CaseP s (Seq1 alts)) = Case (npe s) $ Seq1
>                                 [ Seq1 (digits !! c : take a digits)
>                                   :--> npe e
>                                 | N c :-->: e <- alts 
>                                 , let N a = cons !! c ]
>     npe (VarP (ArgP (N v))) = Var $ Arg $ digits !! v
>     npe (VarP (PatP (N v))) = Var $ Pat $ digits !! v
>     npe (AppP (ConP (N c)) (Seq es)) 
>       = App (Con (digits !! c)) (Seq (map npe es))
>     npe (AppP (RedP (N f)) (Seq es)) 
>       = App (Red (digits !! f)) (Seq (map npe es))

> instance Show ProP where
>   show = show . nameProP

Intermediate Form: Peano
========================

We have another intermediate form which uses positional naming, 
represented by lazy peano naturals.

> data Peano = Z | S Peano deriving (Show, Eq, Ord)
>
> ptake :: Peano -> [a] -> [a]
> ptake Z     _      = []
> ptake _     []     = []
> ptake (S n) (x:xs) = x : ptake n xs
>   
> pdrop :: Peano -> [a] -> [a]
> pdrop Z     xs     = xs
> pdrop _     []     = []
> pdrop (S n) (x:xs) = pdrop n xs
>
> plength :: [a] -> Peano
> plength [] = Z
> plength (_:xs) = S (plength xs)
>
> peanos :: [Peano]
> peanos = Z : map S peanos
>
> class Peanoable a where
>   peano :: a -> Peano
>   
> instance Peanoable Int where
>   peano 0 = Z
>   peano k = S $ peano $ k - 1
>   
> instance Peanoable Bool where
>   peano False = Z
>   peano True = S Z
> 
> pAdd :: Peano -> Peano -> Peano
> pAdd Z      n = n
> pAdd (S m)  n = S (pAdd m n)
> 
> pSub :: Peano -> Peano -> Peano
> pSub m      Z = m
> pSub (S m)  (S n) = pSub m n
> 
> maximumPeano :: [Peano] -> Peano
> maximumPeano (x:xs) = pAdd x (mp x xs)
>   where
>     mp high [] = Z
>     mp high (x:xs) | x <= high = mp high xs
>                    | otherwise = (x `pSub` high) `pAdd` mp x xs
         
> data ProL = ProL (Seq1 Peano) ExpL (Seq RedDefL)
>    deriving (Ord, Eq)
> 
> data RedDefL = Peano :=:: BodL   -- Function definitions
>    deriving (Ord, Eq)
> 
> data BodL = SoloL ExpL
>           | CaseL ExpL (Seq1 AltL)
>    deriving (Ord, Eq)
> 
> data ExpL = VarL VarIdL           -- Variables
>           | AppL DecIdL (Seq ExpL) -- Applications
>    deriving (Ord, Eq)
> 
> data VarIdL = ArgL Peano
>             | PatL Peano
>    deriving (Show, Ord, Eq)
> 
> data DecIdL = ConL Peano
>             | RedL Peano
>    deriving (Ord, Eq)
> 
> data AltL = Peano :-->:: ExpL    -- Case alternatives
>    deriving (Ord, Eq)

And translate this form into the previous.

> val :: Peano -> Int
> val Z = 0
> val (S n) = 1 + val n
> 
> natProL :: ProL -> ProP
> natProL (ProL (Seq1 cons) m (Seq eqns)) 
>   = ProP (Seq1 (map (N . val) cons)) (nple m) (Seq (map nplr eqns))
>   where
>     nple (VarL (ArgL v)) = VarP $ ArgP $ N $ val v
>     nple (VarL (PatL v)) = VarP $ PatP $ N $ val v
>     nple (AppL (ConL c) (Seq es)) 
>       = AppP (ConP (N $ val c)) (Seq (map nple es))
>     nple (AppL (RedL f) (Seq es)) 
>       = AppP (RedP (N $ val f)) (Seq (map nple es))
>     nplr (a :=:: b) = N (val a) :=: nplb b
>     nplb (SoloL e) = SoloP (nple e)
>     nplb (CaseL s (Seq1 alts)) 
>       = CaseP (nple s) (Seq1 [ N (val a) :-->: nple e
>                              | a :-->:: e <- alts ])
> 
> instance Show ProL where
>   show = show . nameProP . natProL

Current Representation: Non-Redundant
=====================================

Our current working representation is the non-redundant. It assumes; 

- No more than two functions. 
- Each function has an arity less-than or equal to two. 
- No more than two constructors. 
- Each constructor has an arity less-than or equal to two.
- Applications reference declarables by arity and index.
- Case alternatives reference declarables by order and pattern 
variable use.

> data ProR = ProR ExpR (Seq0'2 BodR)
>           deriving Eq
>
> data BodR = SoloR ExpR
>           | CaseR (AltR, AltR)
>           deriving (Show, Eq, Ord)
>
> data AltR = NoAltR
>           | AltR ExpR
>           deriving (Show, Eq, Ord)
>
> data ExpR = VarR VarIdR
>           | AppR DecIdR (Seq0'2 ExpR)
>           deriving (Show, Eq, Ord)
>
> data VarIdR = ArgR Bool | PatR Bool
>             deriving (Show, Eq, Ord)
>
> data DecIdR = ConR Bool | RedR Bool
>             deriving (Show, Eq, Ord)

Let us define some generic operations.

> universeR :: ExpR -> [ExpR]
> universeR e@(AppR _ (Seq0'2 es)) = e : concatMap universeR es
> universeR e = [e]
>
> expsR :: BodR -> [ExpR]
> expsR (SoloR e) = [e]
> expsR (CaseR (alts1, alts2)) = VarR (ArgR False) 
>                                : [ e | AltR e <- [alts1, alts2] ]
> 
> redsR :: ExpR -> [(Bool, Peano)]
> redsR (VarR _) = []
> redsR (AppR d (Seq0'2 es)) = [ (f, plength es) | RedR f <- [d] ]
>                              ++ concatMap redsR es
>                              
> argsR :: ExpR -> [Bool]
> argsR (VarR (ArgR v)) = [v]
> argsR (VarR (PatR _)) = []
> argsR (AppR _ (Seq0'2 es)) = concatMap argsR es
>
> consR :: ExpR -> [(Bool, Peano)]
> consR (VarR _) = []
> consR (AppR d (Seq0'2 es)) = [ (c, plength es) 
>                              | ConR c <- [d] ]
>                              ++ concatMap consR es
>
> patsR :: ExpR -> [Bool]
> patsR (VarR (ArgR _)) = []
> patsR (VarR (PatR v)) = [v]
> patsR (AppR _ (Seq0'2 es)) = concatMap patsR es

And derive the positional form from the non-redundant. We shall 
assume that all constructors must be referenced in an application but 
there are only two.

> twoDistinctBy :: (a -> a -> Bool) -> [a] -> [a]
> twoDistinctBy f [] = []
> twoDistinctBy f (x:xs) = x : case filter (not . f x) xs of
>   []    -> []
>   (y:_) -> [y]
>
> isOrdered :: (a -> a -> Bool) -> [a] -> Bool
> isOrdered f (x:y:zs) = f x y && isOrdered f (y:zs)
> isOrdered f _ = True
>
> newtype Flag a = Flag { runFlag :: (Bool, a) }
>
> instance Functor Flag where
>   fmap f (Flag (flag, x)) = Flag (flag, f x)
>
> instance Monad Flag where
>   return = Flag . (,) True
>   Flag (flag_x, x) >>= f = let Flag (flag_fx, fx) = f x
>                            in Flag (flag_x && flag_fx, fx)
>
> instance MonadPlus Flag where
>   mzero = Flag (False, error "Bad value.")
>   mplus (Flag (False, x)) = id
>   mplus (Flag (True, x)) = const $ Flag (True, x)
>
> implies :: Bool -> Bool -> Bool
> implies False _ = True
> implies True x = x
>
> conj :: Flag Bool -> Property
> conj (Flag (flag, x)) = flag |&| x
>
> mlookup :: MonadPlus m => Peano -> [a] -> m a
> mlookup _ [] = mzero
> mlookup Z (x:xs) = return x
> mlookup (S n) (x:xs) = mlookup n xs
>
> similarFirst [(c0, a0), (_, a1)] = (a0 == a1) `implies` not c0
> similarFirst _ = True
>
> deriveDatatype :: ProR -> Flag [Peano]
> deriveDatatype (ProR m (Seq0'2 eqns)) = do 
>   let twoCons = twoDistinctBy ((==) `on` fst)
>               $ concatMap consR (m : concatMap expsR eqns)
>   guard ((not.null) twoCons && similarFirst twoCons && 
>          elem False (map fst twoCons))
>   return $ map snd $ sortBy (compare `on` fst) $ twoCons
>
> deriveArity :: ProR -> Flag [Peano]
> deriveArity (ProR m (Seq0'2 eqns)) = do 
>   let twoReds = sortBy (compare `on` fst) 
>               $ twoDistinctBy ((==) `on` fst)
>               $ concatMap redsR (m : concatMap expsR eqns)
>   guard ((not.null) twoReds `implies` (not.fst.head) twoReds)
>   return $ map snd twoReds
>
> deriveProg :: ProR -> Flag ProL
> deriveProg p@(ProR m (Seq0'2 eqns)) = do      
>   dtL <- dtLM
>   mL <- deriveExpr m
>   faLM
>   eqnsL <- mapM deriveRedDef $ zip unsafe_faL eqns
>   return $ ProL (Seq1 dtL) mL (Seq eqnsL)
>     where
>       dtLM@(Flag (_, unsafe_dtL)) = deriveDatatype p
>       faLM@(Flag (_, unsafe_faL)) = deriveArity p
>       deriveExpr (VarR (ArgR x)) = return $ VarL $ ArgL $ peano x
>       deriveExpr (VarR (PatR p)) = return $ VarL $ PatL $ peano p
>       deriveExpr (AppR (ConR c) (Seq0'2 es)) = do
>         AppL (ConL $ peano c) . Seq <$> mapM deriveExpr es
>       deriveExpr (AppR (RedR f) (Seq0'2 es)) = do
>         AppL (RedL $ peano f) . Seq <$> mapM deriveExpr es
>       deriveRedDef (arity, SoloR e) = do
>         (:=::) arity . SoloL <$> deriveExpr e
>       deriveRedDef (arity, CaseR (alts1, alts2)) = do
>         guard $ (plength unsafe_dtL < S (S Z)) 
>                   `implies` (alts2 == NoAltR)
>         altsL <- sequence [ (:-->::) c <$> deriveExpr e
>                         | (c, AltR e) <- zip peanos [alts1, alts2] ]
>         return $ arity :=:: CaseL (VarL (ArgL Z)) (Seq1 altsL)

And use this to display the program.

> instance Show ProR where
>   show p@(ProR m eqns) = case runFlag (deriveProg p) of
>     (False, _) -> show $ "Invalid program: ProR (" ++ 
>                             show m ++ ") (" ++ show eqns ++ ")"
>     (True, p') -> show p'


Free generation of representation
=================================

We can generate freely over this structure but only count depth costs 
over the recursive structure ExpR.

> depth :: Int -> Int -> Int
> depth d d' | d >= 0    = d'+1-d
>            | otherwise = error "SmallCheck.depth: argument < 0"
>
> instance Serial ProR where
>    series = cons2 ProR . depth 0
> instance Serial BodR where
>    series = (cons1 SoloR \/ cons1 CaseR) . depth 0
> instance Serial ExpR where
>    series = (cons1 VarR \/ cons2 AppR)
> instance Serial VarIdR where
>    series = (cons1 ArgR \/ cons1 PatR) . depth 0
> instance Serial DecIdR where
>    series = (cons1 ConR \/ cons1 RedR) . depth 0
> instance Serial AltR where
>    series = (cons0 NoAltR \/ cons1 AltR) . depth 0

Validity
========

A program is only valid if; 
- its function applications are consistent with each other and the 
function definition,
- variables are used appropriately.

> consistentTwos :: Eq a => Maybe a -> Maybe a -> [(Bool, a)] -> Bool
> consistentTwos x y [] = True
> consistentTwos x y ((k, v):zs) 
>   | not k = maybe True (v ==) x && consistentTwos (Just v) y zs
>   | k     = maybe True (v ==) y && consistentTwos x (Just v) zs

> consistentRedApps :: ProR -> Bool
> consistentRedApps p@(ProR m (Seq0'2 eqns))
>   = consistentTwos Nothing Nothing 
>     $ concatMap redsR $ m : concatMap expsR eqns

> wellRed :: ProR -> Flag Bool
> wellRed p@(ProR _ (Seq0'2 eqns)) = do
>   arities <- deriveArity p
>   return $ plength arities == plength eqns

> consistentConApps :: ProR -> Bool
> consistentConApps p@(ProR m (Seq0'2 eqns))
>   = consistentTwos Nothing Nothing 
>     $ concatMap consR $ m : concatMap expsR eqns

> noSndAlt (CaseR (_, AltR _)) = False
> noSndAlt _ = True

> wellCon :: ProR -> Flag Bool
> wellCon p@(ProR _ (Seq0'2 eqns)) = do
>   dt <- deriveDatatype p
>   return $ (plength dt < S (S Z)) `implies`
>            all noSndAlt eqns

> wellVar :: Bool -> ExpR -> Bool
> wellVar flag (VarR (ArgR _)) = flag
> wellVar flag (VarR (PatR _)) = False
> wellVar flag (AppR _ (Seq0'2 es)) = all (wellVar flag) es

> wellCase :: BodR -> Bool
> wellCase (CaseR (NoAltR, NoAltR)) = False
> wellCase _ = True

> pvalidR :: ProR -> Property
> pvalidR p@(ProR m (Seq0'2 eqns)) 
>   = consistentRedApps p |&|
>     conj (wellRed p) |&|
>     consistentConApps p |&|
>     conj (wellCon p) |&|
>     wellVar False m |&|
>     and [ wellVar True e | SoloR e <- eqns ] |&|
>     all wellCase eqns

Principles of Canonicity
========================

Principles of ordering and use
------------------------------

We enforce sequential first use of all equation definitions, argument 
use and constructor references.

> ordConArities :: ProR -> Flag Bool
> ordConArities p = do
>   dt <- deriveDatatype p
>   return $ isOrdered (<=) dt

> ordEqns :: ProR -> Flag Bool
> ordEqns p@(ProR _ (Seq0'2 eqns)) = do
>   arities <- deriveArity p
>   return $ isOrdered (<) $ zip arities eqns

> seqArgs :: ProR -> Flag Bool
> seqArgs p@(ProR _ (Seq0'2 eqns)) = do
>   arities <- deriveArity p
>   return $ and [ (twoDistinctBy (==) $ concatMap argsR $ expsR b) 
>                  ==  ptake a [False, True]
>                | (a, b) <- zip arities eqns ]

> maxPats :: ProR -> Flag Bool
> maxPats p@(ProR _ (Seq0'2 eqns)) = do
>   dt <- deriveDatatype p
>   let (alts1, alts2) = unzip [ alts | CaseR alts <- eqns ]
>   let missingCase alts = and [ False | AltR _ <- alts ]
>   guard (and $ zipWith implies (map (const False) dt ++ repeat True)
>                (map missingCase [alts1, alts2]))
>   let maxPat alts = maximumPeano 
>                     $ Z : [ S (peano p) | AltR e <- alts
>                                         , p <- patsR e ]
>   return $ and $ zipWith (==) dt [maxPat alts1, maxPat alts2]

> seqPats :: ProR -> Flag Bool
> seqPats p@(ProR _ (Seq0'2 eqns)) = do
>   dt <- deriveDatatype p
>   return $ check dt (fstPat as) && 
>            ((not.null) dt `implies` check (tail dt) (fstPat bs))
>   where (as, bs) = unzip [ alts | CaseR alts <- eqns ]
>         fstPat alts = [ p | AltR e <- alts, p <- patsR e ]
>         check (S (S Z):_) (True:_) = False
>         check _ _ = True

> porduseR :: ProR -> Property
> porduseR p = conj (ordConArities p) |&|
>              conj (ordEqns p) |&|
>              conj (seqArgs p) |&| 
>              conj (maxPats p) |&|
>              conj (seqPats p)

Principle of Caller/Callee Demarcation
--------------------------------------

> noSoloId :: [BodR] -> Bool
> noSoloId eqns = null eqns || 
>                 head eqns /= SoloR (VarR (ArgR False))

> noRenamings :: BodR -> Bool
> noRenamings (SoloR (AppR _ (Seq0'2 es))) 
>   = or $ zipWith ((/=) . VarR . ArgR) [False,True] es
> noRenamings _ = True

> noReconsArg :: BodR -> Bool
> noReconsArg (SoloR _) = True
> noReconsArg (CaseR (alt1, alt2)) = all (noRecons' False) (universe' alt1) &&
>                                    all (noRecons' True) (universe' alt2)
>   where noRecons' :: Bool -> ExpR -> Bool
>         noRecons' c (AppR (ConR c') (Seq0'2 es))
>           | c == c' = not $ and $ zipWith (==) es 
>                        [ VarR (PatR p) | p <- [False, True] ]
>         noRecons' _ _ = True
>         universe' (AltR e) = universeR e
>         universe' _ = []

> noCaseId :: BodR -> Bool
> noCaseId (CaseR (alt1, alt2)) 
>  = any (/= x) [ e | AltR e <- [alt1, alt2] ]
>  where x = VarR (ArgR False)
> noCaseId _ = True

> noConstCase :: BodR -> Bool
> noConstCase (CaseR ( AltR (VarR (ArgR False))
>                    , AltR (AppR (ConR False) (Seq0'2 xs)))) 
>  = or $ zipWith ((/=) . VarR . PatR) [False, True] xs
> noConstCase (CaseR ( AltR (AppR (ConR True) (Seq0'2 xs))
>                    , AltR (VarR (ArgR False))))
>  = or $ zipWith ((/=) . VarR . PatR) [False, True] xs
> noConstCase (CaseR (AltR alt1, AltR alt2))
>  = alt1 /= alt2 || (not.null.patsR) alt1
> noConstCase _ = True

> isRecursive :: [BodR] -> [Bool]
> isRecursive eqns = case eqns of
>   [_,_] | mutRec -> [True, True]
>   otherwise -> selfRec
>   where reds = twoDistinctBy (==) . map fst 
>                . concatMap redsR . expsR
>         selfRec = [ f `elem` reds b
>                   | (f, b) <- zip [False,True] eqns ]
>         mutRec = and [ g `elem` reds b
>                      | (g, b) <- zip [True, False] eqns ]

> noTrivialInlineable :: ProR -> Bool
> noTrivialInlineable (ProR m (Seq0'2 eqns)) 
>   = and [ not (allCons e) && S Z < noCalls f 
>         | (f, SoloR e) <- zip [False,True] eqns ]
>   where noCalls f = plength $ filter ((==) f . fst) 
>                     $ concatMap redsR $ m : concatMap expsR eqns
>         allCons (AppR (ConR _) (Seq0'2 es)) = all allCons es
>         allCons _ = False

> noCommonCtx :: (Bool, BodR) -> Bool
> noCommonCtx (False, CaseR ( AltR (AppR d1 (Seq0'2 es1))
>                           , AltR (AppR d2 (Seq0'2 es2))))
>   | d1 == d2 = and [ (not.null.patsR) e1 
>                      || (notElem False . argsR) e1
>                      || e1 /= e2
>                    | (e1, e2) <- zip es1 es2 ]
> noCommonCtx _ = True

> binaryApps :: ExpR -> [(Bool, Bool)]
> binaryApps (AppR (ConR c) (Seq0'2 [x, y])) = (c, x /= y) : 
>                                       concatMap binaryApps [x,y]
> binaryApps _ = []

> noDupArgs :: [ExpR] -> Bool
> noDupArgs = all (any snd) . groupBy ((==) `on` fst) 
>             . sortBy (compare `on` fst) . concatMap binaryApps

> pcallerR :: ProR -> Property
> pcallerR p@(ProR m (Seq0'2 eqns)) = 
>     noSoloId eqns |&|
>     all noCaseId eqns |&|
>     all noRenamings eqns |&|
>     all noReconsArg eqns |&|
>     all noConstCase eqns |&|
>     noTrivialInlineable p |&|
>     all noCommonCtx (zip (isRecursive eqns) eqns) |&|
>     noDupArgs (m : concatMap expsR eqns)

Principle of Dead Computation
-----------------------------

> noDeadComp :: [BodR] -> Bool
> noDeadComp eqns = all st (zip [False,True] eqns)
>   where
>     redsIn f = case drop (fromEnum f) eqns of
>       []    -> []
>       (b:_) -> twoDistinctBy (==) $ map fst 
>                $ concatMap redsR $ expsR b
>     st (f, SoloR e) = ste False f e
>     st (f, e@(CaseR _)) = all (ste True f) (expsR e)
>     ste destr f (VarR _) = True
>     ste destr f (AppR (ConR _) _) = True
>     ste destr f (AppR (RedR g) (Seq0'2 es)) 
>       = (destr && or [ True | VarR (PatR _) <- es ]) ||
>         (f `notElem` g : redsIn g && all (ste destr f) es)

> pdeadCompR :: ProR -> Property
> pdeadCompR (ProR _ (Seq0'2 eqns)) = lift $ noDeadComp eqns

Principle of Dead Code
----------------------

> cheatTrace :: [BodR] -> [[Bool]]
> cheatTrace eqns = twostep
>   where onestep = map (twoDistinctBy (==) . map fst 
>                       . concatMap redsR. expsR) eqns
>         twostep = [ twoDistinctBy (==)  
>                   $ fcalls ++ (guard (g `elem` fcalls) >> gcalls)
>                   | (f, fcalls) <- zip [False, True] onestep
>                   , let g = not f
>                   , let gcalls = head $ drop (fromEnum g) onestep ]
>
> noDeadReds :: ProR -> Bool
> noDeadReds (ProR m (Seq0'2 eqns)) 
>   = plength (twoDistinctBy (==) 
>              [ (if f then tail else id) calls 
>              | (f, _) <- redsR m ])
>     == plength eqns
>   where calls = cheatTrace eqns

Trace using a big-step call-by-name semantics up to a certain 
derivation depth, counting function calls.

> data TValue = Known Bool [TThunk]
>             | UnKnown
> type TThunk = WriterT Trace Flag TValue
> type Trace = [(Bool, Maybe Bool)]
>
> bigStepTrace :: Int -> [BodR] -> [TThunk] -> [TThunk] ->
>                 Bool -> BodR -> TThunk
> bigStepTrace reds fs xs ps curf focus = case focus of
>   SoloR (VarR (ArgR x)) -> join $ mlookup (peano x) xs
>   SoloR (VarR (PatR p)) -> join $ mlookup (peano p) ps
>   SoloR (AppR (ConR c) (Seq0'2 es)) -> do
>     return $ Known c
>            $ map (bigStepTrace reds fs xs ps curf . SoloR) es
>   SoloR (AppR (RedR f) (Seq0'2 es)) ->     
>     if reds <= 0
>        then do
>          calls <- mlookup (peano f) (cheatTrace fs)
>          tell [ (g, Nothing) | g <- calls ]
>          return UnKnown
>        else do 
>          let args = map (bigStepTrace reds fs xs ps curf . SoloR) es
>          focus' <- mlookup (peano f) fs
>          bigStepTrace (reds - 1) fs args [] f focus'
>   CaseR (alt1, alt2) -> do
>     guard $ (not.null) xs
>     x <- head xs
>     case x of
>       Known c vals -> do
>         tell [(curf, Just c)]
>         let alt = if c then alt2 else alt1
>         guard (alt /= NoAltR)
>         let AltR e = alt
>         bigStepTrace reds fs xs vals curf (SoloR e)
>       UnKnown -> do
>        calls <- mlookup (peano $ curf) (cheatTrace fs)
>        tell $ (curf, Nothing) : [ (g, Nothing) | g <- calls ]
>        return UnKnown

> forceTrace :: TValue -> WriterT Trace Flag ()
> forceTrace (UnKnown) = return ()
> forceTrace (Known _ xs) = sequence_ xs

> traverseTrace :: (Bool, Bool) -> (Bool, Bool) -> Trace -> Bool
> traverseTrace (False, False) (False, False) _ = True
> traverseTrace (fA, fB) (gA, gB) [] = not $ or [fA, fB, gA, gB]
> traverseTrace (fA, fB) (gA, gB) (x:xs) = case x of
>   (x, Nothing) -> traverseTrace 
>                       (x && fA, x && fB) 
>                       (not x && gA, not x && gB) xs
>   (x, Just c) -> traverseTrace
>                       ((x || c) && fA, (x || not c) && fB) 
>                       ((not x || c) && gA, (not x || not c) && gB) xs

> noDeadAlts :: ProR -> Flag Bool
> noDeadAlts (ProR m (Seq0'2 eqns)) = do
>   ((), trace) <- runWriterT
>                 (bigStepTrace 5 eqns [] [] undefined (SoloR m) >>=
>                  forceTrace)
>   return $ traverseTrace (initial False) (initial True) trace
>   where initial f = case drop (fromEnum f) eqns of
>                       (CaseR (a, b):_) -> (a /= NoAltR, b /= NoAltR)
>                       _ -> (False, False)

> pdeadCodeR :: ProR -> Property
> pdeadCodeR p = noDeadReds p |&| conj (noDeadAlts p)

===========================

> arg x = VarR (ArgR x)
> pat x = VarR (PatR x)
> con c xs = AppR (ConR c) (Seq0'2 xs)
> red f xs = AppR (RedR f) (Seq0'2 xs)
> cas ab = CaseR ab
> pro m eqns = ProR m (Seq0'2 eqns)

> inversion = pro (red False [con False []]) 
>              [cas ( AltR $ con True []
>                   , NoAltR)]

> conjunction = pro (red False [con False [], con False []]) 
>               [cas ( AltR $ con True []
>                    , NoAltR)]

> addition = pro (red False [one, one]) 
>              [cas ( AltR $ arg True
>                   , AltR $ con True [red False [pat False, arg True]])]
>  where one = con True [con False []]

> append = pro (red False [singleton, singleton]) 
>              [cas ( AltR $ arg True
>                   , AltR $ con True [pat False, red False [pat True, arg True]])]
>  where singleton = con True [con False [], con False []]

> applen = pro (red len_ref [red app_ref [cons nil nil, nil]]) [len, app]
>  where len_ref = False
>        head_ref = True
>        cons x xs | head_ref  = con True [xs, x]
>                  | otherwise = con True [x, xs]
>        nil = con False []       
>        app_ref = not len_ref
>        tail_ref = not head_ref
>        len = cas ( AltR $ arg False
>                  , AltR $ cons nil (red len_ref [pat $ tail_ref]))
>        app = cas ( AltR $ arg True
>                  , AltR $ cons (pat head_ref) (red app_ref [pat $ tail_ref, arg True]))

> unitTests = mapM_ (depthCheck 1 . good)
>             [inversion, addition, append, applen]

===========================

> principles = [ pvalidR, porduseR, pcallerR, pdeadCompR, pdeadCodeR ]

> combine xs p = foldr1 (|&|) $ map ($ p) xs

> experiments = map combine $ tail $ inits principles

> good = combine principles

> force x = length (show x) `seq` True

> names = lines "Validity\n+ Ordering + Use\n+Caller/Callee\n+Dead Computation\n+Dead Code"

> criterion = [ bench i $
>               depthCheck 3 (\x -> pred x >=> True)
>             | (i, pred) <- zip names experiments ]    

> main = do hSetBuffering stdout NoBuffering
>           defaultMain criterion


