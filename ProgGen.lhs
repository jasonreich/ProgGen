% ProgGen, LazyCheck variant
% jason,mfn,colin
% Forked 5/12/11

> {-# LANGUAGE DeriveFunctor, DeriveDataTypeable #-}

+ > module ProgGen-LC where

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

> import Test.LazySmallCheck2012
> import Test.LazySmallCheck2012.Core (Series(..), mkProperty)

> -- import Criterion.Main
> import Control.Applicative
> import Control.Arrow
> import Control.Monad (foldM, guard, MonadPlus(..))
> import Control.Monad.Writer.Lazy hiding ((>=>), lift)
> import Data.Generics (Data, Typeable)
> import Data.Function
> import Data.List
> import Data.Maybe
> import Data.Set (Set)
> import qualified Data.Set as Set
> import System.IO
> import Debug.Trace

Small sequences
---------------

These will be useful later on.

> newtype Seq0'2 a = Seq0'2 [a] deriving (Ord,Eq, Functor, Data, Typeable)
> 
> instance Show a => Show (Seq0'2 a) where
>   show (Seq0'2 xs) = show xs
> 
> instance Serial a => Serial (Seq0'2 a) where
>   series = pure Seq0'2 `applZC` Series (\d -> runSeries (list d) 2)
>     where list d = pure [] <|> ((:) <$> (series <.> const (d - 1)) <*> list d)

Our Language
============

Our language can be represented as follows.

> newtype Id = Id Char
>   deriving (Data, Typeable)
> 
> data Pro = Pro (Seq1 ConDef) Exp (Seq RedDef)
>   deriving (Data, Typeable)
> 
> data ConDef = Id :# Nat        -- Constructor definitions
>   deriving (Data, Typeable)
> 
> data RedDef = Seq1 Id := Bod   -- Function definitions
>   deriving (Data, Typeable)
> 
> data Bod = Solo Exp
>          | Case Exp (Seq1 Alt)
>   deriving (Data, Typeable)
> data Exp = Var VarId           -- Variables
>          | App DecId (Seq Exp) -- Applications
>   deriving (Data, Typeable)
> data VarId = Arg Id
>            | Pat Id
>   deriving (Data, Typeable)
> 
> data DecId = Con Id
>            | Red Id
>   deriving (Data, Typeable)
> 
> data Alt = Seq1 Id :--> Exp    -- Case alternatives
>   deriving (Data, Typeable)

And we can have a pretty printer associated with it.

> instance Show Pro where
>   show (Pro (Seq1 cons) m (Seq eqns))
>     = unlines $ ("data D = " ++ show cons) 
>       : map show eqns ++ ["> " ++ show m ]
> 
> instance Show ConDef where
>    show (c :# Nat arity) = concat $ 
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
>  deriving (Eq, Ord, Data, Typeable)
> 
> data RedDefP = Nat :=: BodP   -- Function definitions
>  deriving (Eq, Ord, Data, Typeable, Show)
> 
> data BodP = SoloP ExpP
>           | CaseP ExpP (Seq1 AltP)
>  deriving (Eq, Ord, Data, Typeable, Show)
> 
> data ExpP = VarP VarIdP           -- Variables
>           | AppP DecIdP (Seq ExpP) -- Applications
>  deriving (Eq, Ord, Data, Typeable, Show)
> 
> data VarIdP = ArgP Nat
>             | PatP Nat
>  deriving (Eq, Ord, Data, Typeable, Show)
> 
> data DecIdP = ConP Nat
>             | RedP Nat
>  deriving (Eq, Ord, Data, Typeable, Show)
> 
> data AltP = Nat :-->: ExpP    -- Case alternatives
>  deriving (Eq, Ord, Data, Typeable, Show)

And translate this form into our original.

> nameProP :: ProP -> Pro
> nameProP prog@(ProP (Seq1 cons) m (Seq eqns)) 
>   = Pro (Seq1 (zipWith (:#) digits cons)) 
>         (npe m)
>         (Seq [ Seq1 (f : take a digits)
>                := npb e
>              | (f, Nat a :=: e) <- zip digits eqns ])
>   where
>     digits = map Id ['0'..'9']
>     npb (SoloP e) = Solo (npe e)
>     npb (CaseP s (Seq1 alts)) = Case (npe s) $ Seq1
>                                 [ Seq1 (digits !! c : take a digits)
>                                   :--> npe e
>                                 | Nat c :-->: e <- alts 
>                                 , let Nat a = cons !! c ]
>     npe (VarP (ArgP (Nat v))) = Var $ Arg $ digits !! v
>     npe (VarP (PatP (Nat v))) = Var $ Pat $ digits !! v
>     npe (AppP (ConP (Nat c)) (Seq es)) 
>       = App (Con (digits !! c)) (Seq (map npe es))
>     npe (AppP (RedP (Nat f)) (Seq es)) 
>       = App (Red (digits !! f)) (Seq (map npe es))

> instance Show ProP where
>   show = show . nameProP

> instance Serial ProP where
>    series = cons3 ProP <.> depth 0

> instance Serial RedDefP where
>    series = cons2 (:=:) <.> depth 0

> instance Serial BodP where
>    series = (cons1 SoloP <|> cons2 CaseP) <.> depth 0

> instance Serial ExpP where
>    series = cons1 VarP <|> cons2 AppP

> instance Serial VarIdP where
>    series = (cons1 ArgP <|> cons1 PatP) <.> depth 0

> instance Serial DecIdP where
>    series = (cons1 ConP <|> cons1 RedP) <.> depth 0

> instance Serial AltP where
>    series = cons2 (:-->:) <.> depth 0

> indexThen :: Nat -> [a] -> (a -> Bool) -> Bool
> indexThen (Nat i) xs f = (not.null) xs' && head xs'
>   where xs' = map f (drop i xs)

> valid :: ProP -> Bool
> valid (ProP (Seq1 cons) m (Seq eqns)) = valide (Nat 0) (Nat 0) m && all validr eqns
>  where
>    valide a _ (VarP (ArgP v))     =  a /= Nat 0 && v < a
>    valide _ p (VarP (PatP v))     =  p /= Nat 0 && v < p
>    valide a p (AppP d (Seq es))  =  bound d (length es) && all (valide a p) es

>    bound (ConP c) n  =  indexThen c cons  (\ n'         -> Nat n == n')
>    bound (RedP f) n  =  indexThen f eqns  (\(n' :=: _)  -> Nat n == n')

>    validr (a :=: (SoloP e)) = valide a (Nat 0) e
>    validr (a :=: (CaseP s (Seq1 alts))) = valide a (Nat 0) s 
>      && and  [ indexThen c cons (\p -> valide a p e) | (c :-->: e) <- alts ] 

> orderedBy f (x : y : zs) = f x y && orderedBy f (y:zs)
> orderedBy _ _ = True

> isSequence (Nat hi) = and . zipWith (==) [ Nat n | n <- [0.. hi - 1] ]

> consUse :: [Nat] -> [Nat] -> Bool
> consUse defs = aux (map (map fst) $ groupBy ((==) `on` snd) $ zipWith ((,) . Nat) [0..] defs)
>   where aux [] [] = True
>         aux _  [] = False
>         aux [] _ = False
>         aux gdefs (c:cs) = any ((==) c . head) gdefs &&
>                            aux (rem c gdefs) cs
>         rem x ((y:ys):zs) | x == y    = if null ys then zs else ys : zs
>                           | otherwise = (y:ys) : rem x zs

> fixSet :: [Set Nat] -> Set Nat -> Set Nat
> fixSet repo input | input == output = output
>                   | otherwise = fixSet repo output
>   where output = Set.unions $ input :
>                  [ repo !! i | Nat i <- Set.toList input, i < length repo ]

> redsP b = case b of
>   SoloP x -> redsPe x
>   CaseP x (Seq1 as) -> concatMap redsPe $ x : [y | _ :-->: y <- as ]
> redsPe (VarP _) = []
> redsPe (AppP d (Seq xs)) = [ f | RedP f <- [d] ] ++ concatMap redsPe xs

> consP b = case b of
>   SoloP x -> consPe x
>   CaseP x (Seq1 as) -> concat (consPe x : [ c : consPe y | c :-->: y <- as ])
> consPe (VarP _) = []
> consPe (AppP d (Seq xs)) = [ c | ConP c <- [d] ] ++ concatMap consPe xs

> argsP b = case b of
>   SoloP x -> aux x
>   CaseP x (Seq1 as) -> concatMap aux $ x : [y | _ :-->: y <- as ]
>   where aux (VarP (ArgP v)) = [v]
>         aux (VarP (PatP _)) = []
>         aux (AppP _ (Seq xs)) = concatMap aux xs

> reachable :: ExpP -> [RedDefP] -> Bool
> reachable m eqns = Set.fromList (zipWith (const . Nat) [0..] eqns) ==
>                    fixSet [ Set.fromList $ consP b | _ :=: b <- eqns ] (Set.fromList $ redsPe m)

> ordUseP :: ProP -> Property
> ordUseP (ProP (Seq1 cons) m (Seq eqns)) 
>   = orderedBy (<=) cons |&&|
>     orderedBy (<)  eqns |&&|
>     and [ orderedBy (<) [ c | c :-->: _ <- alts ] 
>         | _ :=: CaseP _ (Seq1 alts) <- eqns ] |&&|
>     and [ isSequence ar $ nub $ argsP b
>         | ar :=: b <- eqns ] |&&|
>     consUse cons (consPe m ++ concat [ consP b | _ :=: b <- eqns ]) |&&|
>     reachable m eqns

Intermediate Form: Peano
========================

We have another intermediate form which uses positional naming, 
represented by lazy peano naturals.

> data Peano = Z | S Peano deriving (Show, Eq, Data, Typeable)
>
> instance Ord Peano where
>  Z   <= _   = True
>  S _ <= Z   = False
>  S m <= S n = m <= n
>
>  _   < Z   = False
>  Z   < S _ = True
>  S m < S n = m < n
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
>    deriving (Ord, Eq, Data, Typeable)
> 
> data RedDefL = Peano :=:: BodL   -- Function definitions
>    deriving (Ord, Eq, Data, Typeable)
> 
> data BodL = SoloL ExpL
>           | CaseL ExpL (Seq1 AltL)
>    deriving (Ord, Eq, Data, Typeable)
> 
> data ExpL = VarL VarIdL           -- Variables
>           | AppL DecIdL (Seq ExpL) -- Applications
>    deriving (Ord, Eq, Data, Typeable)
> 
> data VarIdL = ArgL Peano
>             | PatL Peano
>    deriving (Show, Ord, Eq, Data, Typeable)
> 
> data DecIdL = ConL Peano
>             | RedL Peano
>    deriving (Ord, Eq, Data, Typeable)
> 
> data AltL = Peano :-->:: ExpL    -- Case alternatives
>    deriving (Ord, Eq, Data, Typeable)

And translate this form into the previous.

> val :: Peano -> Int
> val Z = 0
> val (S n) = 1 + val n
> 
> natProL :: ProL -> ProP
> natProL (ProL (Seq1 cons) m (Seq eqns)) 
>   = ProP (Seq1 (map (Nat . val) cons)) (nple m) (Seq (map nplr eqns))
>   where
>     nple (VarL (ArgL v)) = VarP $ ArgP $ Nat $ val v
>     nple (VarL (PatL v)) = VarP $ PatP $ Nat $ val v
>     nple (AppL (ConL c) (Seq es)) 
>       = AppP (ConP (Nat $ val c)) (Seq (map nple es))
>     nple (AppL (RedL f) (Seq es)) 
>       = AppP (RedP (Nat $ val f)) (Seq (map nple es))
>     nplr (a :=:: b) = Nat (val a) :=: nplb b
>     nplb (SoloL e) = SoloP (nple e)
>     nplb (CaseL s (Seq1 alts)) 
>       = CaseP (nple s) (Seq1 [ Nat (val a) :-->: nple e
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
- Case alternatives reference declarables in order.
- Functions references;
  *  in function bodies are referenced as itself (False) or the
     other function (True).
  *  in main as first (False) and second (True).

> newtype Abs = Abs {unAbs :: Bool} deriving (Show, Eq, Ord, Data, Typeable)
> newtype Rel = Rel {unRel :: Bool} deriving (Show, Eq, Ord, Data, Typeable)

> data ProR = ProR (ExpR Abs) (Seq0'2 BodR)
>           deriving (Eq, Data, Typeable)
>
> data BodR = SoloR (ExpR Rel)
>           | CaseR (AltR, AltR)
>           deriving (Show, Eq, Ord, Data, Typeable)
>
>
> data AltR = NoAltR
>           | AltR (ExpR Rel)
>           deriving (Show, Eq, Ord, Data, Typeable)
>
> data ExpR a = VarR VarIdR
>             | AppR (DecIdR a) (Seq0'2 (ExpR a))
>             deriving (Show, Eq, Ord, Functor, Data, Typeable)
>
> data VarIdR = ArgR Bool | PatR Bool
>             deriving (Show, Eq, Ord, Data, Typeable)
>
> data DecIdR a = ConR Bool | RedR a
>                 deriving (Show, Eq, Ord, Functor, Data, Typeable)

Let us define some generic operations.

> universeR :: ExpR a -> [ExpR a]
> universeR e@(AppR _ (Seq0'2 es)) = e : concatMap universeR es
> universeR e = [e]
>
> localExpsR :: ExpR Abs -> [BodR] -> [(Bool, ExpR Rel)]
> localExpsR m eqns = (False, fmap (Rel . unAbs) m) :
>                     [ (g, x) | (g, bod) <- zip [False, True] eqns
>                              , x   <- expsR bod ]
>
>
> expsR :: BodR -> [ExpR Rel]
> expsR (SoloR e) = [e]
> expsR (CaseR (alts1, alts2)) = VarR (ArgR False) 
>                                : [ e | AltR e <- [alts1, alts2] ]
> 
> redsR :: Bool -> ExpR Rel -> [(Bool, Peano)]
> redsR g (VarR _) = []
> redsR g (AppR d (Seq0'2 es)) = [ (g `xor` f, plength es) | RedR (Rel f) <- [d] ]
>                              ++ concatMap (redsR g) es
>
> argsR :: ExpR a -> [Bool]
> argsR (VarR (ArgR v)) = [v]
> argsR (VarR (PatR _)) = []
> argsR (AppR _ (Seq0'2 es)) = concatMap argsR es
>
> consR :: ExpR a -> [(Bool, Peano)]
> consR (VarR _) = []
> consR (AppR d (Seq0'2 es)) = [ (c, plength es) 
>                              | ConR c <- [d] ]
>                              ++ concatMap consR es
>
> patsR :: ExpR a -> [Bool]
> patsR (VarR (ArgR _)) = []
> patsR (VarR (PatR v)) = [v]
> patsR (AppR _ (Seq0'2 es)) = concatMap patsR es

And derive the positional form from the non-redundant. We shall 
assume that all constructors must be referenced in an application but 
there are only two.

> twoDistinct :: Eq a => [a] -> [a]
> twoDistinct = twoDistinctBy (==)

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
> xor :: Bool -> Bool -> Bool
> xor False x = x
> xor True  x = not x
>
> conj :: Flag Bool -> Property
> conj (Flag (flag, x)) = flag |&&| x
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
>               $ consR m ++ concatMap consR (concatMap expsR eqns)
>   guard ((not.null) twoCons && similarFirst twoCons && 
>          elem False (map fst twoCons))
>   return $ map snd $ sortBy (compare `on` fst) $ twoCons
>
> deriveArity :: ProR -> Flag [Peano]
> deriveArity (ProR m (Seq0'2 eqns)) = do 
>   let twoReds = sortBy (compare `on` fst) 
>               $ twoDistinctBy ((==) `on` fst)
>               $ concatMap (uncurry redsR) 
>               $ localExpsR m eqns
>   guard ((not.null) twoReds `implies` (not.fst.head) twoReds)
>   return $ map snd twoReds
>
> deriveProg :: ProR -> Flag ProL
> deriveProg p@(ProR m (Seq0'2 eqns)) = do      
>   dtL <- dtLM
>   mL <- deriveExpr False $ fmap (Rel . unAbs) m
>   faLM
>   eqnsL <- mapM deriveRedDef $ zip3 [False,True] unsafe_faL eqns
>   return $ ProL (Seq1 dtL) mL (Seq eqnsL)
>     where
>       dtLM@(Flag (_, unsafe_dtL)) = deriveDatatype p
>       faLM@(Flag (_, unsafe_faL)) = deriveArity p
>       deriveExpr _ (VarR (ArgR x)) = return $ VarL $ ArgL $ peano x
>       deriveExpr _ (VarR (PatR p)) = return $ VarL $ PatL $ peano p
>       deriveExpr g (AppR (ConR c) (Seq0'2 es)) = do
>         AppL (ConL $ peano c) . Seq <$> mapM (deriveExpr g) es
>       deriveExpr g (AppR (RedR (Rel f)) (Seq0'2 es)) = do
>         AppL (RedL $ peano $ g `xor` f) . Seq <$> mapM (deriveExpr g) es
>       deriveRedDef (g, arity, SoloR e) = do
>         (:=::) arity . SoloL <$> deriveExpr g e
>       deriveRedDef (g, arity, CaseR (alts1, alts2)) = do
>         guard $ (plength unsafe_dtL < S (S Z)) 
>                   `implies` (alts2 == NoAltR)
>         altsL <- sequence [ (:-->::) c <$> deriveExpr g e
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
>            | otherwise = error "ProgGen.depth: argument < 0"
>
> instance Serial Abs where
>    series = cons1 Abs <.> depth 0
> instance Serial Rel where
>    series = cons1 Rel <.> depth 0

> instance Serial ProR where
>    series = cons2 ProR <.> depth 0
> instance Serial BodR where
>    series = (cons1 SoloR <|> cons1 CaseR) <.> depth 0
> instance Serial a => Serial (ExpR a) where
>    series = (cons1 VarR <|> cons2 AppR)
> instance Serial VarIdR where
>    series = (cons1 ArgR <|> cons1 PatR) <.> depth 0
> instance Serial a => Serial (DecIdR a) where
>    series = (cons1 ConR <|> cons1 RedR) <.> depth 0
> instance Serial AltR where
>    series = (cons0 NoAltR <|> cons1 AltR) <.> depth 0


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
>     $ concatMap (uncurry redsR) $ localExpsR m eqns

> wellRed :: ProR -> Flag Bool
> wellRed p@(ProR _ (Seq0'2 eqns)) = do
>   arities <- deriveArity p
>   return $ plength arities == plength eqns

> consistentConApps :: ProR -> Bool
> consistentConApps p@(ProR m (Seq0'2 eqns))
>   = consistentTwos Nothing Nothing 
>     $ consR m ++ concatMap consR (concatMap expsR eqns)

> noSndAlt (CaseR (_, AltR _)) = False
> noSndAlt _ = True

> wellCon :: ProR -> Flag Bool
> wellCon p@(ProR _ (Seq0'2 eqns)) = do
>   dt <- deriveDatatype p
>   return $ (plength dt < S (S Z)) `implies`
>            all noSndAlt eqns

> wellVar :: [Peano] -> Peano -> BodR -> Bool
> wellVar cArs fAr b = case b of
>   SoloR e          -> wv Z e
>   CaseR (e_A, e_B) -> Z < fAr && (and $ zipWith wv cArs $ [ e | AltR e <- [e_A, e_B] ])
>   where wv cAr (VarR (ArgR x)) = peano x < fAr
>         wv cAr (VarR (PatR p)) = peano p < cAr
>         wv cAr (AppR _ (Seq0'2 es)) = all (wv cAr) es

> wellVarEqns :: ProR -> Flag Bool
> wellVarEqns p@(ProR _ (Seq0'2 eqns)) = do
>   fArs <- deriveArity p
>   cArs <- deriveDatatype p
>   return $ and $ zipWith (wellVar cArs) fArs eqns

> wellCase :: BodR -> Bool
> wellCase (CaseR (NoAltR, NoAltR)) = False
> wellCase _ = True

> pvalidR :: ProR -> Property
> pvalidR p@(ProR m (Seq0'2 eqns)) 
>   = consistentRedApps p |&&|
>     conj (wellRed p) |&&|
>     consistentConApps p |&&|
>     conj (wellCon p) |&&|
>     wellVar [] Z (SoloR . fmap (Rel . unAbs) $ m) |&&|
>     conj (wellVarEqns p) |&&|
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
>   return $ and [ (twoDistinct $ concatMap argsR $ expsR b) 
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
> porduseR p = conj (ordConArities p) |&&|
>              conj (ordEqns p) |&&|
>              conj (seqArgs p) |&&| 
>              conj (maxPats p) |&&|
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
>   where noRecons' :: Eq a => Bool -> ExpR a -> Bool
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
> isRecursive eqns
>   = [ (not . and) fRefs || mutRec | fRefs <- relRefs ]
>   where relRefs = map (twoDistinct . map fst .
>                        concatMap (redsR False))
>                   $ map expsR eqns
>         mutRec = all or relRefs

> isSelfRecursive :: BodR -> Bool
> isSelfRecursive = not . and . twoDistinct . map fst . 
>                   concatMap (redsR False) . expsR

> isMutRecursive :: [BodR] -> Bool
> isMutRecursive = and . map (or . twoDistinct . map fst . 
>                  concatMap (redsR False) . expsR)

Non-recursive, non-casey and no sharing.

> noTrivialInlineable :: ProR -> Bool
> noTrivialInlineable (ProR m (Seq0'2 eqns)) 
>   = and [ S Z < (plength . argsR) x
>         || isSelfRecursive b
>         | b@(SoloR x) <- eqns ]

> noCommonCtx :: (Bool, BodR) -> Bool
> noCommonCtx (rec, CaseR ( AltR (AppR d1 (Seq0'2 es1))
>                           , AltR (AppR d2 (Seq0'2 es2))))
>   | d1 == d2 = rec || and [ (not.null.patsR) e1 
>                           || (notElem False . argsR) e1
>                           || e1 /= e2
>                           | (e1, e2) <- zip es1 es2 ]
> noCommonCtx _ = True

> binaryApps :: Eq a => ExpR a -> [(Bool, Bool)]
> binaryApps (AppR (ConR c) (Seq0'2 [x, y])) = (c, x /= y) : 
>                                       concatMap binaryApps [x,y]
> binaryApps _ = []

> noDupArgs :: Eq a => [ExpR a] -> Bool
> noDupArgs = all (any snd) . groupBy ((==) `on` fst) 
>             . sortBy (compare `on` fst) . concatMap binaryApps

> pcallerR :: ProR -> Property
> pcallerR p@(ProR m (Seq0'2 eqns)) = 
>     noSoloId eqns |&&|
>     all noCaseId eqns |&&|
>     all noRenamings eqns |&&|
>     all noReconsArg eqns |&&|
>     all noConstCase eqns |&&|
>     noTrivialInlineable p |&&|
>     all noCommonCtx (zip (isRecursive eqns) eqns) |&&|
>     noDupArgs (concatMap expsR (SoloR (fmap (Rel . unAbs) m) : eqns))

Principle of Dead Computation
-----------------------------

> noDeadComp :: [BodR] -> Bool
> noDeadComp eqns = all st eqns
>   where
>     redsIn f = case drop (fromEnum f) eqns of
>       []    -> []
>       (b:_) -> twoDistinct $ map fst 
>                $ concatMap (redsR False) $ expsR b
>     st (SoloR e) = ste False e
>     st (e@(CaseR _)) = all (ste True) (expsR e)
>     ste destr (VarR _) = True
>     ste destr (AppR (ConR _) _) = True
>     ste destr (AppR (RedR (Rel f)) (Seq0'2 es)) 
>       = (destr && or [ True | VarR (PatR _) <- es ]) ||
>         (and (f : redsIn f) && all (ste destr) es)

> pdeadCompR :: ProR -> Property
> pdeadCompR (ProR _ (Seq0'2 eqns)) = mkProperty $ noDeadComp eqns

Principle of Dead Code
----------------------

> cheatTrace :: [BodR] -> [[Bool]]
> cheatTrace eqns = twostep
>   where onestep = [ (twoDistinct . map fst 
>                     . concatMap (redsR f) . expsR) x
>                   | (f, x) <- zip [False,True] eqns ]
>         twostep = [ twoDistinct  
>                   $ fcalls ++ (guard (g `elem` fcalls) >> gcalls)
>                   | (f, fcalls) <- zip [False, True] onestep
>                   , let g = not f
>                   , let gcalls = head $ drop (fromEnum g) onestep ]
>
> noDeadReds :: ProR -> Bool
> noDeadReds (ProR m (Seq0'2 eqns)) 
>   = plength (twoDistinct 
>              [ (if f then tail else id) calls 
>              | (f, _) <- redsR False $ fmap (Rel . unAbs) m ])
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
>   SoloR (AppR (RedR (Rel f_)) (Seq0'2 es)) -> let f = curf `xor` f_ in
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
>                 (bigStepTrace 5 eqns [] [] False (SoloR $ fmap (Rel . unAbs) m) >>=
>                  forceTrace)
>   return $ traverseTrace (initial False) (initial True) trace
>   where initial f = case drop (fromEnum f) eqns of
>                       (CaseR (a, b):_) -> (a /= NoAltR, b /= NoAltR)
>                       _ -> (False, False)

> pdeadCodeR :: ProR -> Property
> pdeadCodeR p = noDeadReds p |&&| conj (noDeadAlts p)

Canonicalisation
================

> {-
> bmap :: (ExpR Rel -> ExpR Rel) -> BodR -> BodR
> bmap f (SoloR e) = SoloR (f e)
> bmap f (CaseR (e0, e1)) = CaseR (amap f e0, amap f e1)

> amap :: (ExpR Rel -> ExpR Rel) -> AltR -> AltR
> amap f NoAltR   = NoAltR
> amap f (AltR e) = AltR (f e)

> alt2M :: AltR -> Maybe (ExpR Rel)
> alt2M NoAltR   = Nothing
> alt2M (AltR e) = Just e

Design choices:
- Each should be independent and require only validity.
- Repeated application should converge.

> forBac :: [a] -> [[a]]
> forBac []    = []
> forBac [x]   = [[x]]
> forBac [x,y] = [[x, y], [y, x]]

> condSwap True  [e0, e1] = Seq0'2 [e1, e0]
> condSwap _     es       = Seq0'2 es

> fOrdArg :: ProR -> ProR
> fOrdArg (ProR m (Seq0'2 eqns)) 
>   = ProR (oa isBad m) (Seq0'2 $ zipWith oab (forBac isBad) eqns)
>   where isBad = map (not . go . concatMap argsR . expsR) eqns
>           where go vs = null vs || (not . head) vs
>         oab = bmap . oa
>         oa :: [Bool] -> ExpR a -> ExpR a
>         oa isBad' (VarR (ArgR x)) = VarR (ArgR (head isBad' `xor` x))
>         oa _    (VarR (PatR p)) = VarR (PatR p)
>         oa isBad' (AppR (ConR c) (Seq0'2 es)) 
>           = AppR (ConR c) (Seq0'2 $ oa isBad' `map` es)
>         oa isBad' (AppR (RedR f) (Seq0'2 es)) 
>           = AppR (RedR f) (condSwap (isBad' !! fromEnum f) (oa isBad' `map` es))

> fUseArg :: ProR -> ProR
> fUseArg (ProR m (Seq0'2 eqns)) = ProR (ua fArity m) (Seq0'2 $ zipWith (bmap . ua) (forBac fArity) eqns)
>   where fArity = map (length . nub . concatMap argsR . expsR) eqns
>         ua fArity' (VarR v) = VarR v
>         ua fArity' (AppR (RedR f) (Seq0'2 xs)) = AppR (RedR f) (Seq0'2 $ take (fArity' !! fromEnum f) $ map (ua fArity') xs)
>         ua fArity' (AppR (ConR c) (Seq0'2 xs)) = AppR (ConR c) (Seq0'2 $ map (ua fArity') xs)

> fOrdPat :: ProR -> ProR
> fOrdPat (ProR m (Seq0'2 eqns))
>   = ProR (op False m) (Seq0'2 $ map opb eqns)
>   where (badA, badB) = (go . concat . catMaybes *** go . concat . catMaybes) $
>                        unzip [ (go' *** go') a_AB
>                              | CaseR a_AB <- eqns
>                              , let go' e = alt2M e >>= Just . patsR ]
>           where go vs = not (null vs || (not.head) vs)
>         isBad False = badA
>         isBad True = badB
>         opb (SoloR e) = SoloR (op False e)
>         opb (CaseR (e_A, e_B)) = CaseR (amap (op badA) e_A, amap (op badB) e_B)
>         op self (VarR (ArgR x)) = VarR (ArgR x)
>         op self (VarR (PatR p)) = VarR (PatR (self `xor` p))
>         op self (AppR (ConR c) (Seq0'2 es)) 
>           = AppR (ConR c) (condSwap (isBad c) (op self `map` es))
>         op self (AppR (RedR f) (Seq0'2 es)) 
>           = AppR (RedR f) (Seq0'2 $ op self `map` es)

> fUsePat :: ProR -> ProR
> fUsePat (ProR m (Seq0'2 eqns)) = ProR (up m) (Seq0'2 $ map (bmap up) eqns)
>   where (arA, arB) = (go *** go) $
>                      unzip [ (go' *** go') a_AB
>                            | CaseR a_AB <- eqns
>                            , let go' e = alt2M e >>= Just . patsR ]
>           where go = length . nub . concat . catMaybes
>         cArity False = arA
>         cArity True = arB
>         up (VarR v) = VarR v
>         up (AppR (RedR f) (Seq0'2 xs)) = AppR (RedR f) (Seq0'2 $ map up xs)
>         up (AppR (ConR c) (Seq0'2 xs)) = AppR (ConR c) (Seq0'2 $ take (cArity c) $ map up xs)

> fOrdCon :: ProR -> ProR
> fOrdCon p@(ProR m (Seq0'2 eqns)) 
>   | isBad = ProR (oc m) (Seq0'2 $ map ocb eqns)
>   | True  = ProR m (Seq0'2 eqns)
>   where isBad = not $ uncurry (&&) $ runFlag $ ordConArities p
>         ocb (SoloR e) = SoloR (oc e)
>         ocb (CaseR (e_A, e_B)) = CaseR (amap oc e_B, amap oc e_A)
>         oc (VarR v) = VarR v
>         oc (AppR (ConR c) (Seq0'2 es)) = AppR (ConR $ not c) (Seq0'2 $ map oc es)
>         oc (AppR (RedR f) (Seq0'2 es)) = AppR (RedR f) (Seq0'2 $ map oc es)

> fOrdEqn :: ProR -> ProR
> fOrdEqn p@(ProR m (Seq0'2 eqns)) 
>   | isBad = ProR (oe m) (condSwap True $ eqns)
>   | True  = ProR m (Seq0'2 eqns)
>   where isBad = not $ uncurry (&&) $ runFlag $ ordEqns p
>         oe (VarR v) = VarR v
>         oe (AppR (ConR c) (Seq0'2 es)) = AppR (ConR c) (Seq0'2 $ map oe es)
>         oe (AppR (RedR f) (Seq0'2 es)) = AppR (RedR $ not f) (Seq0'2 $ map oe es)

> fNeqEqn :: ProR -> ProR
> fNeqEqn p@(ProR m (Seq0'2 [b0, b1])) 
>   | isBad = ProR (ne m) (Seq0'2 [bmap ne b0])
>   where isBad = b0 == b1
>         ne (VarR v) = VarR v
>         ne (AppR (ConR c) (Seq0'2 es)) = AppR (ConR c) (Seq0'2 $ map ne es)
>         ne (AppR (RedR f) (Seq0'2 es)) = AppR (RedR $ False) (Seq0'2 $ map ne es)
> fNeqEqn p = p

> forduseR = fNeqEqn . fOrdEqn . fOrdCon . fUsePat . fOrdPat . fUseArg . fUsePat
> prop_forduseR_can p = pvalidR p *==>* (pvalidR p' *==>* porduseR p')
>   where p' = forduseR $ p
> prop_forduseR_ide p = (pvalidR p |&&| porduseR p) *==>* (p == p')
>   where p' = forduseR $ p

> fSoloId :: ProR -> ProR
> fSoloId (ProR m (Seq0'2 eqns)) = ProR (si m) (Seq0'2 eqns')
>   where isBad = map (== SoloR (VarR (ArgR False))) eqns
>         eqns' = map (bmap si . snd) $ filter (not . fst) $ zip isBad eqns
>         si (AppR (RedR f) (Seq0'2 [x])) | f && or isBad = si x
>         si (AppR d (Seq0'2 es)) = AppR d (Seq0'2 $ map si es)
>         si x = x

> fRenamings :: ProR -> ProR
> fRenamings (ProR m (Seq0'2 eqns)) = ProR (rn m) (Seq0'2 $ map (bmap rn) eqns)
>   where isBad = map go eqns
>         go (SoloR (AppR d (Seq0'2 es))) 
>           | or $ zipWith ((/=) . VarR . ArgR) [False,True] es
>           = Just d
>         go _ = Nothing
>         rn (AppR (RedR f) (Seq0'2 es)) = AppR (RedR f `fromMaybe` (isBad !! fromEnum f)) (Seq0'2 $ map rn es)
>         rn (AppR d (Seq0'2 es)) = AppR d (Seq0'2 $ map rn es)
>         rn x = x

> fReconsArgs :: ProR -> ProR
> fReconsArgs (ProR m (Seq0'2 eqns)) = ProR m (Seq0'2 $ map rab eqns)
>   where rab (SoloR e) = SoloR e
>         rab (CaseR (e_A, e_B)) = CaseR (amap (ra False) e_A, amap (ra True) e_B)
>         ra c' (AppR (ConR c) (Seq0'2 es)) 
>           | c == c' && and (zipWith ((==) . VarR . PatR) [False,True] es) 
>           = VarR (ArgR False)
>         ra c' (AppR d (Seq0'2 es)) = AppR d (Seq0'2 $ map (ra c') es)
>         ra _ x = x

> fCaseId :: ProR -> ProR
> fCaseId (ProR m (Seq0'2 eqns)) = ProR (ci m) (Seq0'2 eqns')
>   where isBad = map go eqns
>         go (CaseR (a_A, a_B)) = go' a_A && go' a_B
>         go _ = False
>         go' (AltR (VarR (ArgR False))) = True
>         go' (AltR _) = False
>         go' _ = True
>         eqns' = map (bmap ci . snd) $ filter (not . fst) $ zip isBad eqns
>         ci (AppR (RedR True) (Seq0'2 [x])) | or isBad = ci x
>         ci (AppR d (Seq0'2 es)) = AppR d (Seq0'2 $ map ci es)
>         ci x = x

> fCaseConst :: ProR -> ProR
> fCaseConst (ProR m (Seq0'2 eqns)) = ProR m (Seq0'2 $ map cc eqns)
>   where cc (CaseR (AltR x_A, AltR x_B)) 
>           | x_A == x_B && null (patsR x_A) = SoloR x_A
>           | x_A == arg False && x_B == con False [] = SoloR x_B
>           | x_B == arg False && x_A == con True [] = SoloR x_A
>         cc b = b

> {- fInlineTrivial :: ProR -> ProR
> fInlineTrivial (ProR m (Seq0'2 eqns)) 
>   = ProR (inl isBad m) (Seq0'2 $ zipWith inl (forBac isBad) eqns)
>   where isBad = zipWith go (isRecursive eqns) eqns
>         go False (SoloR x) | (plength . argsR) x < S (S Z) = Just x
>         go _ _ = Nothing
>         inl sub (AppR (RedR f) (Seq0'2 es)) = undefined
>         inl sub (AppR d (Seq0'2 es)) = AppR d (Seq0'2 $ map (inl sub) es)
>         inl sub x = x -}

> fcallerR = fCaseConst . fCaseId . fReconsArgs . fRenamings . fSoloId
> prop_fcallerR_can p = pvalidR p *==>* (pvalidR p' *==>* pcallerR p')
>   where p' = fcallerR $ p
> prop_fcallerR_ide p = (pvalidR p |&&| pcallerR p) *==>* (p == p')
>   where p' = fcallerR $ p
> -}

===========================

> arg x = VarR (ArgR x)
> pat x = VarR (PatR x)
> con c xs = AppR (ConR c) (Seq0'2 xs)
> red f xs = AppR (RedR f) (Seq0'2 xs)
> f0 xs = AppR (RedR $ Abs False) (Seq0'2 xs)
> f1 xs = AppR (RedR $ Abs True) (Seq0'2 xs)
> rec xs = AppR (RedR $ Rel False) (Seq0'2 xs)
> oth xs = AppR (RedR $ Rel True) (Seq0'2 xs)
> cas ab = CaseR ab
> pro m eqns = ProR m (Seq0'2 eqns)

> inversion = pro (f0 [con False []]) 
>              [cas ( AltR $ con True []
>                   , NoAltR)]

> conjunction = pro (f0 [con False [], (f0 [con True [], con False []])])
>               [cas ( AltR $ arg True
>                    , AltR $ arg False )]

> addition = pro (f0 [one, one]) 
>              [cas ( AltR $ arg True
>                   , AltR $ con True [rec [pat False, arg True]])]
>  where one = con True [con False []]

> append = pro (f0 [singleton, singleton]) 
>              [cas ( AltR $ arg True
>                   , AltR $ con True [pat False, rec [pat True, arg True]])]
>  where singleton = con True [con False [], con False []]

> applen = pro (red (Abs len_ref) [red (Abs app_ref) [cons nil nil, nil]]) [len, app]
>  where len_ref = False
>        head_ref = True
>        cons x xs | head_ref  = con True [xs, x]
>                  | otherwise = con True [x, xs]
>        nil = con False []       
>        app_ref = not len_ref
>        tail_ref = not head_ref
>        len = cas ( AltR $ arg False
>                  , AltR $ cons nil (rec [pat $ tail_ref]))
>        app = cas ( AltR $ arg True
>                  , AltR $ cons (pat head_ref) (rec [pat $ tail_ref, arg True]))

> unitTests = mapM_ (depthCheck 1 . good)
>             [inversion, conjunction, addition, append, applen]

===========================

> principles = [ pvalidR, porduseR, pcallerR, pdeadCompR, pdeadCodeR ]

> combine xs p = foldr1 (|&&|) $ map ($ p) xs

> experiments = map combine $ tail $ inits principles

> good = combine principles

> force x = length (show x) `seq` True

> names = lines "Validity\n+ Ordering + Use\n+Caller/Callee\n+Dead Computation\n+Dead Code"

> stats = sequence_ [ do putStrLn i
>                        pruneStats 3 pred
>                   | (i, pred) <- zip names experiments ]    

> criterion = undefined {- [ bench i $
>               depthCheck 3 (\x -> pred x *==>* True)
>             | (i, pred) <- zip names experiments ]  -}

>
> section =  do putStrLn "\nValid, original, 2"
>               pruneStats 2 $ valid
>               putStrLn "\nOrdUse, original, 2"
>               pruneStats 2 $ (\x -> valid x |&&| ordUseP x)
>               putStrLn "\nOrdUse, original, 3"
>               pruneStats 3 $ (\x -> valid x |&&| ordUseP x)
>               putStrLn "\nOrdUse, Non-redundant, 3"
>               pruneStats 3 $ (experiments !! 2)
>               putStrLn "\nOrdUse, Non-redundant, 4"
>               pruneStats 4 $ (experiments !! 2)
>               putStrLn "\nDead Comp, Non-redundant, 3"
>               pruneStats 3 $ (experiments !! 3)
>               putStrLn "\nDead Comp, Non-redundant, 4"
>               pruneStats 4 $ (experiments !! 3)
>               putStrLn "\nDead Code, Non-redundant, 3"
>               pruneStats 3 $ (experiments !! 4)
>               putStrLn "\nDead Code, Non-redundant, 4"
>               pruneStats 4 $ (experiments !! 4)

> data Tests = Section_Stats
>            | Perform_Stats
>            | Perform_Exec
>            | Sample Int

> main = do hSetBuffering stdout NoBuffering
>           case Section_Stats of
>             Section_Stats -> section
>             Perform_Stats -> stats
>             Perform_Exec  -> undefined -- defaultMain criterion
>             -- Sample d      -> sample' good d