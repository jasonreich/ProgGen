{-# LANGUAGE DeriveDataTypeable, FlexibleInstances,
             FlexibleContexts, TypeFamilies #-}
{- |
My reimplementation of LazySmallCheck so that I could understand it. 
Interface is almost the same. For example;

> inOrder :: Ord a => [a] -> Pred
> inOrder (x:y:zs) = x <= y *&&* inOrder (y:zs)
> inOrder _ = tt
>
> noDups :: Eq a => [a] -> Pred
> noDups [] = tt
> noDups (x:ys) = x `notElem` ys *&&* noDups ys
>
> isSet :: Ord a => [a] -> Pred
> isSet xs = inOrder xs |&&| noDups xs

>>> pruneStats (isSet :: [Int] -> Pred) 5
PS {psSpace = 2278, psTests = 672, psKept = 89}
pruned = 2189
(prune / test) = 3.25

> setInsert :: Int -> [Int] -> [Int]
> setInsert x [] = [x]
> setInsert x (y:ys) | x < y  = x : y : ys
>                    | x == y = y : ys
>                    | x > y  = x : setInsert x ys

>>> depthCheck (\x xs -> isSet xs *==>* isSet (setInsert x xs)) 5
LazyCheck: Counter-example found
(-3,([-4],()))
Failure after 22 tests.
False

>>> quickCheck (\x xs -> isSet xs *==>* isSet (setInsert x xs)) 5 (Just 200)
LazyCheck: After 11 tests.
LazyCheck: Counter-example found
(2,([-4],()))
Failure covering 0.047%
False
-}
module Test.LazyCheck(
  -- * Testing properties
  -- ** Smallcheck-like
  -- | Use 'depthCheck' to find counter-examples up to a depth. It 
  -- has a funny type signature but essentially it works on any
  -- curried function resulting in a 'Bool' or a 'Pred'. Use 'test' 
  -- to iteratively deepen.
  depthCheck, test,
  -- ** Quickcheck-like
  -- | 'quickCheck' will randomly walk a depth-bounded search space
  -- either completely or for a certain number of answers. Eg.
  -- @quickCheck p d (Just n)@ will test up to depth d for n answers.
  quickCheck,
  -- * Defining properties
  Pred, (*==>*), (|&&|), (||||), (*&&*), (*||*), pneg, tt, ff, Predable(..),
  -- * Special series
  Seq(..), Seq1(..), Nat(..), Natural(..),
  -- * Constructing series
  {- | Series can be constructed almost automagically if the correct 
       Serial instances are in place. Otherwise, an algebraic 
       interface is exposed through the standard 'Applicative' and 
       'Alternative' combinators. -}
  module Control.Applicative,
  Serial(..), Series(..), drawnFrom, depth,
  cons, cons0, cons1, cons2, cons3, cons4, cons5,
  seqSeries, seq1Series,
  -- * Measuring statistics
  view, sSpace,
  -- | Use 'pruneStats' to calculate pruning statics for a predicate. It 
  -- has a funny type signature but essentially it works on any
  -- curried function resulting in a 'Bool' or a 'Pred'
  PruneSum(..), PruneStats(..), pruneStats, sample, sample', mkCtxSeries
  ) where

import Prelude hiding (catch)
import Control.Applicative
import Control.Exception
import Control.Monad
import Data.Function
import Data.IORef
import Data.List
import Data.Fixed
import Data.Typeable (Typeable)
import System.CPUTime
import System.IO
import System.IO.Unsafe
import System.Random
import System.Timeout

-- | Paths through applicative structures
type Path = [Bool]

-- | Possibly Partially Defined (PPD) term and possibly one-step expansions.
data Term a = Term { 
  tSpace  :: Integer,
  tValue  :: Path -> a,
  tExpand :: Path -> [Term a] }

instance Functor Term where
  fmap f (Term ts tv te) = Term ts (f . tv) (map (fmap f) . te)

-- | Depth bounded PPD terms
newtype Series a = Series { unSeries :: Int -> [Term a] }

instance Functor Series where
  fmap f (Series xs) = Series $ \d -> [ fmap f $ mkTerm $ dec xs d | d > 0 ]

-- | Decrease depth of series by 1
dec :: (Int -> a) -> Int -> a
dec f 0 = f 0
dec f n = f (n - 1)

-- | Apply one term to another
apply :: Term (a -> b) -> Term a -> Term b
apply f@(Term fp fv fe) x@(Term xp xv xe) 
  = Term (fp * xp) 
         (\ps -> fv (ps ++ [False]) (xv (ps ++ [True]))) 
         (\(p:ps) -> if p then map (apply f) (xe ps)
                          else map (`apply` x) (fe ps))

-- | Modify the depth of a series
depth :: (Int -> Int) -> Series a -> Series a
depth f = Series . (. f) . unSeries

-- | Custom exception for requesting expansion.
newtype Expand = Expand {exPath :: Path} deriving (Show,Typeable)
instance Exception Expand

-- | Convert a list of alternatives into one PPD term
mkTerm :: [Term a] -> Term a
mkTerm [x] = x
mkTerm xs = Term xsp (throw . Expand) $ const xs
  where xsp = foldr ((+) . tSpace) 0 xs

instance Applicative Series where
  pure x = Series $ \d -> [ Term 1 (const x) (error "Over-expanded term.") ]
  Series fs <*> Series xs = Series $ \d ->
    [ fx | d > 0, f <- fs d, let fx = f `apply` mkTerm (dec xs d), tSpace fx > 0 ]
    
instance Alternative Series where
  empty = Series $ const []
  Series xs <|> Series ys = Series $ (++) <$> xs <*> ys

class Serial a where
  -- | Generate a series of type `a`
  series :: Series a

-- | Produce a series of terms from a finite list
drawnFrom :: [a] -> [Term a]
drawnFrom xs = [ Term 1 (const x) (error "Over-expanded term.") | x <- xs]

-- | 0-arity constructors
cons, cons0 :: a -> Series a
cons = pure
cons0 = pure

-- | 1-arity constructors
cons1 :: Serial a => (a -> b) -> Series b
cons1 c = c <$> series

-- | 2-arity constructors
cons2 :: (Serial a, Serial b) => (a -> b -> c) -> Series c
cons2 c = c <$> series <*> series

-- | 3-arity constructors
cons3 :: (Serial a, Serial b, Serial c) => (a -> b -> c -> d) -> Series d
cons3 c = c <$> series <*> series <*> series

-- | 4-arity constructors
cons4 :: (Serial a, Serial b, Serial c, Serial d) 
         => (a -> b -> c -> d -> e) -> Series e
cons4 c = c <$> series <*> series <*> series <*> series

-- | 5-arity constructors
cons5 :: (Serial a, Serial b, Serial c, Serial d, Serial e)
         => (a -> b -> c -> d -> e -> f) -> Series f
cons5 c = c <$> series <*> series <*> series <*> series <*> series

-- | View a series up to a depth
view :: Show a => Series a -> Int -> IO ()
view xs = view' [] . mkTerm . unSeries xs
  where view' spaces x@(Term xp xv xe) = {- when (xp > 0) $ -} do
          putStr spaces
          res <- try (print $ xv [])
          case res of
            Left (Expand path) -> do
              putStrLn $ "⊥   … " ++ show xp ++ " possiblities."
              mapM_ (view' $ ' ':' ':spaces) (xe path)
            Right () -> return ()
            
-- | Calculate size of a space
sSpace :: Series a -> Int -> Integer
sSpace x d = sum $ map tSpace $ unSeries x d
            
-- | Print the first fully-defined term
displayFirst :: Show a => Term a -> IO Bool
displayFirst (Term _ xv xe) = do
  res <- try $ mapM evaluate $ show $ xv []
  case res of
    Left (Expand path) -> anyM displayFirst $ xe path
    Right str -> putStrLn str >> return True
    
-- | Print the all fully-defined terms
displayAll :: Show a => Term a -> IO ()
displayAll (Term _ xv xe) = do
  res <- try $ mapM evaluate $ show $ xv []
  case res of
    Left (Expand path) -> mapM_ displayAll $ xe path
    Right str -> putStrLn str

-- | Predicates including parallel composition
data Pred = Lift !Bool
          | PAnd Pred Pred
          | And  Pred Pred
          | Impl Pred Pred
          | Neg  Pred
            
class Predable a where
  -- | Make a predicate from another type
  mkPred :: a -> Pred
instance Predable Bool where mkPred = Lift  
instance Predable Pred where mkPred = id

infix 4 *==>*
infixr 3 |&&|, *&&*
infixr 2 *||*

-- | Parallel conjunction
(|&&|) :: (Predable a, Predable b) => a -> b -> Pred
x |&&| y = mkPred x `PAnd` mkPred y

-- | Parallel disjunction
(||||) :: (Predable a, Predable b) => a -> b -> Pred
x |||| y = Neg (Neg (mkPred x) `PAnd` Neg (mkPred y))

-- | Sequential conjunction
(*&&*) :: (Predable a, Predable b) => a -> b -> Pred
x *&&* y = mkPred x `And` mkPred y

-- | Sequential disjunction
(*||*) :: (Predable a, Predable b) => a -> b -> Pred
x *||* y = Neg (Neg (mkPred x) `And` Neg (mkPred y))

-- | Sequential implication
(*==>*) :: (Predable a, Predable b) => a -> b -> Pred
x *==>* y = mkPred x `Impl` mkPred y

-- | Truth
tt :: Pred
tt = Lift True

-- | Falseness
ff :: Pred
ff = Lift False

-- | Negate
pneg :: Predable a => a -> Pred
pneg = Neg . mkPred

infixl 1 >>=>
-- | Custom IO bind passing through Either a
(>>=>) :: IO (Either a b) -> (b -> IO (Either a b')) -> IO (Either a b')
x >>=> f = x >>= either (return . Left) (f >=> return)

-- | Evaluate predicates checking for undefined.
evalPred :: IO () -> Pred -> IO (Either Path Bool)
evalPred err pred = do
  res <- (Right <$> evaluate pred)
    `catches` [ Handler (\e@(Expand _) -> return (Left e))
              , Handler (\e@(ErrorCall _) -> err >> throw e >> fail "")]
  case res of
    Left (Expand path) -> return (Left path) 
    Right (Lift p) -> return (Right p)
    Right (Neg p) -> evalPred err p >>=> return . Right . not
    Right (And p q) -> evalPred err p >>=> \p' -> 
      if p' then evalPred err q else return (Right False)
    Right (Impl p q) -> evalPred err p >>=> \p' -> 
      if p' then evalPred err q else return (Right True)
    Right (PAnd p q) -> do
      pres <- evalPred err p
      case pres of
        Left lpath -> do
          qres <- evalPred err q
          case qres of
            Left rpath  -> return (Left lpath)
            Right True  -> return (Left lpath)
            Right False -> return (Right False)
        Right True  -> evalPred err q
        Right False -> return (Right False)

-- | A context, places a barrier between arguments and contexts.
data Context a b = Ctx { ctxFun :: a -> b, ctxArg :: a }

-- | For any context, extract out the result.
ctxExtract = ctxFun <*> ctxArg

instance Show a => Show (Context a b) where
  show (Ctx _ x) = show x

-- | The class of data that can be converted into contexts.
class Contextable a where
  -- | Given `a`, what is the argument type
  type CtxIn a
  -- | Given `a`, what is the result type
  type CtxOut a
  -- | Make a context out of an `a` and the argument.
  mkCtx :: a -> CtxIn a -> Context (CtxIn a) (CtxOut a)

instance Contextable Bool where
  type CtxIn  Bool = ()
  type CtxOut Bool = Pred
  mkCtx x () = Ctx (const $ Lift x) ()
  
instance Contextable Pred where
  type CtxIn  Pred = ()
  type CtxOut Pred = Pred
  mkCtx x () = Ctx (const x) ()
  
instance Contextable b => Contextable (a -> b) where
  type CtxIn  (a -> b) = (a, CtxIn b)
  type CtxOut (a -> b) = CtxOut b
  mkCtx f = Ctx $ \(x, ys) -> ctxExtract $ mkCtx (f x) ys

-- | Make a context that has a series interface.
mkCtxSeries :: (Serial (CtxIn a), Contextable a) => a -> Series (Context (CtxIn a) (CtxOut a))
mkCtxSeries f = pure (mkCtx f) <*> (Series $ unSeries series . (+1))

-- | Test predicate context terms
testPCtx :: Show a 
            => (Term (Context a Pred) -> Path -> IO o)
            -> (Term (Context a Pred) -> Bool -> IO o)
            -> Term (Context a Pred) -> IO o
testPCtx fexpand fanswer x@(Term xp xv xe) = do
  res <- 10000000 `timeout` evalPred (displayAll x) (ctxExtract $ xv [])
  maybe
    (putStrLn "" >> displayFirst x >> fail "Predicate timeout!") 
    (either (fexpand x) (fanswer x))
    res

test x = mapM_ (depthCheck x >=> flip unless (fail "")) [0..]

globLastUpdate :: IORef Integer
{-# NOINLINE globLastUpdate #-}
globLastUpdate = unsafePerformIO $ getCPUTime >>= newIORef

putStrCr :: String -> IO ()
putStrCr s = do
  lastTime <- readIORef globLastUpdate
  currentTime <- getCPUTime
  when (abs (currentTime - lastTime) > 10 ^ 10) $ do
    writeIORef globLastUpdate currentTime
    putStr (' ' : ' ' : s ++ "  \r") >> hFlush stdout

depthCheck x d = do
    (tests, result) <- test (mkTerm $ unSeries (mkCtxSeries x) d)
    putStr $ if result then "Success" else "Failure"
    putStrLn $ " after " ++ show tests ++ " tests."
    return result
  where test = testPCtx fexpand fanswer
        fexpand x path = test' (tExpand x path)
          where test' [] = return (1, True)
                test' (y:ys) = do
                  (n, p) <- test y
                  if p
                    then do (ns, ps) <- test' ys
                            let nplusns = n + ns
                            nplusns `seq` return (nplusns, ps)
                    else return (n, False)
        fanswer x False = do
          when (tSpace x == 1) 
            (putStrLn "LazyCheck: Counter-example found")
          when (tSpace x > 1) 
            (putStrLn $ "LazyCheck: Counter-example class found containing " ++ show (tSpace x) ++ ", including;")
          displayFirst x
          return (1, False)
        fanswer x True = return (1, True)

quickCheck x d n = do
    let x_term = mkTerm $ unSeries (mkCtxSeries x) d
    (sp, result) <- test (0 , [x_term])
    putStr $ if result then "Success" else "Failure"
    putStrLn $ " covering " ++ show ((fromInteger (100 * sp) / fromInteger (tSpace x_term)) :: Milli) ++ "%"
    return result
  where test (m, xs)
          | maybe False (m >=) n || null xs 
              = putStrLn ("LazyCheck: Completed " ++ show m ++ " tests.") >> return (0, True)
          | otherwise = do i <- randomRIO (0, length xs - 1)
                           let (ls, x:rs) = splitAt i xs
                           let mxs' = (m, ls ++ rs)
                           testPCtx (fexpand mxs') (fanswer mxs') x
        fexpand (m, xs) x path = test (m, xs ++ filter ((/= 0) . tSpace) (tExpand x path))
        fanswer (m, xs) x True = do
          (sp, result) <- test (m, xs)
          return (tSpace x + sp, result)
        fanswer (m, xs) x False = do
          putStrLn ("LazyCheck: After " ++ show m ++ " tests.") >> return True
          when (tSpace x == 1) 
            (putStrLn "LazyCheck: Counter-example found")
          when (tSpace x > 1) 
            (putStrLn $ "LazyCheck: Counter-example class found containing " ++ show (tSpace x) ++ ", including;")
          displayFirst x
          return (tSpace x, False)

-- Monadic `all`
allM p []     = return True
allM p (x:xs) = do
  res <- p x
  if res then allM p xs else return False

-- Monadic `any`
anyM p []     = return False
anyM p (x:xs) = do
  res <- p x
  if res then return True else anyM p xs

-- | Summarises prune statistics
data PruneSum = PS { 
  psTests :: !Integer,
  psKept  :: !Integer, 
  psPrune :: !Integer } deriving Show

newtype PruneStats = PST { unPST :: PruneSum }

instance Show PruneStats where
  show (PST ps) = show ps 
               ++ "\ntotal = " ++ show total
               ++ "\n(prune / test) = " 
               ++ show ((fromInteger (psPrune ps)
                       / fromInteger (psTests ps)) :: Centi)

   where total = psPrune ps + psKept ps

pruneStats x d = do
  testsRef <- newIORef (0 :: Integer)
  counterRef <- newIORef (0 :: Integer)
  let   term = mkTerm $ unSeries (mkCtxSeries x) d
        space = fromInteger (tSpace term)
        test x = do
          tests <- readIORef testsRef
          modifyIORef testsRef (+ 1)
          counter <- readIORef counterRef
          putStrCr $ show tests ++ "  -  "
            ++ show (fromInteger (counter * 100) / fromInteger space :: Pico) ++ "%"
          testPCtx fexpand fanswer x
        fexpand (Term xp _ xe) path = do
            unless (xp == sum (map tSpace (xe path))) (putStrLn "Not the same. ")
            foldM combine (PS 1 0 0) (filter ((/=) 0 . tSpace) (xe path))
          where combine (PS ts ks ps) x = do
                  unless (tSpace x < xp) (putStrLn "Not decreasing. ")
                  PS t k p <- test x
                  return $ PS (t + ts) (k + ks) (p + ps)
        fanswer (Term xp _ _) False = xp `seq` do
          modifyIORef counterRef (+ xp)
          return $ PS 1 0 xp
        fanswer (Term xp _ _) True = xp `seq` do
          modifyIORef counterRef (+ xp)
          return $ PS 1 xp 0
  test term

sample x d n = test (0, [mkTerm $ unSeries (mkCtxSeries x) d])
  where test (m, xs)
          | maybe False (m >=) n || null xs 
              = putStrLn ("LazyCheck: Completed " ++ show m ++ " samples.") >> return ()
          | otherwise = do let options = length xs
                           putStrCr $ show options
                           i <- randomRIO (0, options - 1)
                           let (ls, x:rs) = splitAt i xs
                           let mxs' = (m, ls ++ rs)
                           testPCtx (fexpand mxs') (fanswer mxs') x
        fexpand (m, xs) x path = test (m, xs ++ filter ((/= 0) . tSpace) (tExpand x path))
        fanswer (m, xs) x True = do
          displayAll x
          putStrLn ""
          test (1 + m, xs)
        fanswer (m, xs) x False = test (m, xs)
        
sample' x d = test (mkTerm $ unSeries (mkCtxSeries x) d)
  where
    test = testPCtx fexpand fanswer
    fexpand x path = mapM_ test (tExpand x path)
    fanswer x False = return ()
    fanswer x True = displayAll x >> putStrLn "" >> hFlush stdout

{- Default instances -}

instance Serial () where
  series = cons0 ()
  
instance (Serial a, Serial b) => Serial (a, b) where
  series = (,) <$> depth (+1) series <*> depth (+1) series

instance (Serial a, Serial b, Serial c) => Serial (a, b, c) where
  series = (,,) <$> depth (+1) series <*> depth (+1) series 
                <*> depth (+1) series
                
instance (Serial a, Serial b, Serial c, Serial d) 
         => Serial (a, b, c, d) where
  series = (,,,) <$> depth (+1) series <*> depth (+1) series 
                 <*> depth (+1) series <*> depth (+1) series
  
instance (Serial a, Serial b, Serial c, Serial d, Serial e)
         => Serial (a, b, c, d, e) where
  series = (,,,,) <$> depth (+1) series <*> depth (+1) series 
                  <*> depth (+1) series <*> depth (+1) series
                  <*> depth (+1) series
  
instance Serial a => Serial [a] where
  series = cons0 [] <|> cons2 (:)
  
-- | List where each element is of equal depth
newtype Seq a = Seq { unSeq :: [a] }
              deriving (Eq, Ord)

instance Show a => Show (Seq a) where
  show = show . unSeq
  
newtype Seq1 a = Seq1 { unSeq1 :: [a] }
              deriving (Eq, Ord)

instance Show a => Show (Seq1 a) where
  show = show . unSeq1
                       
instance Serial a => Serial (Seq a) where
  series = seqSeries id series
  
instance Serial a => Serial (Seq1 a) where
  series = seq1Series id series

seqSeries :: (Int -> Int) -> Series a -> Series (Seq a)
seqSeries seqd elemSeries = Series $ \d ->
    let elem = depth (const (d - 1)) elemSeries
        list = depth seqd $ pure [] <|> ((:) <$> elem <*> list)
    in map (fmap Seq) (unSeries list d)
       
seq1Series :: (Int -> Int) -> Series a -> Series (Seq1 a)
seq1Series seqd elemSeries = Series $ \d ->
    let elem = depth (const (d - 1)) elemSeries
        list = depth seqd $ pure [] <|> ((:) <$> elem <*> list)
    in map (fmap Seq1) (unSeries ((:) <$> elem <*> list) d)
          
instance Serial Bool where
  series = pure False <|> pure True

instance Serial Int where
  series = Series $ \d -> drawnFrom [(-d)..d]
  
instance Serial Integer where
  series = Series $ \d -> drawnFrom $ map toInteger [(-d)..d]

newtype Nat = Nat { unNat :: Int } deriving (Eq,Ord)

newtype Natural = Natural { unNatural :: Integer } deriving (Eq,Ord)

instance Show Nat where show = show . unNat
instance Show Natural where show = show . unNatural

instance Serial Nat where
  series = Series $ \d -> drawnFrom $ map Nat [0..d]
  
instance Serial Natural where
  series = Series $ \d -> drawnFrom $ map (Natural . toInteger) [0..d]

instance Serial Char where
  series = Series $ \d -> drawnFrom $ take (d + 1) ['a'..]
  
instance Serial a => Serial (Maybe a) where
  series = pure Nothing <|> cons1 Just