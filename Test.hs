{-# LANGUAGE MagicHash, FlexibleContexts, BlockArguments, LambdaCase, DeriveGeneric, DeriveAnyClass, MultiParamTypeClasses, TypeFamilies, PatternSynonyms, ViewPatterns, UndecidableInstances, TypeApplications, ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}

module Test where

import Data.Array.Accelerate as A
import Data.Array.Accelerate.Data.Either
import Data.Array.Accelerate.Data.Maybe
-- import Data.Array.Accelerate.Smart (match)

import Data.Array.Accelerate.Interpreter
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.Smart
import Data.Array.Accelerate.Product

main :: IO ()
main = do
  let
    -- exprs = fromList (Z :. 2) [Left (Left 1), Right ()] :: Vector (Either (Either Int Int) ())

  -- print (A.map fn $ use exprs)
  -- print . run $ A.map fn $ use exprs
  -- print (match f)
  print . run $ A.map hybrid2 hybrid2s


printVary :: Elt t => Exp t -> IO ()
printVary x = case vary x of
  Nothing -> print "No variants"
  Just (m, vs) -> do
    putStrLn "------"
    print m
    putStrLn "---"
    mapM_ (\(t, e) -> print t >> print e >> putStrLn "---") vs
    putStrLn "------"


-- fn :: Exp (Either (Either Int Int) ()) -> Exp Int
-- fn = match go
--   where
--     go (Left_  x) = switch x \case
--       Left_  y -> 2 + y
--       Right_ y -> 3 + y
--     go (Right_ _) = 0
--     -- go _ = 5

fn2 :: Exp (Either (Either Int Int) ()) -> Exp Int
fn2 = match go
  where
    go (Left_  x) = case x of
      Left_  y -> 2 + y
      Right_ y -> 3 + y
    go (Right_ _) = 0

-- x = match g (if ... then Left_ (Left 0) else Right_ ())

-- switch = flip match

-- (&) = flip ($)

h :: Exp (Either Int Int) -> Exp (Either () ()) -> Exp Int
h (Left_  _) (Left_  _) = 0
h (Left_  _) (Right_ _) = 1
h (Right_ _) (Left_  _) = 2
h (Right_ _) (Right_ _) = 3

k :: Exp (Either Int Int) -> Exp Int -> Exp (Either () ()) -> Exp Int
k (Left_  _) n (Left_  _) = n + 0
k (Left_  _) n (Right_ _) = n + 1
k (Right_ _) n (Left_  _) = n + 2
k (Right_ _) n (Right_ _) = n + 3

f :: Exp (Either (Either Int Int) ())
  -> Exp Int
  -> Exp (Either (Either () ()) (Either () ()))
  -> Exp Int
f (Left_ (Left_  n)) m (Left_  _) = 0 + n + m
f (Left_ (Right_ n)) m (Left_  _) = 1 + n + m
f (Right_ _        ) m (Left_  _) = 2     + m
f (Left_ (Left_  n)) m (Right_ _) = 3 + n + m
f (Left_ (Right_ n)) m (Right_ _) = 4 + n + m
f (Right_ _        ) m (Right_ _) = 5     + m
f _ _ (Left_ _) = 6
f _ _ (Right_ _) = 7

g :: Exp (Either (Either Int Int) ())
  -> Exp Int
g (Left_ (Left_  _n)) = 0
g (Left_ (Right_ _n)) = 1
g (Right_ _         ) = 2

may :: Exp (Maybe Int) -> Exp Int
may (Just_ n) = n
may Nothing_  = 0
may _         = 100

two :: Exp (Duo Int Int) -> Exp Int
two (Duo_ n m) = n + m

tw :: Exp (Duo (Either Int Int) Int) -> Exp Int
tw (Duo_ (Left_  n) m) = n + m
tw (Duo_ (Right_ n) m) = n - m

wo :: Exp (Either (Duo Int Int) Int) -> Exp Int
wo (Left_  (Duo_ n m)) = n + m
wo (Right_ n         ) = n


data Duo a b = Duo a b
  deriving (Show, Generic, IsProduct Elt)


unduo :: (Elt a, Elt b) => Exp (Duo a b) -> (Exp a, Exp b)
unduo (Exp (Match (Exp (Tuple (NilTup `SnocTup` x1 `SnocTup` x2))) _)) = (x1, x2)
unduo x = (Exp $ SuccTupIdx ZeroTupIdx `Prj` x, Exp $ ZeroTupIdx `Prj` x)

mkDuo :: (Elt a, Elt b) => Exp a -> Exp b -> Exp (Duo a b)
mkDuo x1 x2 = Exp . Tuple $ NilTup `SnocTup` x1 `SnocTup` x2

instance (Elt a, Elt b) => Elt (Duo a b) where
  vary x =
    let
      (x1, x2 ) = unduo x
      (m1, vs1) = go x1
      (m2, vs2) = go x2
    in
      Just ( Mask 1 [VarMask 2 [m1, m2]]
           , [ ( TagIx 0 [t1, t2]
               , Exp $ Match (mkDuo x1' x2') (TagIx 0 [t1, t2])
               )
             | (t1, x1') <- vs1
             , (t2, x2') <- vs2
             ]
           )
    where
      go e = case vary e of
        Just (m, vs) -> (m, vs)
        Nothing      -> (Mask 1 [], [(TagIx 0 [], e)])

{-# COMPLETE Duo_ #-}
pattern Duo_ :: (Elt a, Elt b) => Exp a -> Exp b -> Exp (Duo a b)
pattern Duo_ x1 x2 <- (unduo -> (x1, x2))
  where
    Duo_ = mkDuo

data Hybrid a b c = Zero | One a | Two b c
  deriving (Show, Generic)

instance (Elt a, Elt b, Elt c) => IsProduct Elt (Hybrid a b c) where
  type ProdRepr (Hybrid a b c) = ProdRepr (Word8, a, b, c)
  toProd (((((), 0), _a), _b), _c) = Zero
  toProd (((((), 1),  a), _b), _c) = One a
  toProd (((((), _), _a),  b),  c) = Two b c
  fromProd  Zero     = (((((), 0), evalUndef @a), evalUndef @b), evalUndef @c)
  fromProd (One a  ) = (((((), 1),            a), evalUndef @b), evalUndef @c)
  fromProd (Two b c) = (((((), 2), evalUndef @a),            b),            c)
  prod = prod @Elt @(Word8, a, b, c)


instance (Elt a, Elt b, Elt c) => Elt (Hybrid a b c) where
  type EltRepr (Hybrid a b c) = TupleRepr (Word8, EltRepr a, EltRepr b, EltRepr c)
  eltType = eltType @(Word8, a, b, c)
  toElt (((((), 0), _a), _b), _c) = Zero
  toElt (((((), n),  a), _b), _c) | n Prelude.<= maskN @a = One (toElt a)
  toElt (((((), _), _a),  b),  c) = Two (toElt b) (toElt c)
  fromElt  Zero     = (((((), 0), fromElt (evalUndef @a)), fromElt (evalUndef @b)), fromElt (evalUndef @c))
  fromElt (One a  ) = let x = fromElt a
                      in (((((), 1 + varElt @a x), x), fromElt (evalUndef @b)), fromElt (evalUndef @c))
  fromElt (Two b c) = let y = fromElt b
                          z = fromElt c
                      in (((((), 1 + maskN @a + varElt @b y * maskN @c + varElt @c z), fromElt (evalUndef @a)), y), z)
  --
  varElt (((((), n), _), _), _) = n
  vary x = Just $ ( Mask 3 [VarMask 0 [], VarMask 1 [m_a], VarMask 2 [m_b, m_c]]
                  , concat [h0, h1, h2]
                  )
    where
      (b, c) = fromHybrid2 x
      (m_a, vs_a) = varied (fromHybrid1 x)
      (m_b, vs_b) = varied b
      (m_c, vs_c) = varied c
      h0 = [tagged 0 [] (mkHybrid0 @a @b @c)]
      h1 = [tagged 1 [t_a] (mkHybrid1 @a @b @c a') | (t_a, a') <- vs_a]
      h2 = [tagged 2 [t_b, t_c] (mkHybrid2 @a @b @c b' c') | (t_b, b') <- vs_b, (t_c, c') <- vs_c]

mkHybrid0 :: (Elt a, Elt b, Elt c) => Exp (Hybrid a b c)
mkHybrid0 = Exp . Tuple $ NilTup `SnocTup` constant 0 `SnocTup` undef `SnocTup` undef `SnocTup` undef

mkHybrid1 :: (Elt a, Elt b, Elt c) => Exp a -> Exp (Hybrid a b c)
mkHybrid1 a = Exp . Tuple $ NilTup `SnocTup` constant 1 `SnocTup` a `SnocTup` undef `SnocTup` undef

mkHybrid2 :: (Elt a, Elt b, Elt c) => Exp b -> Exp c -> Exp (Hybrid a b c)
mkHybrid2 b c = Exp . Tuple $ NilTup `SnocTup` constant 2 `SnocTup` undef `SnocTup` b `SnocTup` c

unHybrid0 :: (Elt a, Elt b, Elt c) => Exp (Hybrid a b c) -> Bool
unHybrid0 (Exp (Match _ (TagIx 0 _))) = True
unHybrid0 _                           = False

unHybrid1 :: (Elt a, Elt b, Elt c) => Exp (Hybrid a b c) -> Maybe (Exp a)
unHybrid1 (Exp (Match (Exp (Tuple (NilTup `SnocTup` _tag `SnocTup` a `SnocTup` _b `SnocTup` _c))) (TagIx 1 _))) = Just a
unHybrid1 (Exp (Match x (TagIx 1 _))) = Just (fromHybrid1 x)
unHybrid1 _ = Nothing

unHybrid2 :: (Elt a, Elt b, Elt c) => Exp (Hybrid a b c) -> Maybe (Exp b, Exp c)
unHybrid2 (Exp (Match (Exp (Tuple (NilTup `SnocTup` _tag `SnocTup` _a `SnocTup` b `SnocTup` c))) (TagIx 2 _))) = Just (b, c)
unHybrid2 (Exp (Match x (TagIx 1 _))) = Just (fromHybrid2 x)
unHybrid2 _ = Nothing

fromHybrid1 :: (Elt a, Elt b, Elt c) => Exp (Hybrid a b c) -> Exp a
fromHybrid1 x = Exp ((SuccTupIdx $ SuccTupIdx $ ZeroTupIdx) `Prj` x)

fromHybrid2 :: (Elt a, Elt b, Elt c) => Exp (Hybrid a b c) -> (Exp b, Exp c)
fromHybrid2 x = (Exp ((SuccTupIdx ZeroTupIdx) `Prj` x), Exp (ZeroTupIdx `Prj` x))

{-# COMPLETE Zero_, One_, Two_ #-}

pattern Zero_ :: (Elt a, Elt b, Elt c) => Exp (Hybrid a b c)
pattern Zero_ <- (unHybrid0 -> True)
  where
    Zero_ = mkHybrid0

pattern One_ :: (Elt a, Elt b, Elt c) => Exp a -> Exp (Hybrid a b c)
pattern One_ a <- (unHybrid1 -> Just a)
  where
    One_ = mkHybrid1

pattern Two_ :: (Elt a, Elt b, Elt c) => Exp b -> Exp c -> Exp (Hybrid a b c)
pattern Two_ b c <- (unHybrid2 -> Just (b, c))
  where
    Two_ = mkHybrid2


hybrid0 :: Exp (Hybrid Int Int Int) -> Exp Int
hybrid0  Zero_   = 0
hybrid0 (One_ a) = 1 + a
hybrid0 (Two_ b c) = 2 + b + c

hybrid1 :: Exp (Hybrid Int Int Int) -> Exp (Hybrid Int Int Int) -> Exp Int
hybrid1 Zero_ Zero_ = 0 + 0
hybrid1 Zero_ (One_ a) = 0 + 1 + a
hybrid1 Zero_ (Two_ b c) = 0 + 2 + b + c
hybrid1 _ _ = 100

hybrid2 :: Exp (Either (Hybrid Int Int Int) ()) -> Exp Int
hybrid2 (Left_ Zero_) = 0 + 0
hybrid2 (Left_ (One_ a)) = 0 + 1 + a
hybrid2 (Left_ (Two_ b c)) = 0 + 1 + b + c
hybrid2 (Right_ _) = 1

hybrid2s :: Acc (Vector (Either (Hybrid Int Int Int) ()))
hybrid2s = use $ fromList (Z :. 4) [Left Zero, Left (One 1), Left (Two 2 3), Right ()]

f100 :: Exp (Either (Either Int Int) ()) -> Exp Int
f100 = match go
  where
    go (Left_ x) = g100 x + 1
    go _         = 100

g100 :: Exp (Either Int Int) -> Exp Int
g100 = match go
  where
    go (Left_ _) = 0
    go (Right_ _) = 1

-- *Test> f100
-- \x0 ->
--   Jump:
--   (Mask 2 [ Mask 2 [  ] [  ] ] [  ])
--   (x0)
--   [
--   (Tag 0 [ Tag 0 [ ] ]
--   ->
--   Jump:
--   (Mask 2 [  ] [  ])
--   (Match: (Tag 0 [ ]) -> x0 # 1)
--   [
--   (Tag 0 [ ] -> 0) , (Tag 1 [ ] -> 1)
--   ]
--   + 1)
--   ,
--   (Tag 0 [ Tag 1 [ ] ]
--   ->
--   Jump:
--   (Mask 2 [  ] [  ])
--   (Match: (Tag 1 [ ]) -> x0 # 1)
--   [
--   (Tag 0 [ ] -> 0) , (Tag 1 [ ] -> 1)
--   ]
--   + 1)
--   ,
--   (Tag 1 [ ] -> 100)
--   ]
-- *Test>

-- *Test> f100
-- \x0 ->
--   Jump:
--   (Mask 2 [ Mask 2 [  ] [  ] ] [  ])
--   (x0)
--   [
--   (Tag 0 [ Tag 0 [ ] ] -> 0 + 1)
--   ,
--   (Tag 0 [ Tag 1 [ ] ] -> 1 + 1)
--   ,
--   (Tag 1 [ ] -> 100)
--   ]
-- *Test>
