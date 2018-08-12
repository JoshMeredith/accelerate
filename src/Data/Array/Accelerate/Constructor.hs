{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE ViewPatterns          #-}
-- |
-- Module      : Data.Array.Accelerate.Constructor
-- Copyright   : [2018..2018] Joshua Meredith, Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Constructor (

  pattern MkT,

  pattern E2 , pattern E3 , pattern E4 , pattern E5 ,
  pattern E6 , pattern E7 , pattern E8 , pattern E9 , pattern E10,
  pattern E11, pattern E12, pattern E13, pattern E14, pattern E15,

  pattern A2 , pattern A3 , pattern A4 , pattern A5 ,
  pattern A6 , pattern A7 , pattern A8 , pattern A9 , pattern A10,
  pattern A11, pattern A12, pattern A13, pattern A14, pattern A15

) where

import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.Product
import Data.Array.Accelerate.Smart

import Language.Haskell.TH hiding (Exp)


-- | This pattern synonym can be used as an alternative to 'lift' and 'unlift'
-- for creating and accessing data types isomorphic to simple product (tuple)
-- types.
--
-- For example, let's say we have regular Haskell data type representing a point
-- in two-dimensional space:
--
-- > data Point = Point_ Float Float
-- >   deriving (Show, Generic, Elt, IsTuple)
--
-- Note that we derive instances for the 'Elt' class, so that this data type can
-- be used within Accelerate scalar expressions, and 'IsTuple', as this is
-- a product type (contains multiple values).
--
-- In order to access the individual fields of the data constructor from within
-- an Accelerate expression, we define the following pattern synonym:
--
-- > pattern Point :: Exp Float -> Exp Float -> Exp Point
-- > pattern Point x y = MkT (x,y)
--
-- In essence, the 'MkT' pattern is really telling GHC how to treat our @Point@
-- type as a regular pair for use in Accelerate code. The pattern can then be
-- used on both the left and right hand side of an expression:
--
-- > addPoint :: Exp Point -> Exp Point -> Exp Point
-- > addPoint (Point x1 y1) (Point x2 y2) = Point (x1+x2) (y1+y2)
--
-- Similarly, we can define pattern synonyms for values in 'Acc'. We can also
-- use record syntax to generate field accessors, if we desire:
--
-- > data SparseVector a = SparseVector_ (Vector Int) (Vector a)
-- >   deriving (Show, Generic, Arrays, IsAtuple)
-- >
-- > pattern SparseVector :: Elt a => Acc (Vector Int) -> Acc (Vector a) -> Acc (SparseVector a)
-- > pattern SparseVector { indices, values } = MkT (indices, values)
--
pattern MkT :: forall tup a context. MkData context a tup => tup -> context a
pattern MkT vars <- (destruct @context -> vars)
  where MkT = construct @context

class MkData con a t where
  construct :: t -> con a
  destruct  :: con a -> t

$(runQ $ do
    let
      genData :: Int -> TypeQ -> ExpQ -> TypeQ -> ExpQ -> ExpQ -> ExpQ -> ExpQ -> Q Dec
      genData n cst tpl conT con prj nil snc = do

        let
          t   = return . VarT $ mkName "t"
          vs  = map mkName . map (:[]) $ take n "abcdefghijklmno"
          x   = mkName "x"
          ts  = map VarT vs

          prodReprN = foldl (\acc a -> [t| ($acc, $(return a)) |]) [t| () |] ts

        eqRepr    <- [t| ProdRepr $t ~ $prodReprN |]
        isProduct <- [t| IsProduct $cst $t |]

        cst'      <- cst
        conT'     <- conT
        t'        <- t

        let
          tut | [x] <- ts = [t| $conT $(return x) |]
              | otherwise = return $ foldl (\acc x -> AppT acc (AppT conT' x)) (TupleT n) ts

          tup      = TupP $ map VarP vs
          snoc x y = [| $snc $x $(return $ VarE y) |]

          tupidx 1 = [| ZeroTupIdx |]
          tupidx n = [| SuccTupIdx $(tupidx (n - 1)) |]
          prjN   n = [| $con $ $prj $(tupidx n) $(return $ VarE x) |]

          cxt = isProduct : eqRepr : map (AppT cst') (t':ts)

        typ    <- [t| MkData $conT $t $tut |]
        constr <- [| $con $ $tpl $ $(foldl snoc nil vs) |]
        destr  <- TupE <$> mapM prjN [n,n-1..1]

        return $ InstanceD Nothing cxt typ
          [ FunD 'construct [Clause [tup   ] (NormalB constr) []]
          , FunD 'destruct  [Clause [VarP x] (NormalB destr ) []]
          ]

      genDataExp :: Int -> Q Dec
      genDataExp n = genData n [t|Elt|] [|Tuple|] [t|Exp|] [|Exp|] [|Prj|] [|NilTup|] [|SnocTup|]

      genDataAcc :: Int -> Q Dec
      genDataAcc n = genData n [t|Arrays|] [|Atuple|] [t|Acc|] [|Acc|] [|Aprj|] [|NilAtup|] [|SnocAtup|]

    exps <- mapM genDataExp [1..15]
    accs <- mapM genDataAcc [1..15]

    return $ exps ++ accs
 )


-- | Specialised pattern synonyms for tuples in @Exp@.
--
pattern E2
  :: (Elt a, Elt b)
  => Exp a -> Exp b
  -> Exp (a, b)
pattern E2 a b = MkT (a, b)

pattern E3
  :: (Elt a, Elt b, Elt c)
  => Exp a -> Exp b -> Exp c
  -> Exp (a, b, c)
pattern E3 a b c = MkT (a, b, c)

pattern E4
  :: (Elt a, Elt b, Elt c, Elt d)
  => Exp a -> Exp b -> Exp c -> Exp d
  -> Exp (a, b, c, d)
pattern E4 a b c d = MkT (a, b, c, d)

pattern E5
  :: (Elt a, Elt b, Elt c, Elt d, Elt e)
  => Exp a -> Exp b -> Exp c -> Exp d -> Exp e
  -> Exp (a, b, c, d, e)
pattern E5 a b c d e = MkT (a, b, c, d, e)

pattern E6
  :: (Elt a, Elt b, Elt c, Elt d, Elt e, Elt f)
  => Exp a -> Exp b -> Exp c -> Exp d -> Exp e -> Exp f
  -> Exp (a, b, c, d, e, f)
pattern E6 a b c d e f = MkT (a, b, c, d, e, f)

pattern E7
  :: (Elt a, Elt b, Elt c, Elt d, Elt e, Elt f, Elt g)
  => Exp a -> Exp b -> Exp c -> Exp d -> Exp e -> Exp f -> Exp g
  -> Exp (a, b, c, d, e, f, g)
pattern E7 a b c d e f g = MkT (a, b, c, d, e, f, g)

pattern E8
  :: (Elt a, Elt b, Elt c, Elt d, Elt e, Elt f, Elt g, Elt h)
  => Exp a -> Exp b -> Exp c -> Exp d -> Exp e -> Exp f -> Exp g -> Exp h
  -> Exp (a, b, c, d, e, f, g, h)
pattern E8 a b c d e f g h = MkT (a, b, c, d, e, f, g, h)

pattern E9
  :: (Elt a, Elt b, Elt c, Elt d, Elt e, Elt f, Elt g, Elt h, Elt i)
  => Exp a -> Exp b -> Exp c -> Exp d -> Exp e -> Exp f -> Exp g -> Exp h -> Exp i
  -> Exp (a, b, c, d, e, f, g, h, i)
pattern E9 a b c d e f g h i = MkT (a, b, c, d, e, f, g, h, i)

pattern E10
  :: (Elt a, Elt b, Elt c, Elt d, Elt e, Elt f, Elt g, Elt h, Elt i, Elt j)
  => Exp a -> Exp b -> Exp c -> Exp d -> Exp e -> Exp f -> Exp g -> Exp h -> Exp i -> Exp j
  -> Exp (a, b, c, d, e, f, g, h, i, j)
pattern E10 a b c d e f g h i j = MkT (a, b, c, d, e, f, g, h, i, j)

pattern E11
  :: (Elt a, Elt b, Elt c, Elt d, Elt e, Elt f, Elt g, Elt h, Elt i, Elt j, Elt k)
  => Exp a -> Exp b -> Exp c -> Exp d -> Exp e -> Exp f -> Exp g -> Exp h -> Exp i -> Exp j -> Exp k
  -> Exp (a, b, c, d, e, f, g, h, i, j, k)
pattern E11 a b c d e f g h i j k = MkT (a, b, c, d, e, f, g, h, i, j, k)

pattern E12
  :: (Elt a, Elt b, Elt c, Elt d, Elt e, Elt f, Elt g, Elt h, Elt i, Elt j, Elt k, Elt l)
  => Exp a -> Exp b -> Exp c -> Exp d -> Exp e -> Exp f -> Exp g -> Exp h -> Exp i -> Exp j -> Exp k -> Exp l
  -> Exp (a, b, c, d, e, f, g, h, i, j, k, l)
pattern E12 a b c d e f g h i j k l = MkT (a, b, c, d, e, f, g, h, i, j, k, l)

pattern E13
  :: (Elt a, Elt b, Elt c, Elt d, Elt e, Elt f, Elt g, Elt h, Elt i, Elt j, Elt k, Elt l, Elt m)
  => Exp a -> Exp b -> Exp c -> Exp d -> Exp e -> Exp f -> Exp g -> Exp h -> Exp i -> Exp j -> Exp k -> Exp l -> Exp m
  -> Exp (a, b, c, d, e, f, g, h, i, j, k, l, m)
pattern E13 a b c d e f g h i j k l m = MkT (a, b, c, d, e, f, g, h, i, j, k, l, m)

pattern E14
  :: (Elt a, Elt b, Elt c, Elt d, Elt e, Elt f, Elt g, Elt h, Elt i, Elt j, Elt k, Elt l, Elt m, Elt n)
  => Exp a -> Exp b -> Exp c -> Exp d -> Exp e -> Exp f -> Exp g -> Exp h -> Exp i -> Exp j -> Exp k -> Exp l -> Exp m -> Exp n
  -> Exp (a, b, c, d, e, f, g, h, i, j, k, l, m, n)
pattern E14 a b c d e f g h i j k l m n = MkT (a, b, c, d, e, f, g, h, i, j, k, l, m, n)

pattern E15
  :: (Elt a, Elt b, Elt c, Elt d, Elt e, Elt f, Elt g, Elt h, Elt i, Elt j, Elt k, Elt l, Elt m, Elt n, Elt o)
  => Exp a -> Exp b -> Exp c -> Exp d -> Exp e -> Exp f -> Exp g -> Exp h -> Exp i -> Exp j -> Exp k -> Exp l -> Exp m -> Exp n -> Exp o
  -> Exp (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o)
pattern E15 a b c d e f g h i j k l m n o = MkT (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o)


-- | Specialised pattern synonyms for tuples in @Acc@.
--
pattern A2
  :: (Arrays a, Arrays b)
  => Acc a -> Acc b
  -> Acc (a, b)
pattern A2 a b = MkT (a, b)

pattern A3
  :: (Arrays a, Arrays b, Arrays c)
  => Acc a -> Acc b -> Acc c
  -> Acc (a, b, c)
pattern A3 a b c = MkT (a, b, c)

pattern A4
  :: (Arrays a, Arrays b, Arrays c, Arrays d)
  => Acc a -> Acc b -> Acc c -> Acc d
  -> Acc (a, b, c, d)
pattern A4 a b c d = MkT (a, b, c, d)

pattern A5
  :: (Arrays a, Arrays b, Arrays c, Arrays d, Arrays e)
  => Acc a -> Acc b -> Acc c -> Acc d -> Acc e
  -> Acc (a, b, c, d, e)
pattern A5 a b c d e = MkT (a, b, c, d, e)

pattern A6
  :: (Arrays a, Arrays b, Arrays c, Arrays d, Arrays e, Arrays f)
  => Acc a -> Acc b -> Acc c -> Acc d -> Acc e -> Acc f
  -> Acc (a, b, c, d, e, f)
pattern A6 a b c d e f = MkT (a, b, c, d, e, f)

pattern A7
  :: (Arrays a, Arrays b, Arrays c, Arrays d, Arrays e, Arrays f, Arrays g)
  => Acc a -> Acc b -> Acc c -> Acc d -> Acc e -> Acc f -> Acc g
  -> Acc (a, b, c, d, e, f, g)
pattern A7 a b c d e f g = MkT (a, b, c, d, e, f, g)

pattern A8
  :: (Arrays a, Arrays b, Arrays c, Arrays d, Arrays e, Arrays f, Arrays g, Arrays h)
  => Acc a -> Acc b -> Acc c -> Acc d -> Acc e -> Acc f -> Acc g -> Acc h
  -> Acc (a, b, c, d, e, f, g, h)
pattern A8 a b c d e f g h = MkT (a, b, c, d, e, f, g, h)

pattern A9
  :: (Arrays a, Arrays b, Arrays c, Arrays d, Arrays e, Arrays f, Arrays g, Arrays h, Arrays i)
  => Acc a -> Acc b -> Acc c -> Acc d -> Acc e -> Acc f -> Acc g -> Acc h -> Acc i
  -> Acc (a, b, c, d, e, f, g, h, i)
pattern A9 a b c d e f g h i = MkT (a, b, c, d, e, f, g, h, i)

pattern A10
  :: (Arrays a, Arrays b, Arrays c, Arrays d, Arrays e, Arrays f, Arrays g, Arrays h, Arrays i, Arrays j)
  => Acc a -> Acc b -> Acc c -> Acc d -> Acc e -> Acc f -> Acc g -> Acc h -> Acc i -> Acc j
  -> Acc (a, b, c, d, e, f, g, h, i, j)
pattern A10 a b c d e f g h i j = MkT (a, b, c, d, e, f, g, h, i, j)

pattern A11
  :: (Arrays a, Arrays b, Arrays c, Arrays d, Arrays e, Arrays f, Arrays g, Arrays h, Arrays i, Arrays j, Arrays k)
  => Acc a -> Acc b -> Acc c -> Acc d -> Acc e -> Acc f -> Acc g -> Acc h -> Acc i -> Acc j -> Acc k
  -> Acc (a, b, c, d, e, f, g, h, i, j, k)
pattern A11 a b c d e f g h i j k = MkT (a, b, c, d, e, f, g, h, i, j, k)

pattern A12
  :: (Arrays a, Arrays b, Arrays c, Arrays d, Arrays e, Arrays f, Arrays g, Arrays h, Arrays i, Arrays j, Arrays k, Arrays l)
  => Acc a -> Acc b -> Acc c -> Acc d -> Acc e -> Acc f -> Acc g -> Acc h -> Acc i -> Acc j -> Acc k -> Acc l
  -> Acc (a, b, c, d, e, f, g, h, i, j, k, l)
pattern A12 a b c d e f g h i j k l = MkT (a, b, c, d, e, f, g, h, i, j, k, l)

pattern A13
  :: (Arrays a, Arrays b, Arrays c, Arrays d, Arrays e, Arrays f, Arrays g, Arrays h, Arrays i, Arrays j, Arrays k, Arrays l, Arrays m)
  => Acc a -> Acc b -> Acc c -> Acc d -> Acc e -> Acc f -> Acc g -> Acc h -> Acc i -> Acc j -> Acc k -> Acc l -> Acc m
  -> Acc (a, b, c, d, e, f, g, h, i, j, k, l, m)
pattern A13 a b c d e f g h i j k l m = MkT (a, b, c, d, e, f, g, h, i, j, k, l, m)

pattern A14
  :: (Arrays a, Arrays b, Arrays c, Arrays d, Arrays e, Arrays f, Arrays g, Arrays h, Arrays i, Arrays j, Arrays k, Arrays l, Arrays m, Arrays n)
  => Acc a -> Acc b -> Acc c -> Acc d -> Acc e -> Acc f -> Acc g -> Acc h -> Acc i -> Acc j -> Acc k -> Acc l -> Acc m -> Acc n
  -> Acc (a, b, c, d, e, f, g, h, i, j, k, l, m, n)
pattern A14 a b c d e f g h i j k l m n = MkT (a, b, c, d, e, f, g, h, i, j, k, l, m, n)

pattern A15
  :: (Arrays a, Arrays b, Arrays c, Arrays d, Arrays e, Arrays f, Arrays g, Arrays h, Arrays i, Arrays j, Arrays k, Arrays l, Arrays m, Arrays n, Arrays o)
  => Acc a -> Acc b -> Acc c -> Acc d -> Acc e -> Acc f -> Acc g -> Acc h -> Acc i -> Acc j -> Acc k -> Acc l -> Acc m -> Acc n -> Acc o
  -> Acc (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o)
pattern A15 a b c d e f g h i j k l m n o = MkT (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o)
