{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Lib
( someFunc
, ghettoInterpret
, runExpr
, example
, Expr(..)
, Stmt(..)
, Value(..)

)
where

import Control.Monad (void, forM_, return)
import Data.List (zip, (++), map, lines, reverse, intercalate)
import Text.Megaparsec
import Text.Megaparsec.Expr
import Text.Megaparsec.String
import qualified Text.Megaparsec.Lexer as L
import Text.Show ( Show(..) )
import Data.Function ( ($) )
import Data.String (String)
import System.IO (IO(..), readFile, writeFile, putStrLn)
import GHC.Float (Double)
import GHC.Err (undefined, error)
import qualified Data.Map.Strict as M
import GHC.Num (Num(..))
import Data.Maybe (Maybe(..))
import Data.Foldable (foldrM)
import Data.Functor ((<$>))
import Data.Char (ord, chr)
import GHC.Base (id)



--  1: 1,2,3,4     --  let :1 = [1,2,3,4]
--  2: "AbCD"      --  let :2 = "AbCD"
--  3: < :2        --  let :3 = readFile :2
--  4: - ^ :3      --  let :4 = map incr :3
--  5: > :4 "AbCD2"--  let :5 = writeFile :4 "AbCD2"
--  6:
--  7:
--  8:
--
--
--
--
--

data AElem a = AE (Expr a) (AElem a)
             | AN
           deriving (Show)

--data Expr = Var String
--          | LitA AElem
--          | LitS String
--          | LitI Double
--          | (:<) Expr
--          | (:>) Expr Expr
--          | (:-) Expr Expr
--          | (:^)
--          | Ap Expr Expr
--          deriving (Show)
data Expr a where
  Var :: String -> Expr Value
  LitAN :: [Double] -> Expr ([Double])
  LitAS :: [String] -> Expr ([String])
  LitS :: String -> Expr String
  LitN :: Double -> Expr Double
  ToV :: Valuable a => Expr a -> Expr Value
  (:<) :: Expr Value -> Expr ([String])
  (:>) :: Expr Value -> Expr Value -> Expr ()
  (:-) :: Expr (Value -> Value) -> Expr Value -> Expr (Value)
  (:^) :: Incrementable a => Expr (a -> a)
  Store :: M.Map String Value -> Expr Value -> Expr (M.Map String Value)
  Stop :: Valuable a => Expr a -> Expr ()


deriving instance Show (Expr a)

data Value = VN Double
           | VS String
           | VAS [String]
           | VAN [Double]
           | VU
           deriving (Show)

data Target = TV String
            | TS String
            deriving Show
newtype Variable = Variable String deriving Show

--data Stmt = Seq [Stmt]
--          | Run Expr
--          | Empty
--          deriving (Show)

data Stmt = Seq [Stmt]
          | Run (Expr ())
          | Empty
deriving instance Show (Stmt)

instance Incrementable Value where
  incr' (VN d) = VN $ incr' d
  incr' (VS s) = VS $ incr' s
  incr' (_) = error "ADASDAS"

example = Seq [
      Run $ Stop $ LitAN [1,2,3,4]
    , Run $ Stop $ LitS "/tmp/file1"
    , Run $ Stop $ (:<) (Var ":2")
    , Run $ Stop $ (:-) (:^) (Var ":3")
    , Run $ Stop $ (:>) (ToV (LitS "/tmp/file2")) (Var ":4")
  ]

ghettoInterpret :: Stmt -> IO ()
ghettoInterpret (Seq stmts) = do
  let st = M.empty
  void $ foldrM' st (reverse $ zip (map (\x -> ":" ++ show x) [1..]) stmts) $ \(n, s) st' -> do
    putStrLn n
    go st' n s
  where go st'' n (Run expr) = do
          (res,m) <- runExpr n st'' expr
          return $ m


runExpr :: String -> (M.Map String Value) -> Expr a -> IO (a, M.Map String Value)
runExpr n st = go
  where go (Var s) = case M.lookup s st of
          Nothing -> error $ "Lookup: " ++ s ++ show st
          Just x -> do
            putStrLn $ s ++ show st
            return (x, st)
        go (LitAN a) = return (a, st)
        go (LitAS a) = return (a, st)
        go (LitS a) = return (a, st)
        go (LitN a) = return (a, st)
        go ((:<) e) = do
          (r, st') <- runExpr n st e
          case r of
            VS s -> do
              l <- lines <$> readFile s
              return (l, st')
            _ -> error "BOOM"
        go ((:>) e e') = do
          (t, st') <- runExpr n st e
          (v, st'') <- runExpr n st' e'
          let v'' = case v of
                      VS v' -> v'
                      VAS vs' -> intercalate "\n" vs'
          case t of
            VS s -> do
              writeFile s v''
              return ((), st'')
            _ -> error "Boom2"
        go ((:-) e e') = do
          (f, st') <- runExpr n st e
          (v, st'') <- runExpr n st' e'
          case v of
            VAS ss -> do
              return $ (VAS $ map (\s -> case f (VS s) of
                                           VS s' -> s' ) ss, st'')
            VAN ns -> do
              return $ (VAN $ map (\n -> case f (VN n) of
                                           VN n' -> n') ns, st'')
            _ -> error "Boom3"
        go (:^) = return (incr, st)
        go (ToV v) = do
          (v',st') <- runExpr n st v
          return (toVal v', st')
        go (Stop e) = do
          (r, st') <- runExpr n st e
          let val = toVal r
          putStrLn n
          return ((), M.insert n val st')

incr :: Incrementable a => a -> a
incr = incr'

class Incrementable a where
  incr' :: a -> a

instance Incrementable Double where
  incr' = (+1)
instance Incrementable String where
  incr' = map (\c -> chr $ ord c + 1)

class Valuable a where
  toVal :: a -> Value

instance Valuable [String] where
  toVal s = VAS s
instance Valuable [Double] where
  toVal d = VAN d

instance Valuable String where
  toVal s = VS s
instance Valuable Double where
  toVal d = VN d
instance Valuable () where
  toVal _ = VU
instance Valuable Value where
  toVal = id

foldrM' ac l a = foldrM a ac l

someFunc :: IO ()
someFunc = undefined
