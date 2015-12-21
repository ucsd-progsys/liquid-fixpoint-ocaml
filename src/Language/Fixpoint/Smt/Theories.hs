{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE UndecidableInstances      #-}

module Language.Fixpoint.Smt.Theories
     (
       -- * Convert theory applications TODO: merge with smt2symbol
       smt2App
       -- * Convert theory sorts
     , smt2Sort
       -- * Convert theory symbols
     , smt2Symbol
       -- * Preamble to initialize SMT
     , preamble

     ) where

import           Prelude hiding (map)
import           Language.Fixpoint.Config
import           Language.Fixpoint.Types
import           Language.Fixpoint.Smt.Types
import qualified Data.HashMap.Strict      as M
import qualified Data.Text                as T
import           Data.Text.Format         hiding (format)
import qualified Data.Text.Lazy.Builder   as LT


--------------------------------------------------------------------------
-- | Set Theory ----------------------------------------------------------
--------------------------------------------------------------------------

elt, set, map, bit, sz32, sz64 :: Raw
elt  = "Elt"
set  = "Set"
map  = "Map"
bit  = "BitVec"
sz32 = "Size32"
sz64 = "Size64"


emp, add, cup, cap, mem, dif, sub, com, sel, sto :: Raw
emp   = "smt_set_emp"
add   = "smt_set_add"
cup   = "smt_set_cup"
cap   = "smt_set_cap"
mem   = "smt_set_mem"
dif   = "smt_set_dif"
sub   = "smt_set_sub"
com   = "smt_set_com"
sel   = "smt_map_sel"
sto   = "smt_map_sto"


setEmpty, setEmp, setCap, setSub, setAdd, setMem, setCom, setCup, setDif, setSng, mapSel, mapSto :: Symbol
setEmpty = "Set_empty"
setEmp   = "Set_emp"
setCap   = "Set_cap"
setSub   = "Set_sub"
setAdd   = "Set_add"
setMem   = "Set_mem"
setCom   = "Set_com"
setCup   = "Set_cup"
setDif   = "Set_dif"
setSng   = "Set_sng"
mapSel   = "Map_select"
mapSto   = "Map_store"

z3Preamble :: [LT.Builder]
z3Preamble
  = [ build "(define-sort {} () Int)"
        (Only elt)
    , build "(define-sort {} () (Array {} Bool))"
        (set, elt)
    , build "(define-fun {} () {} ((as const {}) false))"
        (emp, set, set)
    , build "(define-fun {} ((x {}) (s {})) Bool (select s x))"
        (mem, elt, set)
    , build "(define-fun {} ((s {}) (x {})) {} (store s x true))"
        (add, set, elt, set)
    , build "(define-fun {} ((s1 {}) (s2 {})) {} ((_ map or) s1 s2))"
        (cup, set, set, set)
    , build "(define-fun {} ((s1 {}) (s2 {})) {} ((_ map and) s1 s2))"
        (cap, set, set, set)
    , build "(define-fun {} ((s {})) {} ((_ map not) s))"
        (com, set, set)
    , build "(define-fun {} ((s1 {}) (s2 {})) {} ({} s1 ({} s2)))"
        (dif, set, set, set, cap, com)
    , build "(define-fun {} ((s1 {}) (s2 {})) Bool (= {} ({} s1 s2)))"
        (sub, set, set, emp, dif)
    , build "(define-sort {} () (Array {} {}))"
        (map, elt, elt)
    , build "(define-fun {} ((m {}) (k {})) {} (select m k))"
        (sel, map, elt, elt)
    , build "(define-fun {} ((m {}) (k {}) (v {})) {} (store m k v))"
        (sto, map, elt, elt, map)
    ]

smtlibPreamble :: [LT.Builder]
smtlibPreamble
  = [        "(set-logic QF_UFLIA)"
    , build "(define-sort {} () Int)"       (Only elt)
    , build "(define-sort {} () Int)"       (Only set)
    , build "(declare-fun {} () {})"        (emp, set)
    , build "(declare-fun {} ({} {}) {})"   (add, set, elt, set)
    , build "(declare-fun {} ({} {}) {})"   (cup, set, set, set)
    , build "(declare-fun {} ({} {}) {})"   (cap, set, set, set)
    , build "(declare-fun {} ({} {}) {})"   (dif, set, set, set)
    , build "(declare-fun {} ({} {}) Bool)" (sub, set, set)
    , build "(declare-fun {} ({} {}) Bool)" (mem, elt, set)
    , build "(declare-fun {} ({} {}) {})"    (sel, map, elt, elt)
    , build "(declare-fun {} ({} {} {}) {})" (sto, map, elt, elt, map)
    ]

mkSetSort _ _  = set
mkEmptySet _ _ = emp
mkSetAdd _ s x = build "({} {} {})" (add, s, x)
mkSetMem _ x s = build "({} {} {})" (mem, x, s)
mkSetCup _ s t = build "({} {} {})" (cup, s, t)
mkSetCap _ s t = build "({} {} {})" (cap, s, t)
mkSetDif _ s t = build "({} {} {})" (dif, s, t)
mkSetSub _ s t = build "({} {} {})" (sub, s, t)


-- smt_set_funs :: M.HashMap Symbol Raw
-- smt_set_funs = M.fromList [ (setEmp, emp), (setAdd, add), (setCup, cup)
--                           , (setCap, cap), (setMem, mem), (setDif, dif)
--                           , (setSub, sub), (setCom, com)]

theorySymbols :: M.HashMap Symbol TheorySymbol
theorySymbols = M.fromList
  [ tSym setEmp emp undefined
  , tSym setAdd add undefined
  , tSym setCup cup undefined
  , tSym setCap cap undefined
  , tSym setMem mem undefined
  , tSym setDif dif undefined
  , tSym setSub sub undefined
  , tSym setCom com undefined
  , tSym mapSel sel undefined
  , tSym mapSto sto undefined
  ]

tSym :: Symbol -> Raw -> Sort -> (Symbol, TheorySymbol)
tSym x n t = (x, Thy x n t)

-------------------------------------------------------------------------------
-- | Exported API -------------------------------------------------------------
-------------------------------------------------------------------------------

smt2Symbol :: Symbol -> Maybe LT.Builder
smt2Symbol x = LT.fromText . tsRaw <$> M.lookup x theorySymbols

smt2Sort :: Sort -> Maybe LT.Builder
smt2Sort (FApp (FTC c) t)
  | fTyconSymbol c == "Set_Set" = Just $ build "{}" (Only set)
smt2Sort (FApp (FApp (FTC c) t1) t2)
  | fTyconSymbol c == "Map_t"   = Just $ build "{}" (Only map)
smt2Sort _                      = Nothing

smt2App :: LocSymbol -> [LT.Builder] -> Maybe LT.Builder
smt2App f [d]
  | val f == setEmpty = Just $ build "{}"             (Only emp)
  | val f == setEmp   = Just $ build "(= {} {})"      (emp, d)
  | val f == setSng   = Just $ build "({} {} {})"     (add, emp, d)
smt2App _ _           = Nothing

preamble :: SMTSolver -> [LT.Builder]
preamble Z3 = z3Preamble
preamble _  = smtlibPreamble
