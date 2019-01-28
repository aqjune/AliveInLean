-- Copyright (c) Microsoft Corporation. All rights reserved.
-- Licensed under the MIT license.

import system.io
import system.random
import .lang
import .lang_tostr

def new_free_var (sz:nat) (i:nat): (ty × string) :=
  (ty.int sz, "var" ++ (to_string i))

def rand_subseq {α:Type} (l:list α) (g:std_gen): (list α × std_gen) :=
  list.foldl (λ (e:list α × std_gen) itm,
    let (l2, g0) := e in
    let (n, g') := std_next (e.2) in
    if n % 2 = 0 then
      (l2, g')
    else
      (itm::l2, g')
    ) ([], g) l

def rand_choose {α:Type} (l:list α) (g:std_gen)
    (HPOS:0 < l.length): (α × std_gen) :=
  let (n, g') := std_next g in
  let i := n % l.length in
  (l.nth_le i (by apply nat.mod_lt; apply HPOS), g')

def powerset {α: Type} : list α → list (list α)
| (h::t) := (powerset t) ++ (powerset t).map(λ e, h::e)
| [] := []

def bops: list bopcode :=
  [bopcode.add, bopcode.sub, bopcode.mul,
   bopcode.udiv, bopcode.urem, bopcode.sdiv, bopcode.srem,
   bopcode.and, bopcode.or,  bopcode.xor,
   bopcode.shl, bopcode.lshr, bopcode.ashr]

def icmpconds: list icmpcond :=
  [ icmpcond.eq, icmpcond.ne, icmpcond.ugt, icmpcond.uge,
    icmpcond.ult, icmpcond.ule, icmpcond.sgt, icmpcond.sge,
    icmpcond.slt, icmpcond.sle ]

def uops: list uopcode :=
  [ uopcode.sext, uopcode.zext, uopcode.trunc ]

-- select

meta def nextinst (g:std_gen) : io std_gen :=
  let bops2 := bops.map (λ itm,
    let e := powerset (bop_availflags itm) in
    e.map (λ flags, (itm, flags))) in
  let bops2 := bops2.join in
  let (n, g) := std_next g in
  let n := n % (bops.length + icmpconds.length + uops.length + 1) in
  do
  (if H:(n < bops2.length) then
    -- create bop.
    io.put_str (to_string (bops2.nth_le n H))
  else
    let n := n - bops2.length in
    if H:(n < icmpconds.length) then
      -- create icmp.
      io.put_str (to_string (icmpconds.nth_le n H))
    else
      let n := n - icmpconds.length in
      if H:(n < uops.length) then
        -- create uop.
        io.put_str (to_string (uops.nth_le n H))
      else
        io.put_str "select"),
  return g

meta def main : io unit :=
  let gen := mk_std_gen in do
  do
  h ← nextinst gen,
  return ()