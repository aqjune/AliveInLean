-- Copyright (c) Microsoft Corporation. All rights reserved.
-- Licensed under the MIT license.

import system.io
import system.random
import .lang
import .lang_tostr


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
| [h] := [[],[h]]
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

-- Possible integer type sizes.
@[simp]
def ISZ_LIST := [1, 4, 8, 16, 32, 64]

def is_even (n:nat): bool :=
  n % 2 = 0

-- state monad
structure vars_record :=
  (freevars: list (ty × string))
  (vars: list (ty × string))
@[reducible]
def vars_state := state vars_record
def vars_record_empty: vars_record := ⟨[], []⟩

-- Creates a new free variable.
def fv_new (t:ty): vars_state string :=
do r ← get,
  let name := "%var" ++ (to_string (r.freevars.length + r.vars.length)),
  put ⟨(t,name)::r.freevars, r.vars⟩,
  return name

-- Creates a random type.
def ty_new (g:std_gen): (ty × std_gen) :=
  let (n, g) := rand_choose ISZ_LIST g (by simp; repeat {constructor}) in
  (ty.int n, g)

-- Chooses an integer-typed variable or create a new one.
-- returns (type of the variable, variable name, is-a-fresh-var, std_gen)
def choose_or_newvar (wantedty: option ty) (g:std_gen)
: vars_state (ty × string × bool × std_gen) :=
  -- type generator
  let tygen: std_gen → (ty × std_gen) := λ (g:std_gen),
    match wantedty with | none := ty_new g | some t := (t, g) end in
do
  r ← get,
  let vars := r.freevars ++ r.vars,
  -- Filter vars with wantedty
  let vars := match wantedty with | none := vars | some t := vars.filter (λ x, x.1 = t) end in
  if HPOS:(0 < vars.length) then
    let (n, g) := std_next g in
    let n := n % (1 + vars.length) in
    if HLT:(n < vars.length) then
      let (t, name) := vars.nth_le n HLT in
      return (t, name, ff, g)
    else
      -- create
      let (thety, g) := tygen g in
      do name ← fv_new thety, return (thety, name, tt, g)
  else
    let (thety, g) := tygen g in
    do name ← fv_new thety, return (thety, name, tt, g)

def vars_update := λ fvs vs (isfresh:bool) (itm:ty × string),
    if isfresh then (itm::fvs, vs)
    else (fvs, itm::vs)

-- Returns: (new var, new instruction, std_gen)
def rand_bop (retty:ty) (retvar:string) (bopc:bopcode) (flags:list bopflag) (g:std_gen)
: vars_state (instruction × std_gen) :=
do
  -- choose operand 1
  (varty1, varname1, isfresh1, g) ← choose_or_newvar retty g,
  -- choose operand 2
  -- operand 1 and 2 should have the same type
  (varty2, varname2, isfresh2, g) ← choose_or_newvar varty1 g,
  -- make lhs
  let lhs := reg.r retvar,
  -- create bop.
  let bop := instruction.binop varty1 lhs bopc flags (operand.reg (reg.r varname1))
      (operand.reg (reg.r varname2)),
  return (bop, g)

def rand_icmpop (retvar:string) (cond:icmpcond) (g:std_gen)
: vars_state (instruction × std_gen) :=
do
  -- choose operand 1
  (varty1, varname1, isfresh1, g) ← choose_or_newvar none g,
  -- choose operand 2
  -- operand 1 and 2 should have the same type
  (varty2, varname2, isfresh2, g) ← choose_or_newvar varty1 g,
  -- make lhs
  let lhs := reg.r retvar,
  -- create icmp.
  let iop := instruction.icmpop varty1 lhs cond (operand.reg (reg.r varname1))
      (operand.reg (reg.r varname2)),
  return (iop, g)

def rand_selectop (retty:ty) (retvar:string) (g:std_gen)
: vars_state (instruction × std_gen) :=
do
  -- choose operand 1
  (varty1, varname1, isfresh1, g) ← choose_or_newvar none g,
  -- choose operand 2
  -- operand 1 and 2 should have the same type
  (varty2, varname2, isfresh2, g) ← choose_or_newvar varty1 g,
  -- choose conditional operand
  (vartyc, varnamec, isfreshc, g) ← choose_or_newvar (ty.int 1) g,
  let selop := instruction.selectop (reg.r retvar)
      vartyc (operand.reg (reg.r varnamec))
      varty1 (operand.reg (reg.r varname1)) (operand.reg (reg.r varname2)) in
  return (selop, g)


def rand_castop (retty:ty) (retvar:string) (castop:uopcode) (fromty:option ty)
    (opname:option string) (g:std_gen)
: vars_state (instruction × std_gen) :=
do
  res:(ty × string × bool × std_gen) ←
    match (opname, fromty) with
    | (none, fromty) := choose_or_newvar fromty g
    | (some r, some fromty) := return (fromty, r, ff, g)
    | _ := sorry
    end,
  let (varty, varname, isfresh, g) := res in
  -- make lhs
  let lhs := reg.r retvar in
  -- create uop
  let uop := instruction.unaryop lhs castop varty (operand.reg (reg.r varname)) retty in
  return (uop, g)


-- Returns: (new freevars, new vars, new instructions, std_gen)
def rand_inst (retty:ty) (retvar:string) (g:std_gen)
: vars_state (list instruction × std_gen) :=
  let bops2 := bops.map (λ itm,
    let e := powerset (bop_availflags itm) in
    e.map (λ flags, (itm, flags))) in
  let bops2 := bops2.join in
  let (n, g) := std_next g in
  let n := n % (match retty with
    | ty.int 1 := (bops2.length + uops.length + 1 + icmpconds.length)
    | _ := (bops2.length + uops.length + 1) -- cannot make icmp
    end) in

  if H:(n < bops2.length) then
    let (bopc, flags) := bops2.nth_le n H in
    do
    (inst, g) ← rand_bop retty retvar bopc flags g,
    return ([inst], g)

  else
    let n := n - bops2.length in
    if H:(n < uops.length) then
      do
      (fromty, fromvar, isfresh, g) ← choose_or_newvar none g,
      let res:(uopcode × std_gen) :=
        match (fromty, retty) with
        | (ty.int fromsz, ty.int tosz) :=
          if fromsz < tosz then
            let (n, g) := std_next g in
            ((if is_even n then uopcode.sext else uopcode.zext), g)
          else (uopcode.trunc, g)
        | (_, _) := sorry
        end in
      let (castop, g) := res in
      do
      (inst, g) ← rand_castop retty retvar castop fromty fromvar g,
      return ([inst], g)

    else
      let n := n - uops.length in
      if n = 0 then
        do
        (inst, g) ← rand_selectop retty retvar g,
        return ([inst], g)
      else
        let n := n - 1 in
        if H:(n < icmpconds.length) then
          let icond := icmpconds.nth_le n H in
          do
          (inst, g) ← rand_icmpop retvar icond g,
          return ([inst], g)
        else sorry

def rand_inst_run (retty:ty) (retvar:string) (g:std_gen) (vr:vars_record)
: (list instruction × std_gen) × vars_record :=
  let f: vars_state (list instruction × std_gen) :=
    rand_inst retty retvar g in
  f.run vr

def run_n: nat → std_gen → io unit
| 0 g := (return ())
| (nat.succ n') g :=
  do
  let ((insts, g), _) := rand_inst_run (ty.int 8) "res" g vars_record_empty,
  io.put_str_ln (to_string $ insts.nth 0),
  run_n n' g


meta def main : io unit :=
  let g := mk_std_gen in
  let freevars:list (ty × string) := [] in
  let vars:list (ty × string) := [] in
  do
  run_n 30 g,
  return ()
