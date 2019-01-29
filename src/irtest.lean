-- Copyright (c) Microsoft Corporation. All rights reserved.
-- Licensed under the MIT license.

import system.io
import system.random
import .lang
import .lang_tostr

def new_free_var (t:ty) (i:nat): (ty × string) :=
  (t, "var" ++ (to_string i))

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

def MAX_ISZ := 64

def asdf := true.

-- Chooses an integer-typed variable or create a new one.
-- returns (type of the variable, variable name, is-a-fresh-var, std_gen)
def choose_or_newvar (vars:list (ty × string)) (wantedty: option ty) (g:std_gen)
: (ty × string × bool × std_gen) :=
  -- type generator
  let tygen: std_gen → (ty × std_gen) := λ (g:std_gen),
    match wantedty with
    | none :=
      let (n,g) := std_next g in
      (ty.int (1 + n % MAX_ISZ), g)
    | some t := (t, g)
    end in
  let vars0len := vars.length in
  -- Filter vars with wantedty
  let vars := match wantedty with | none := vars | some t := vars.filter (λ x, x.1 = t) end in
  if HPOS:(0 < vars.length) then
    let (n, g) := std_next g in
    let n := n % (1 + vars.length) in
    if HLT:(n < vars.length) then
      let (t, name) := vars.nth_le n HLT in
      (t, name, ff, g)
    else
      let (thety, g) := tygen g in
      let (t, name) := new_free_var thety vars0len in
      (t, name, tt, g)
  else
    let (thety, g) := tygen g in
    let (t, name) := new_free_var thety vars0len in
    (t, name, tt, g)


-- Returns: (freevars, vars, instruction, std_gen)
meta def nextinst (freevars:list (ty × string)) (vars:list (ty × string)) (g:std_gen)
: io (list (ty × string) × list (ty × string) × instruction × std_gen) :=
  let vars_update := λ fvs vs (isfresh:bool) (itm:ty × string),
    if isfresh then (itm::fvs, vs)
    else (fvs, itm::vs) in
  let bops2 := bops.map (λ itm,
    let e := powerset (bop_availflags itm) in
    e.map (λ flags, (itm, flags))) in
  let bops2 := bops2.join in
  let (n, g) := std_next g in
  let n := n % (bops.length + icmpconds.length + uops.length + 1) in

  if H:(n < bops2.length) then
    -- choose operand 1
    let (varty1, varname1, isfresh1, g) := choose_or_newvar (freevars ++ vars) none g in
    let (freevars, vars) := vars_update freevars vars isfresh1 (varty1, varname1) in
    -- choose operand 2
    -- operand 1 and 2 should have the same type
    let (varty2, varname2, isfresh2, g) := choose_or_newvar (freevars ++ vars) varty1 g in
    let (freevars, vars) := vars_update freevars vars isfresh2 (varty2, varname2) in
    -- make lhs
    let lhsname := ("var" ++ (to_string (freevars.length + vars.length))) in
    let lhs := reg.r lhsname in
    -- create bop.
    let (bopc, flags) := bops2.nth_le n H in
    let bop := instruction.binop varty1 lhs bopc flags (operand.reg (reg.r varname1))
        (operand.reg (reg.r varname2)) in
    do
    io.put_str (to_string bop),
    return (freevars, (varty1, lhsname)::vars, bop, g)

  else
    let n := n - bops2.length in
    if H:(n < icmpconds.length) then
      -- choose operand 1
      let (varty1, varname1, isfresh1, g) := choose_or_newvar (freevars ++ vars) none g in
      let (freevars, vars) := vars_update freevars vars isfresh1 (varty1, varname1) in
      -- choose operand 2
      -- operand 1 and 2 should have the same type
      let (varty2, varname2, isfresh2, g) := choose_or_newvar (freevars ++ vars) varty1 g in
      let (freevars, vars) := vars_update freevars vars isfresh2 (varty2, varname2) in
      -- make lhs
      let lhsname := ("var" ++ (to_string (freevars.length + vars.length))) in
      let lhs := reg.r lhsname in
      -- create icmp.
      let cond := icmpconds.nth_le n H in
      let iop := instruction.icmpop varty1 lhs cond (operand.reg (reg.r varname1))
          (operand.reg (reg.r varname2)) in
      do
      io.put_str (to_string iop),
      return (freevars, (ty.int 1, lhsname)::vars, iop, g)

    else
      let n := n - icmpconds.length in
      if H:(n < uops.length) then
        let uopc := uops.nth_le n H in
        -- choose operand
        let (varty, varname, isfresh, g) := choose_or_newvar (freevars ++ vars) none g in
        -- make lhs
        let lhsname := ("var" ++ (to_string (freevars.length + vars.length))) in
        let lhs := reg.r lhsname in
        -- make target type
        match varty with
        | ty.int isz :=
          let res:(ty × std_gen) := match uopc with
            | uopcode.trunc :=
              let (n, g) := std_next g in
              (ty.int (n % isz + 1), g)
            | _ :=
              if isz = MAX_ISZ then (ty.int MAX_ISZ, g)
              else
                let (n, g) := std_next g in
                (ty.int (isz + (n % (64 - isz))), g)
            end in
          let (toty, g) := res in
          -- create uop
          let uop := instruction.unaryop lhs uopc varty (operand.reg (reg.r varname)) toty in
          do
          io.put_str (to_string uop),
          return (freevars, (toty, lhsname)::vars, uop, g)
        | _ := sorry -- unreachable
        end

      else
        -- select
        -- choose operand 1
        let (varty1, varname1, isfresh1, g) := choose_or_newvar (freevars ++ vars) none g in
        let (freevars, vars) := vars_update freevars vars isfresh1 (varty1, varname1) in
        -- choose operand 2
        -- operand 1 and 2 should have the same type
        let (varty2, varname2, isfresh2, g) := choose_or_newvar (freevars ++ vars) varty1 g in
        let (freevars, vars) := vars_update freevars vars isfresh2 (varty2, varname2) in
        -- choose conditional operand
        let (vartyc, varnamec, isfreshc, g) := choose_or_newvar (freevars ++ vars) (ty.int 1) g in
        let (freevars, vars) := vars_update freevars vars isfreshc (vartyc, varnamec) in
        -- make lhs
        let lhsname := ("var" ++ (to_string (freevars.length + vars.length))) in
        let lhs := reg.r lhsname in
        -- create select.
        let selop := instruction.selectop lhs vartyc (operand.reg (reg.r varnamec))
            varty1 (operand.reg (reg.r varname1)) (operand.reg (reg.r varname2)) in
        do
        io.put_str (to_string selop),
        return (freevars, (varty1, lhsname)::vars, selop, g)


meta def main : io unit :=
  let gen := mk_std_gen in
  let freevars:list (ty × string) := [] in
  let vars:list (ty × string) := [] in
  do
  h ← nextinst freevars vars gen,
  return ()