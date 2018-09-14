/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Functions handling variables and substitution.
-/
import .syntax

namespace hol

namespace term

/-- `subst_at_depth u n t k` substitutes `u` for free variable `n` in `t` within `k` binders -/
def subst_at_depth (u : term) (n : nat) : term → nat → term
| (Var m)      k := if m = k + n then u else Var m
| (Const c)    k := Const c
| (App t₁ t₂)  k := App (subst_at_depth t₁ k) (subst_at_depth t₂ k)
| (Abs s ty t) k := Abs s ty (subst_at_depth t (k + 1))

/-- `subst u n t` substitutes `u` for free variable `n` in `t` -/
def subst (u : term) (n : nat) (t : term) := subst_at_depth u n t 0

/-- `abstract_aux n t k` renumbers free variable `n` at binder depth `k` so that it is free 
variable 0 -/
def abstract_aux (n : nat) : term → nat → term
| (Var m)      k := if m = n + k then Var k
                    else if m ≥ k ∧ m < n + k then Var (m + 1) 
                    else Var m 
| (Const c)    k := Const c
| (App t₁ t₂)  k := App (abstract_aux t₁ k) (abstract_aux t₂ k)
| (Abs s ty t) k := Abs s ty (abstract_aux t (k + 1))

/-- `abstract n s ty t` labmda abstracts free variable `n` with name `s` and type `ty` in `t` -/
def abstract (n : nat) (s: string) (ty : type) (t : term) := 
(Abs s ty (abstract_aux n t 0))

end term

end hol
