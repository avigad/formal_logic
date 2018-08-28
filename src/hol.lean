/-
An implementation of simple type theory, i.e. inductive definition of types and terms.

Notes:

When it comes to basic types, type constructors, and constants, we distinguish between "built in"
and "user" objects. The former are fixed for the implementation, and the implementation can refer
to them directly (for example, logical connectives, arithmetic symbols, types like nat and bool,
and type constructors like list, sum, and prod).

TODO: objects store all the relevant information for type checking, but also information as to 
the source. We can add additional predicates to say that a type or term is correct with respect
to the environment, i.e. that the objects have the properties the terms say they have.

TODO: In addition to "built in" and "user" objects, we can add "local" objects. In the meanwhile,
we use indices everywhere.

TODO: For now, we won't handle polymorphic types, though we will eventually (mostly following
HOL light).

TODO: For now, use naive equality tests. We can worry about more efficient tests (e.g. with
unique id's) later, if necessary.

Note: namespaces `hol.type` and `hol.term` are expected to be opened as necessary, so the
`repr` functions omit these prefixes.
-/

namespace hol

/-
Instead of option, we'll have failure produce error messages. But we will not use
the full-blown exception monad or do anything fancy, to make it easier to reason
about these programs.

TODO: not using this yet.
-/

inductive except (α : Type*)
| ok   : α → except
| fail : string → except

/- 
    Types    
-/

namespace type

  /- basic types -/

  @[derive has_reflect, derive decidable_eq]
  inductive basic : Type
  | user : ℕ → basic
  | prop 
  | nat
  | int
  | bool
  | unit

  namespace basic
    def repr : basic → string
    | (user n) := "(basic.user " ++ n.repr ++ ")"
    | prop := "basic.prop"
    | nat  := "basic.nat"
    | int  := "basic.int"
    | bool := "basic.bool"
    | unit := "basic.unit"

    instance : has_repr basic := ⟨repr⟩   
  end basic

  /- type constructors -/

  namespace constructor
    @[derive has_reflect, derive decidable_eq]
    inductive kind
    | user : nat → kind
    | list 
    | prod 
    | sum
  end constructor

  @[derive has_reflect, derive decidable_eq]
  structure constructor :=
  (symb : constructor.kind) (arity : nat)

  namespace constructor
    def user (n arity : nat)  : constructor := ⟨kind.user n, arity⟩
    def list : constructor := ⟨kind.list, 1⟩ 
    def prod : constructor := ⟨kind.prod, 2⟩ 
    def sum : constructor := ⟨kind.sum, 2⟩ 
    
    def repr : constructor → string
    | ⟨kind.user n, a⟩ := "(constructor.user " ++ n.repr ++ " " ++ a.repr ++")"
    | ⟨kind.list, _⟩   := "constructor.list"   
    | ⟨kind.prod, _⟩   := "constructor.list"   
    | ⟨kind.sum, _⟩    := "constructor.list"

    instance : has_repr constructor := ⟨repr⟩   
  end constructor

end type

/- 
The types themselves

Notes:

To avoid a nested inductive type, we'll use iterated application for constructors.

Basic and arrow types are really special cases of constructors, but we'll keep them separate.
-/

@[derive has_reflect, derive decidable_eq]
inductive type
| Var         : nat → type
| Basic       : hol.type.basic → type
| Arr         : type → type → type
| Constructor : hol.type.constructor → type
| App         : type → type → type

namespace type

def repr : type → string
| (Var n)         := "(Var " ++ n.repr ++ ")"
| (Basic b)       := "(Basic " ++ b.repr ++ ")"
| (Arr t₁ t₂)     := "(Arr " ++ t₁.repr ++ " " ++ t₂.repr ++")"
| (Constructor c) := "(Constructor " ++ c.repr ++ ")"
| (App t₁ t₂)     := "(App " ++ t₁.repr ++ " " ++ t₂.repr ++ ")"

instance : has_repr type := ⟨repr⟩

-- `arities_ok t l` says the type `t` iteratively applied to `l` makes sense
def arities_ok_aux : type → list type → bool
| (Var n)         l := l.empty
| (Basic b)       l := l.empty
| (Arr t₁ t₂)     l := arities_ok_aux t₁ l && arities_ok_aux t₂ l
| (Constructor c) l := c.arity = l.length
| (App t₁ t₂)     l := arities_ok_aux t₂ [] && arities_ok_aux t₁ (t₂ :: l)

def arities_ok (t : type) : bool := arities_ok_aux t []

end type

/- convenient type constructors -/

section
open type

def mk_prop := Basic basic.prop
def mk_nat := Basic basic.nat
def mk_int := Basic basic.int
def mk_unit := Basic basic.int
def mk_bool := Basic basic.bool
def mk_user_type (n : ℕ) := Basic (basic.user n)

def mk_list_type (t : type) : type := App (Constructor constructor.list) t
def mk_prod_type (t₁ t₂ : type) : type := App (App (Constructor constructor.prod) t₁) t₂
def mk_sum_type (t₁ t₂ : type) : type := App (App (Constructor constructor.sum) t₁) t₂

--notation t₁ ` ⇒ `:65 t₂ := Arr t₁ t₂  
infixr ` ⇒ ` := Arr

theorem arities_ok_mk_prop : arities_ok mk_prop :=
by simp [mk_prop, arities_ok, arities_ok_aux, list.empty]

theorem arities_ok_mk_nat : arities_ok mk_nat :=
by simp [mk_nat, arities_ok, arities_ok_aux, list.empty]

theorem arities_ok_mk_int : arities_ok mk_int :=
by simp [mk_int, arities_ok, arities_ok_aux, list.empty]

theorem arities_ok_mk_list_type (t : type) (h : arities_ok t = tt) : 
  arities_ok (mk_list_type t) = tt :=
by { simp [arities_ok] at *, simp [mk_list_type, arities_ok_aux, h, constructor.list] }

theorem arities_ok_mk_prod_type (t₁ t₂ : type) 
    (h₁ : arities_ok t₁ = tt) (h₂ : arities_ok t₂ = tt) : 
  arities_ok (mk_prod_type t₁ t₂) = tt :=
by { simp [arities_ok] at *, simp [mk_prod_type, arities_ok_aux, h₁, h₂, constructor.prod] }

theorem arities_ok_mk_sum_type (t₁ t₂ : type) 
    (h₁ : arities_ok t₁ = tt) (h₂ : arities_ok t₂ = tt) : 
  arities_ok (mk_sum_type t₁ t₂) = tt :=
by { simp [arities_ok] at *, simp [mk_sum_type, arities_ok_aux, h₁, h₂, constructor.sum] }

end

/-
    Terms
-/

namespace term

  /- constants -/

  namespace const
    @[derive has_reflect, derive decidable_eq]
    inductive kind
    | user : nat → kind
    | true 
    | false 
    | not
    | and
    | or
    | implies
    | iff
    | all
    | ex
    | add
    | mul
    | sub
    | bval : bool → kind
    | nval : nat → kind
  end const

  -- instantiations are for polymorphic constants
  @[derive has_reflect, derive decidable_eq]
  structure const :=
  (symb : const.kind) (type : type) (insts : list hol.type)

  namespace const
    def user (n : nat) (t : hol.type) (l : list hol.type) : const := ⟨kind.user n, t, l⟩
    def true : const := ⟨kind.true, mk_prop, []⟩ 
    def false : const := ⟨kind.false, mk_prop, []⟩ 
    def not : const := ⟨kind.not, mk_prop ⇒ mk_prop, []⟩
    def and : const := ⟨kind.and, mk_prop ⇒ (mk_prop ⇒ mk_prop), []⟩
    def or : const := ⟨kind.or, mk_prop ⇒ (mk_prop ⇒ mk_prop), []⟩
    def implies : const := ⟨kind.implies, mk_prop ⇒ (mk_prop ⇒ mk_prop), []⟩
    def iff : const := ⟨kind.iff, mk_prop ⇒ (mk_prop ⇒ mk_prop), []⟩
    def add : const := ⟨kind.add, mk_nat ⇒ (mk_nat ⇒ mk_nat), []⟩
    def mul : const := ⟨kind.mul, mk_nat ⇒ (mk_nat ⇒ mk_nat), []⟩
    def sub : const := ⟨kind.sub, mk_nat ⇒ (mk_nat ⇒ mk_nat), []⟩
    def tt  : const := ⟨kind.bval tt, mk_bool, []⟩
    def ff  : const := ⟨kind.bval ff, mk_bool, []⟩
    def nval (n : nat) : const := ⟨kind.nval n, mk_nat, []⟩

    def repr : const → string
    | ⟨kind.user n, t, l⟩       := "(const.user " ++ n.repr ++ " " ++ t.repr ++ " " ++ l.repr ++ ")"
    | ⟨kind.true, _, _⟩         := "const.true"
    | ⟨kind.false, _, _⟩        := "const.false"
    | ⟨kind.not, _, _⟩          := "const.not"
    | ⟨kind.and, _, _⟩          := "const.and"
    | ⟨kind.or, _, _⟩           := "const.or"
    | ⟨kind.implies, _, _⟩      := "const.implies"
    | ⟨kind.iff, _, _⟩          := "const.iff"
    | ⟨kind.all, _, _⟩          := "const.all"
    | ⟨kind.ex, _, _⟩           := "const.ex"
    | ⟨kind.add, _, _⟩          := "const.add"
    | ⟨kind.mul, _, _⟩          := "const.mul"
    | ⟨kind.sub, _, _⟩          := "const.sub"
    | ⟨kind.bval bool.tt, _, _⟩ := "const.tt"
    | ⟨kind.bval bool.ff, _, _⟩ := "const.ff"
    | ⟨kind.nval n, _, _⟩       := "(const.nval " ++ n.repr ++ ")"

    instance : has_repr const := ⟨repr⟩

    def is_connective : const → bool
    | ⟨kind.true, t, l⟩         := if t = mk_prop then l.empty else bool.ff
    | ⟨kind.false, t, l⟩        := if t = mk_prop then l.empty else bool.ff
    | ⟨kind.not, t, l⟩          := if t = (mk_prop ⇒ mk_prop) then l.empty else bool.ff
    | ⟨kind.and, t, l⟩          := if t = (mk_prop ⇒ mk_prop ⇒ mk_prop) then l.empty else bool.ff
    | ⟨kind.or, t, l⟩           := if t = (mk_prop ⇒ mk_prop ⇒ mk_prop) then l.empty else bool.ff
    | ⟨kind.implies, t, l⟩      := if t = (mk_prop ⇒ mk_prop ⇒ mk_prop) then l.empty else bool.ff
    | ⟨kind.iff, t, l⟩          := if t = (mk_prop ⇒ mk_prop ⇒ mk_prop) then l.empty else bool.ff
    | _                         := bool.ff
  end const

end term

/- the terms themselves -/

@[derive has_reflect, derive decidable_eq]
inductive term
| Var     : nat → term
| Const   : hol.term.const → term
| App     : term → term → term                -- application
| Abs     : string → hol.type → term → term   -- the string gives the preferred name

namespace term

def sizeof' : term → nat
| (Var n)      := 0
| (Const n)    := 0
| (App s t)    := sizeof' s + sizeof' t + 1
| (Abs s ty t) := sizeof t + 1

instance : has_sizeof term := ⟨sizeof'⟩

def repr : term → string
| (Var n)      := "(Var " ++ n.repr ++ ")"
| (Const c)    := "(Const " ++ c.repr ++ ")"
| (App t₁ t₂)  := "(App " ++ t₁.repr ++ t₂.repr ++ ")"
| (Abs s ty t) := "(Abs " ++ _root_.repr s ++ " " ++ ty.repr ++ " " ++ t.repr ++ ")"
  
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

/-- Inter the type of a term, given an assignment to free variables. -/
def infer_type : term → list type → option type 
| (Var n)     l  := l.nth n
| (Const c)   l  := some c.type 
| (App t₁ t₂) l  := match infer_type t₁ l with 
                    | some (type.Arr u v) := some v
                    | _                   := none
                    end
| (Abs s ty t) l := match infer_type t (ty :: l) with
                    | some ty₂ := some (type.Arr ty ty₂)
                    | _        := none
                    end

end term

section examples

open term

private def foo : term :=
  let ty := mk_nat ⇒ mk_nat ⇒ mk_nat,
      f := Const (const.user 0 ty []),
      x := Var 0,
      y := Var 1,
      t := abstract 1 "y" mk_nat (App (App f x) y),
      c := Const (const.user 1 mk_nat []),
      s := subst c 0 t in
  s

-- #eval foo.repr
-- #eval repr (foo.infer_type [])

end examples

end hol