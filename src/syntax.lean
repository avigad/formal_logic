/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

The syntax of simple type theory, i.e. inductive definitions of types and terms.

Notes:

When it comes to basic types, type constructors, and constants, we distinguish between "built in"
and "user" objects. The former are fixed for the implementation, and the implementation can refer
to them directly (for example, logical connectives, arithmetic symbols, types like nat and bool,
and type constructors like list, sum, and prod).

TODO: Factor out types for constants, basic types, etc. These can include more information
about the environment, source, pretty-printing, etc.

TODO: We do not have "local_constants". It is probably best to have these as special sorts of
constants, but we can revisit this decision.

TODO: For now, we won't handle polymorphic types, though we will eventually (mostly following
HOL light).

TODO: For now, use naive equality tests. We can worry about more efficient tests (e.g. with
unique id's) later, if necessary.

TODO: if we replace each `= tt` by a coercion to bool, things break in some places. They are 
fixable, but then something more dramatic breaks in fol.syntax and the terms are huge.
-/
import data.list

/- TODO: move these -/

@[simp]
theorem if_neg_eq {α : Type*} (p : Prop) [decidable p] (a b : α) : 
  (if ¬ p then a else b) = (if p then b else a) :=
begin
  by_cases h : p; simp [h],
end

theorem to_bool_eq_to_bool (p q : Prop) [decidable p] [decidable q] :
  (to_bool p = to_bool q) ↔ (p ↔ q) :=
by by_cases p; simp [h]

namespace list

@[simp]
theorem not_cons_prefix_nil {α : Type*} (a : α) (l : list α) : ¬ a :: l <+: nil :=
by { unfold is_prefix, intro h, cases h, contradiction }

@[simp]
theorem cons_prefix_cons {α : Type*} (a₁ a₂ : α) (l₁ l₂ : list α) :
  a₁ :: l₁ <+: a₂ :: l₂ ↔ a₁ = a₂ ∧ l₁ <+: l₂ :=
begin
  unfold is_prefix, 
  split; intro h,
  { cases h with l h, split, apply head_eq_of_cons_eq h, existsi l, apply tail_eq_of_cons_eq h},
  cases h with h₀ h₁, cases h₁ with l h₁,
  existsi l, rw [h₀, ← h₁], simp  
end

theorem length_le_of_prefix {α : Type*} {l₁ l₂ : list α} (h : l₁ <+: l₂) : length l₁ ≤ length l₂ :=
length_le_of_sublist $ sublist_of_prefix h

theorem prefix_iff_eq_of_length_eq {α : Type*} {l₁ l₂ : list α} (h : length l₁ = length l₂) :
  l₁ <+: l₂ ↔ (l₁ = l₂) :=
by { split, { intro h', exact eq_of_prefix_of_length_eq h' h}, intro h', rw h'}

theorem drop_succ {α : Type*} (n : nat) (l : list α) : drop n.succ l = drop n (drop 1 l) :=
by induction l; simp

theorem drop_eq_nil  {α : Type*} (n : nat) (l : list α) : drop n l = [] ↔ n ≥ l.length:=
begin
  revert n,  
  induction l with a l ih; simp, 
  { apply nat.zero_le }, 
  intro n, cases n with n; simp, 
  { rw add_comm, apply nat.zero_lt_succ },
  rw ih, rw [add_comm, ge, ge, nat.succ_le_succ_iff]
end

end list

namespace hol

/-
Instead of option, we'll have failure produce error messages. But we will not use the full-blown
exception monad or do anything fancy, to make it easier to reason about these programs.

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
| (Arr t₁ t₂)     l := arities_ok_aux t₁ l && arities_ok_aux t₂ l && l.empty
| (Constructor c) l := c.arity = l.length
| (App t₁ t₂)     l := arities_ok_aux t₂ [] && arities_ok_aux t₁ (t₂ :: l)

def arities_ok (t : type) : bool := arities_ok_aux t []

/-- Returns the domain of an arrow type, or the type itself if it is not an arrow. -/
@[simp]
def domain : type → type
| (type.Arr t₁ t₂) := t₁
| t                := t

/-- Returns the codomain of an arrow type, or the type itself if it is not an arrow. -/
@[simp]
def codomain : type → type
| (type.Arr t₁ t₂) := t₂ 
| t                := t

@[simp]
def get_arg_types : type → list type
| (type.Arr t₁ t₂) := t₁ :: get_arg_types t₂
| _                := []

@[simp]
def num_arg_types : type → nat
| (type.Arr t₁ t₂) := num_arg_types t₂ + 1
| _                := 0

lemma length_get_arg_types (t : type) : t.get_arg_types.length = t.num_arg_types :=
by induction t; simp [*]

@[simp]
def get_return_type : type → type 
| (type.Arr t₁ t₂) := get_return_type t₂
| t                := t

@[simp]
def mk_fn_type : list type → type → type 
| []        ret := ret
| (a :: as) ret := (type.Arr a (mk_fn_type as ret))

theorem mk_fn_type_eq (t : type) : t = mk_fn_type (get_arg_types t) (get_return_type t) :=
by { induction t; simp [get_arg_types, get_return_type, mk_fn_type], assumption }

@[simp]
theorem get_return_type_codomain (t : type) : get_return_type (t.codomain) = get_return_type t :=
by induction t; simp

theorem get_arg_types_codomain (t : type) : get_arg_types (t.codomain) = t.get_arg_types.drop 1 :=
by induction t; simp

@[simp]
def is_arrow : type → bool
| (Arr t₁ t₂) := tt
| _           := ff

theorem is_arrow_mk_fn_type (ts : list type) (t : type) (h : t.is_arrow = ff) :
  (mk_fn_type ts t).is_arrow = (ts ≠ []) :=
by induction ts; simp [h]

theorem is_arrow_get_return_type_eq_ff (t : type) : t.get_return_type.is_arrow = ff :=
by induction t; simp [*]

theorem eq_of_is_arrow (t : type) (h : is_arrow t = tt) : t = Arr (domain t) (codomain t) :=
by cases t; simp at h; trivial

lemma cons_prefix_get_arg_types (ty ty' : type) (tys : list type) :
  (ty :: tys) <+: ty'.get_arg_types ↔ 
    is_arrow ty' = tt ∧ ty = ty'.domain ∧ tys <+: ty'.codomain.get_arg_types :=
by cases ty'; simp

end type

/- convenient type constructors -/

section
open type

-- TODO: mark these as reducible?

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
    | ⟨kind.user n, t, l⟩       := "(const.user " ++ n.repr ++ " " ++ t.repr ++ " " ++ 
                                      l.repr ++ ")"
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

    -- TODO: delete this?
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

-- TODO: not needed?
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

@[simp]
def is_var : term → bool
| (Var n) := tt
| _       := ff

def var_num : term → nat
| (Var n) := n
| _       := 0

@[simp]
def is_const : term → bool
| (Const c) := tt
| _         := ff

@[simp]
def is_app : term → bool
| (App f a) := tt
| _         := ff

def app_fn : term → term
| (App f a) := f
| t         := t

def app_arg : term → term
| (App f a) := a
| t         := t

@[simp]
def get_app_fn : term → term
| (App f a) := get_app_fn f
| t          := t

def get_app_num_args : term → ℕ 
| (App f a) := get_app_num_args f + 1
| t         := 0

def get_app_args_aux : term → list term → list term
| (App t₁ t₂)  args := get_app_args_aux t₁ (t₂ :: args)
| (Var n)      args := args
| (Const c)    args := args
| (Abs s ty t) args := args

def get_app_args (t : term) : list term := get_app_args_aux t []

@[simp]
def mk_app : term → list term → term
| t []       := t
| t (a::as)  := mk_app (App t a) as

theorem mk_app_get_app_aux (t : term) : 
  ∀ as, mk_app (get_app_fn t) (get_app_args_aux t as) = mk_app t as :=
by induction t; simp [get_app_fn, get_app_args_aux, mk_app, *]

theorem mk_app_get_app (t : term) : mk_app (get_app_fn t) (get_app_args t) = t :=
by simp [get_app_args, mk_app_get_app_aux, mk_app]

theorem not_is_app_get_app_fn (t : term) : is_app t.get_app_fn = ff :=
by { induction t with _ _ _ _ ih; simp, exact ih }

/-- Infers the type of a term, given an assignment to free variables. Assumes the expression is
    well-typed-/
def typeof : term → list type → type
| (Var n) σ       := if h : n < σ.length then σ.nth_le n h else mk_nat
| (Const c) σ     := c.type
| (App t₁ t₂) σ   := (typeof t₁ σ).codomain
| (Abs s ty t) σ  := ty ⇒ typeof t (ty :: σ)

inductive is_well_typed : term → list type → Prop
| wt_var (n : ℕ) (σ : list type) (h : n < σ.length)      : is_well_typed (Var n) σ
| wt_const (c : const) (σ : list type)                   : is_well_typed (Const c) σ
| wt_app (t₁ t₂ : term) (σ : list type) 
    (h₁ : is_well_typed t₁ σ) 
    (h₂ : is_well_typed t₂ σ) 
    (h₃ : (typeof t₁ σ).is_arrow = tt) 
    (h₄ : (typeof t₁ σ).domain = typeof t₂ σ)            : is_well_typed (App t₁ t₂) σ
| wt_abs (s : string) (ty : type) (t : term) 
      (σ : list type)
    (h₁ : is_well_typed t (ty :: σ))                     : is_well_typed (Abs s ty t) σ

/-- Infers the type of a term, given an assignment to free variables. Returns none of expression is
    not well-typed. -/
def typeof_p : term → list type → option type 
| (Var n)     σ  := σ.nth n
| (Const c)   σ  := some c.type 
| (App t₁ t₂) σ  := 
    match typeof_p t₁ σ, typeof_p t₂ σ with 
    | (some (type.Arr u v)), (some w) := if u = w then some v else none
    | _                    , _        := none
    end
| (Abs s ty t) σ := match typeof_p t (ty :: σ) with
                    | some ty₂ := some (type.Arr ty ty₂)
                    | _        := none
                    end

-- a boolean version
@[simp]
def is_well_typed_b : term → list type → bool
| (Var n)     σ := if n < σ.length then tt else ff
| (Const c)   σ := tt
| (App t₁ t₂) σ := is_well_typed_b t₁ σ && is_well_typed_b t₂ σ && 
                     (typeof t₁ σ).is_arrow && ((typeof t₁ σ).domain = typeof t₂ σ)
| (Abs s ty t) σ := is_well_typed_b t (ty :: σ)

theorem is_well_typed_iff (t : term) : 
  ∀ σ, is_well_typed t σ ↔ (is_well_typed_b t σ = tt) :=
begin
  induction t with _ _ _ _ h₁ h₂ _ ty _ h,
  {intro σ, split, {intro h, cases h; simp [*]}, intro h, simp at h, constructor, assumption},
  {intro σ, split, {intro h, cases h; simp [*]}, intro h, simp at h, constructor},
  {intro σ, simp [(h₁ σ).symm, (h₂ σ).symm], split, {intro h, cases h; simp [*]}, intro h, constructor; simp [*]},
  {intro σ, simp [(h (ty::σ)).symm], split, {intro h, cases h, assumption}, 
    intro h, constructor; simp [*]}
end

@[simp] lemma is_well_typed_of_is_const {t : term} {σ : list type} : 
  is_const t = tt → is_well_typed t σ :=
by { cases t; simp, constructor }

theorem is_well_typed_mk_app (l : list term) (σ : list type) :
  ∀ t, is_well_typed (mk_app t l) σ ↔ 
         is_well_typed t σ ∧ (∀ t' ∈ l, is_well_typed t' σ) ∧ 
           l.map (λ t', typeof t' σ) <+: (t.typeof σ).get_arg_types :=
begin
  induction l with t' l' ih,
  { simp [list.nil_prefix] },
  simp, intro t, rw [ih (App t t')], simp [is_well_typed_iff],
  split, 
  { intro h, simp [*, typeof] at *,
    rcases h with ⟨⟨h₀, h₁, h₂, h₃⟩, h₄, h₅⟩,  
    split, exact h₄, rw [type.eq_of_is_arrow _ h₂],
    simp, rw [h₃], simp, exact h₅},
  intro h, rcases h with ⟨h,  ⟨h₀, h₁⟩, h₂⟩,
  have h₃ := (type.cons_prefix_get_arg_types _ _ _).mp h₂,
  rcases h₃ with ⟨h₃, h₄, h₅⟩,
  simp [h, h₀, h₁, h₃, h₄, h₅, typeof],
  assumption  
end

theorem is_well_typed_iff' {t : term} {σ : list type} :
  t.is_well_typed σ ↔ 
    is_well_typed (t.get_app_fn) σ ∧ (∀ t' ∈ t.get_app_args, is_well_typed t' σ) ∧ 
           t.get_app_args.map (λ t', typeof t' σ) <+: (t.get_app_fn.typeof σ).get_arg_types :=
by { rw [← mk_app_get_app t, is_well_typed_mk_app], simp [mk_app_get_app] }

theorem typeof_mk_app (t: term) (as : list term) (σ : list type) :
  typeof (mk_app t as) σ = 
    type.mk_fn_type (((t.typeof σ).get_arg_types).drop (as.length)) 
      (t.typeof σ).get_return_type :=
begin
  revert t, 
  induction as with a as ih, 
  { intro t, simp, rw ← type.mk_fn_type_eq (t.typeof σ) },
  intro t, simp, rw (ih (App t a)), simp [typeof], rw [add_comm, list.drop_add],
  simp [type.get_arg_types_codomain]
end

theorem is_arrow_get_app_fn_of_is_arrow (t : term)(σ : list type) (h : t.is_well_typed σ) 
  (h' : (t.typeof σ).is_arrow = tt) : (t.get_app_fn.typeof σ).is_arrow = tt :=
begin
  revert h h', 
  induction t with _ _ _ _ ih; simp,
  rintro ⟨h₀, h₁, h₂, h₃⟩, intro h'',
  apply ih; assumption
end

theorem is_arrow_get_app_fn_of_is_app {t : term} {σ : list type} (h : t.is_well_typed σ) 
  (h' : is_app t = tt) : ((t.get_app_fn).typeof σ).is_arrow = tt :=
begin
  revert h h',
  cases t; simp,
  intro h, cases h,
  apply is_arrow_get_app_fn_of_is_arrow; assumption
end

theorem typeof_mk_app_is_arrow (t: term) (as : list term) (σ : list type) :
  (typeof (mk_app t as) σ).is_arrow = (as.length < (t.typeof σ).num_arg_types) := 
begin
  rw [typeof_mk_app, type.is_arrow_mk_fn_type, to_bool_eq_to_bool, ne, list.drop_eq_nil,
    lt_iff_not_ge, type.length_get_arg_types], --simp [- bool.to_bool_not],
  apply type.is_arrow_get_return_type_eq_ff
end

theorem length_le_num_arg_types_typeof  {t: term} {as : list term} {σ : list type} 
    (h : is_well_typed (mk_app t as) σ) :
  as.length ≤ (t.typeof σ).num_arg_types :=
begin
  have : as.map (λ t', typeof t' σ) <+: (t.typeof σ).get_arg_types, 
    from ((is_well_typed_mk_app as σ t).mp h).right.right,
  have := list.length_le_of_prefix this,
  simpa [type.length_get_arg_types]
end

theorem length_get_app_args_of_not_is_arrow {t : term} {σ : list type} 
    (h : (t.typeof σ).is_arrow = ff) (h' : t.is_well_typed σ) :
  t.get_app_args.length = (t.get_app_fn.typeof σ).num_arg_types :=
begin
  rw ← mk_app_get_app t at h h',
  have : t.get_app_args.length ≤ (t.get_app_fn.typeof σ).num_arg_types,
    from length_le_num_arg_types_typeof h',
  by {apply le_antisymm this, rw typeof_mk_app_is_arrow at h, simp at h, exact h }
end

theorem get_arg_types_typeof_get_app_fn {t : term} {σ : list type} (h : (t.typeof σ).is_arrow = ff)
     (h' : t.is_well_typed σ) :
  (t.get_app_fn.typeof σ).get_arg_types = t.get_app_args.map (λ t', t'.typeof σ) :=
begin
  have : t.get_app_args.length = (t.get_app_fn.typeof σ).num_arg_types,
    from length_get_app_args_of_not_is_arrow h h',
  rw ← mk_app_get_app t at h h',
  have : t.get_app_args.map (λ t', typeof t' σ) <+: (t.get_app_fn.typeof σ).get_arg_types,
    from ((is_well_typed_mk_app t.get_app_args σ t.get_app_fn).mp h').right.right,
  have : t.get_app_args.map (λ t', typeof t' σ) = (t.get_app_fn.typeof σ).get_arg_types,
    by { apply list.eq_of_prefix_of_length_eq this, rw type.length_get_arg_types, simp, assumption},
  exact this.symm
end

theorem is_well_typed_of_not_is_arrow {t : term} {σ : list type} (h : (t.typeof σ).is_arrow = ff) :
  t.is_well_typed σ ↔ 
    is_well_typed (t.get_app_fn) σ ∧ 
    (∀ t' ∈ t.get_app_args, is_well_typed t' σ) ∧ 
    t.get_app_args.map (λ t', typeof t' σ) = (t.get_app_fn.typeof σ).get_arg_types :=
begin
  split; intro h',
  { have h₀ := is_well_typed_iff'.mp h',
    rcases h₀ with ⟨h₀, h₁, h₂⟩,
    split, apply h₀,
    split, apply h₁, 
    apply list.eq_of_prefix_of_length_eq h₂, simp,
    rw length_get_app_args_of_not_is_arrow h h',
    rw [type.length_get_arg_types] },
  rw is_well_typed_iff',    
  rcases h' with ⟨h₀, h₁, h₂⟩,
  split, apply h₀,
  split, apply h₁, 
  rw h₂ 
end

theorem typeof_eq_of_not_is_arrow {t : term} {σ : list type} 
    (h : (t.typeof σ).is_arrow = ff) (h' : t.is_well_typed σ) :
  t.typeof σ = ((t.get_app_fn).typeof σ).get_return_type :=
begin
  have h₀ : t.typeof σ = (mk_app t.get_app_fn t.get_app_args).typeof σ,
    by rw mk_app_get_app,
  transitivity, exact h₀,
  rw [typeof_mk_app, length_get_app_args_of_not_is_arrow h h', ← type.length_get_arg_types],
  rw (list.drop_eq_nil _ _).mpr, simp, apply le_refl
end

lemma type_is_not_arrow' {t : term} {σ : list type} (h : is_well_typed t σ) :
  (t.typeof σ).is_arrow = ff ↔ 
     (t.get_app_fn.typeof σ).get_arg_types = (t.get_app_args).map (λ t', t'.typeof σ) :=
begin
  split,
  { intro h₀,
    rw [get_arg_types_typeof_get_app_fn h₀ h] },
  intro h,
  rw ← mk_app_get_app t,
  rw typeof_mk_app,
  have : (get_app_args t).length = (t.get_app_fn.typeof σ).get_arg_types.length,
    by { rw h, simp },
  rw this, rw (list.drop_eq_nil _ _).mpr (le_refl _),
  apply type.is_arrow_get_return_type_eq_ff
end

-- an inductive characterization of well typed terms whose types are not arrows 
theorem type_is_not_arrow_iff {σ : list type} : 
  ∀ {t : term}, t.is_well_typed σ → 
    ((t.typeof σ).is_arrow = ff ↔
      (t.is_var = tt ∧ (t.typeof σ).is_arrow = ff) ∨ 
      (t.is_const = tt ∧ (t.typeof σ).is_arrow = ff) ∨ 
      (t.is_app = tt ∧ 
          (t.get_app_fn.typeof σ).get_arg_types = t.get_app_args.map (λ t', t'.typeof σ))) :=
begin
  intro t, 
  induction t with _ _ t₁ t₂ ih₁ ih₂; simp,
  { intro h', simp [type_is_not_arrow' h'] },
  simp [typeof]
end

end term

end hol