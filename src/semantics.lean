import .hol data.bool

universe u

/- For now, we're only dealing with "pure" types, i.e. types without type
   variables and constructors -- only basic types and arrows.

   Also, the use of Type* is illusory. Because we interpret `nat`, `bool`, etc.
   as the corresponding elements of Type 1, Type* is forced to be Type 1.
   Maybe we can get around this with lifting.
-/

namespace hol

/-
structure model :=
(domain : Type*)
(const_val : term.const → domain)
(app : domain → domain → domain)
-/

namespace type

/- evaluate the value of a type modulo a partial assignment, `bval`, to basic types -/

namespace basic

def evalp (bval : ℕ → option Type*) : type.basic → option Type*
| (user n) := bval n
| prop     := some Prop
| nat      := some _root_.nat
| bool     := some _root_.bool
| int      := some _root_.int
| unit     := some _root_.unit

def ok (bval : ℕ → option Type*) : type.basic → _root_.bool
| (user n) := option.is_some (bval n)
| prop     := tt
| nat      := tt
| bool     := tt
| int      := tt
| unit     := tt

def eval (bval : ℕ → option Type*) : Π b : type.basic, b.ok bval = tt → Type*
| (user n) h := option.get h
| prop     h := _root_.bool
| nat      h := _root_.nat
| bool     h := _root_.bool
| int      h := _root_.int
| unit     h := _root_.unit

end basic

def lift_arrow : option Type* → option Type* → option Type*
| (some T₁) (some T₂) := some (T₁ → T₂)
| _         _         := none 

def evalp (bval : ℕ → option Type*) : type → option Type*
| (Var n)         := none
| (Basic b)       := basic.evalp bval b
| (Arr t₁ t₂)     := lift_arrow (evalp t₁) (evalp t₂)
| (Constructor _) := none
| (App _ _ )      := none

def ok (bval : ℕ → option Type*) : type → bool
| (Var n)         := ff
| (Basic b)       := b.ok bval
| (Arr t₁ t₂)     := ok t₁ && ok t₂ 
| (Constructor _) := ff
| (App _ _ )      := ff

def eval (bval : ℕ → option Type*) : Π t : type, t.ok bval → Type*
| (Var n)         h := by { simp [type.ok] at h, contradiction }
| (Basic b)       h := b.eval bval h
| (Arr t₁ t₂)     h := eval t₁ (bool.band_elim_left h) → 
                         eval t₂ (bool.band_elim_right h) 
| (Constructor _) h := by { simp [type.ok] at h, contradiction }
| (App _ _ )      h := by { simp [type.ok] at h, contradiction }

end type

/- For the moment, only closed terms, no quantifiers -/

section
local attribute [instance] classical.prop_decidable

noncomputable def classical_ball (T : Type*) (f : T → bool) : bool :=
if ∀ t : T, f t = bool.tt then bool.tt else bool.ff

noncomputable def classical_bex (T : Type*) (f : T → bool) : bool :=
if ∃ t : T, f t = bool.tt then bool.tt else bool.ff

end

namespace term

namespace const

inductive evaluates_to (bval : ℕ → option Type*) (cval : ℕ → option (Σ T : Type*, T)) : 
  const → Π T : Type*, T → Prop
| eval_user (n : ℕ) (h : option.is_some (cval n)) (t : hol.type) (l : list hol.type) : 
    evaluates_to ⟨kind.user n, t, l⟩ (option.get h).1 (option.get h).2
| eval_true  : evaluates_to ⟨kind.true, mk_prop, []⟩ bool bool.tt
| eval_false : evaluates_to ⟨kind.false, mk_prop, []⟩ bool bool.ff
| eval_not   : evaluates_to ⟨kind.not, mk_prop ⇒ mk_prop, []⟩ (bool → bool) bnot
| eval_and   : evaluates_to ⟨kind.and, mk_prop ⇒ mk_prop ⇒ mk_prop, []⟩ (bool → bool → bool) band
| eval_or    : evaluates_to ⟨kind.or, mk_prop ⇒ mk_prop ⇒ mk_prop, []⟩ (bool → bool → bool) bor
| eval_implies : evaluates_to ⟨kind.implies, mk_prop ⇒ mk_prop ⇒ mk_prop, []⟩ 
                    (bool → bool → bool) (λ b₁ b₂, bor (bnot b₁) b₂)
| eval_iff   : evaluates_to ⟨kind.iff, mk_prop ⇒ mk_prop ⇒ mk_prop, []⟩ 
                    (bool → bool → bool) (λ b₁ b₂, if b₁ = b₂ then bool.tt else bool.ff)
| eval_all (t : hol.type) (h : t.ok bval)  : 
                  let T := type.eval bval t h in
                  evaluates_to ⟨kind.all, (t ⇒ mk_prop) ⇒ mk_prop, [t]⟩ ((T → bool) → bool)
                    (classical_ball T)
| eval_ex  (t : hol.type) (h : t.ok bval)  : 
                  let T := type.eval bval t h in
                  evaluates_to ⟨kind.all, (t ⇒ mk_prop) ⇒ mk_prop, [t]⟩ ((T → bool) → bool)
                    (classical_bex T)
| eval_add   : evaluates_to ⟨kind.add, mk_nat ⇒ mk_nat ⇒ mk_nat, []⟩ (nat → nat → nat) nat.add
| eval_mul   : evaluates_to ⟨kind.mul, mk_nat ⇒ mk_nat ⇒ mk_nat, []⟩ (nat → nat → nat) nat.mul
| eval_sub   : evaluates_to ⟨kind.sub, mk_nat ⇒ mk_nat ⇒ mk_nat, []⟩ (nat → nat → nat) nat.sub
| eval_bval (b : bool) : evaluates_to ⟨kind.bval b, mk_bool, []⟩ bool b
| eval_nval (n : nat) : evaluates_to ⟨kind.nval n, mk_nat, []⟩ nat n

inductive ok (bval : ℕ → option Type*) (cval : ℕ → option (Σ T : Type*, T)) : 
  const → Prop
| ok_user (n : ℕ) (t : hol.type) (l : list hol.type) 
    (h₀ : option.is_some (cval n)) (h₁ : t.ok bval) 
    (h₂ : t.eval bval h₁ = (option.get h₀).fst ) : 
    ok ⟨kind.user n, t, l⟩
| ok_true  : ok ⟨kind.true, mk_prop, []⟩
| ok_false : ok ⟨kind.false, mk_prop, []⟩
| ok_not   : ok ⟨kind.not, mk_prop ⇒ mk_prop, []⟩
| ok_and   : ok ⟨kind.and, mk_prop ⇒ mk_prop ⇒ mk_prop, []⟩
| ok_or    : ok ⟨kind.or, mk_prop ⇒ mk_prop ⇒ mk_prop, []⟩
| ok_implies : ok ⟨kind.implies, mk_prop ⇒ mk_prop ⇒ mk_prop, []⟩
| ok_iff   : ok ⟨kind.iff, mk_prop ⇒ mk_prop ⇒ mk_prop, []⟩ 
--| ok_all (t : hol.type) (h : t.ok bval)  : 
--                  ok ⟨kind.all, (t ⇒ mk_prop) ⇒ mk_prop, [t]⟩
--| ok_ex  (t : hol.type) (h : t.ok bval)  : 
--                  ok ⟨kind.ex, (t ⇒ mk_prop) ⇒ mk_prop, [t]⟩
| ok_add   : ok ⟨kind.add, mk_nat ⇒ mk_nat ⇒ mk_nat, []⟩
| ok_mul   : ok ⟨kind.mul, mk_nat ⇒ mk_nat ⇒ mk_nat, []⟩
| ok_sub   : ok ⟨kind.sub, mk_nat ⇒ mk_nat ⇒ mk_nat, []⟩
| ok_bval (b : bool) : ok ⟨kind.bval b, mk_bool, []⟩
| ok_nval (n : nat) : ok ⟨kind.nval n, mk_nat, []⟩

def type_ok (bval : ℕ → option Type*) (cval : ℕ → option (Σ T : Type*, T)) :
  ∀ c : const, c.ok bval cval → c.type.ok bval
| ⟨kind.user n, t, l⟩ h := by cases h; assumption
| ⟨kind.true, t, k⟩ h := by cases h; apply eq.refl 
| ⟨kind.false, t, k⟩ h := by cases h; apply eq.refl 
| ⟨kind.not, t, k⟩ h := by cases h; apply eq.refl 
| ⟨kind.and, t, k⟩ h := by cases h; apply eq.refl 
| ⟨kind.or, t, k⟩ h := by cases h; apply eq.refl 
| ⟨kind.implies, t, k⟩ h := by cases h; apply eq.refl 
| ⟨kind.iff, t, k⟩ h := by cases h; apply eq.refl 
| ⟨kind.all, t, k⟩ h := by cases h; apply eq.refl 
| ⟨kind.ex, t, k⟩ h := by cases h; apply eq.refl 
| ⟨kind.add, t, k⟩ h := by cases h; apply eq.refl 
| ⟨kind.mul, t, k⟩ h := by cases h; apply eq.refl 
| ⟨kind.sub, t, k⟩ h := by cases h; apply eq.refl 
| ⟨kind.bval b, t, k⟩ h := by cases h; apply eq.refl 
| ⟨kind.nval n, t, k⟩ h := by cases h; apply eq.refl 

def eval (bval : ℕ → option Type*) (cval : ℕ → option (Σ T : Type*, T)) : 
  Π (c : const) (h : c.ok bval cval), 
    (c.type).eval bval (c.type_ok bval cval h) 
| c@⟨kind.user n, ty, l⟩ h := 
    have h' : option.is_some (cval n), by cases h; assumption,
    have h'' :  c.type.eval bval (c.type_ok bval cval h)  = (option.get h').fst,
      by {cases h, assumption}, 
    cast h''.symm (option.get h').snd
| c@⟨kind.true, _, _⟩     h := cast (by cases h; reflexivity) bool.tt 
| c@⟨kind.false, _, _⟩    h := cast (by cases h; reflexivity) bool.tt 
| c@⟨kind.not, _, _⟩      h := cast (by cases h; reflexivity) bnot  
| c@⟨kind.and, _, _⟩      h := cast (by cases h; reflexivity) band
| c@⟨kind.or, _, _⟩       h := cast (by cases h; reflexivity) bor
| c@⟨kind.implies, _, _⟩  h := 
    have h' : c.type.eval bval (c.type_ok bval cval h) = (bool → bool → bool),
      by {cases h, reflexivity}, 
    cast h'.symm (λ b₁ b₂, bor (bnot b₁) b₂) 
| c@⟨kind.iff, _, _⟩      h := 
    have h' : c.type.eval bval (c.type_ok bval cval h) = (bool → bool → bool),
      by {cases h, reflexivity},
    cast h'.symm (λ b₁ b₂, if b₁ = b₂ then bool.tt else bool.ff)
-- these are the noncomputable clauses 
--| ⟨kind.all, _, [t]⟩    h := have h' : t.ok bval, by cases h; assumption,
--                             let T := type.eval_safe bval t h' in
--                             ⟨((T → bool) → bool), (classical_ball T)⟩ 
--| ⟨kind.ex, _, [t]⟩     h := have h' : t.ok bval, by cases h; assumption,
--                             let T := type.eval_safe bval t h' in
--                             ⟨((T → bool) → bool), (classical_bex T)⟩ 
| c@⟨kind.add, _, _⟩      h := cast (by cases h; reflexivity) nat.add 
| c@⟨kind.mul, _, _⟩      h := cast (by cases h; reflexivity) nat.mul 
| c@⟨kind.sub, _, _⟩      h := cast (by cases h; reflexivity) nat.sub 
| c@⟨kind.bval b, _, _⟩   h := cast (by cases h; reflexivity) b 
| c@⟨kind.nval n, _, _⟩   h := cast (by cases h; reflexivity) n
| c@⟨kind.all, _, _⟩      h := false.elim (by cases h)
| c@⟨kind.ex, _, _⟩       h := false.elim (by cases h)


/- TODO: prove that `evaluates_to` agrees with `eval`. -/ 

end const

inductive evaluates_to (bval : ℕ → option Type*) (cval : ℕ → option (Σ T : Type*, T)) : 
  term → (list (Σ T : Type*, T)) → Π T : Type*, T → Prop
| eval_var {n : ℕ} {T : Type*} (σ : list (Σ T : Type*, T)) {h : n < σ.length} :
    evaluates_to (Var n) σ (σ.nth_le n h).fst (σ.nth_le n h).snd 
| eval_const {c : const} {T : Type*} {a : T} {σ} (h : c.evaluates_to bval cval T a) :
    evaluates_to (Const c) σ T a
| eval_app {t₁ t₂ : term} {σ} {T₁ T₂ : Type} {f : T₁ → T₂} {a : T₁}
      (h₁ : evaluates_to t₁ σ (T₁ → T₂) f) (h₂ : evaluates_to t₂ σ T₁ a) :
    evaluates_to (term.App t₁ t₂) σ T₂ (f a)
| eval_abs {s : string} {ty : type} {t : term} {σ} {T₁ T₂ : Type} {f : T₁ → T₂} {a : T₁}
      (h₁ : ty.evalp bval = some T₁) (h₂ : ∀ a : T₁, evaluates_to t (⟨T₁, a⟩ :: σ) T₂ (f a)) :
    evaluates_to (term.Abs s ty t) σ (T₁ → T₂) f

/-
inductive ok (bval : ℕ → option Type*) (cval : ℕ → option (Σ T : Type*, T)) : 
  term → list Type* → Prop
| ok_var {n : ℕ} (σ : list Type*) {h : n < σ.length}      : ok (Var n) σ
| ok_const {c : const} {σ} (h : c.well_typed bval cval)   : ok (Const c) σ
| ok_app {t₁ t₂ : term} {σ} (h₁ : ok t₁ σ) (h₂ : ok t₂ σ) : ok (term.App t₁ t₂) σ
| ok_abs {s : string} {ty : type} {t : term} {σ}  
      (h₁ : ty.ok bval = tt) (h₂ : ok t (ty.eval_safe bval h₁ :: σ)) :
    ok (term.Abs s ty t) σ
-/

/-
The reason it is so hard to write an evaluation function for a term is that there is
so much data, and constraints. To evaluate a term `t`, we need

  `σ` : a specification of the types of the free deBruijn indices  
  `bval` : an interpretation of basic types
  `cval` : an interpretation of constants 
  `l` : an assignment of values to the indices

and we need to know:

  `t` is well-typed with respect to `σ`, and `σ` assigns types to all free variables
  `bval` interprets all the relevant basic types
  `cval` interprets all the relevant constants, and assigns values of the right types
  `l` interprets all the relevant deBruin indices, and assigns values of the right types
-/

-- TODO: move the next three
def domain : type → type
| (type.Arr t₁ t₂) := t₁
| t                := t

def codomain : type → type
| (type.Arr t₁ t₂) := t₂ 
| t                := t

theorem ok_domain (bval : ℕ → option Type*): Π t : type, t.ok bval → (domain t).ok bval :=
begin
  intro t, induction t; try {exact id}, 
  simp [domain, type.ok], intro h, exact h.left
end

theorem ok_codomain (bval : ℕ → option Type*): Π t : type, t.ok bval → (codomain t).ok bval :=
begin
  intro t, induction t; try {exact id}, 
  simp [codomain, type.ok], intro h, exact h.right
end

inductive is_arrow : type → Prop
| arr_is_arrow (t₁ t₂ : type) : is_arrow (t₁ ⇒ t₂)

theorem eq_of_is_arrow (t : type) (h : is_arrow t) : t = (domain t ⇒ codomain t) :=
by cases h; reflexivity

inductive type_list_ok : term → list type → Prop
| ok_var (n : nat) (σ : list type) (h : n < σ.length) : type_list_ok (Var n) σ
| ok_const (c : const) (σ : list type)                : type_list_ok (Const c) σ
| ok_app (t₁ t₂ : term) (σ : list type) 
    (h₁ : type_list_ok t₁ σ) (h₂ : type_list_ok t₂ σ) : type_list_ok (App t₁ t₂) σ
| ok_abs (s : string) (ty : type) (t : term) 
    (σ : list type) (h : type_list_ok t (ty :: σ))    : type_list_ok (Abs s ty t) σ

def typeof' : Π (t : term) (σ : list type), type_list_ok t σ → type
| (Var n) σ h       := have h' : n < σ.length, by {cases h, assumption},
                       σ.nth_le n h'
| (Const c) σ h     := c.type
| (App t₁ t₂) σ h   := have h' : type_list_ok t₁ σ, by {cases h, assumption}, 
                       codomain (typeof' t₁ σ h')
| (Abs s ty t) σ h  := have h' : type_list_ok t (ty :: σ), by {cases h, assumption},
                       ty ⇒ typeof' t (ty :: σ) h'

def typeof : term → list type → type
| (Var n) σ       := if h : n < σ.length then σ.nth_le n h else mk_nat
| (Const c) σ     := c.type
| (App t₁ t₂) σ   := codomain (typeof t₁ σ)
| (Abs s ty t) σ  := ty ⇒ typeof t (ty :: σ)

inductive is_well_typed : term → list type → Prop
| wt_var (n : ℕ) (σ : list type) (h : n < σ.length)      : is_well_typed (Var n) σ
| wt_const (c : const) (σ : list type)                   : is_well_typed (Const c) σ
| wt_app (t₁ t₂ : term) (σ : list type) 
    (h₁ : is_well_typed t₁ σ) 
    (h₂ : is_well_typed t₂ σ) 
    (h₃ : is_arrow (typeof t₁ σ)) 
    (h₄ : domain (typeof t₁ σ) = typeof t₂ σ)            : is_well_typed (App t₁ t₂) σ
| wt_abs (s : string) (ty : type) (t : term) 
      (σ : list type)
    (h₁ : is_well_typed t (ty :: σ))                     : is_well_typed (Abs s ty t) σ


-- move
def eval_ext (bval : ℕ → option Type*) (t₁ t₂: type) (h : t₁ = t₂) : 
  ∀ h₁ h₂, t₁.eval bval h₁ = t₂.eval bval h₂ :=
by { rw h, intros, reflexivity }

-- this complicated predicate says that a term `t` is well-typed and we have the right
-- data to interpret it
inductive ok (bval : ℕ → option Type*) (cval : ℕ → option (Σ T : Type*, T)) : 
  Π (t : term) (σ : list type) (l : list (Σ T : Type*, T)), Prop
| var_ok (n : nat) (σ : list type) (l : list (Σ T : Type*, T))
    (h₀ : n < σ.length) (h₁ : n < l.length) (h₂ : (σ.nth_le n h₀).ok bval)
    (h₃ : (σ.nth_le n h₀).eval bval h₂ = (l.nth_le n h₁).fst) :
  ok (Var n) σ l
| const_ok (c : const) (σ : list type) (l : list (Σ T : Type*, T)) (h : c.ok bval cval) :
  ok (Const c) σ l
| app_ok (t₁ t₂ : term) (σ : list type) (l : list (Σ T : Type*, T))
    (h₁ : ok t₁ σ l) (h₂ : ok t₂ σ l) 
    (h₃ : is_arrow (typeof t₁ σ)) 
    (h₄ : domain (typeof t₁ σ) = typeof t₂ σ):
  ok (App t₁ t₂) σ l
| abs_ok (s : string) (ty : type) (t : term) (σ : list type) (l : list (Σ T : Type*, T)) 
    (h₀ : ty.ok bval)
    (h₁ : (typeof t (ty :: σ)).ok bval)
    (h₂ : let T := ty.eval bval h₀ in
          ∀ a : T, ok t (ty :: σ) (⟨T, a⟩ :: l)) :
  ok (Abs s ty t) σ l

def type_ok (bval : ℕ → option Type*) (cval : ℕ → option (Σ T : Type*, T)) : 
  Π (t : term) (σ : list type) (l : list (Σ T : Type*, T)) (h : t.ok bval cval σ l),
    (t.typeof σ).ok bval
| t@(Var n) σ l h := 
    have h₀ : n < σ.length, by cases h; assumption,
    have h' : t.typeof σ = σ.nth_le n h₀, by simp [typeof, h₀],
    by { rw h', cases h, assumption }
| (Const c) σ l h := 
    have h₀ : c.ok bval cval, by cases h; assumption,
    c.type_ok bval cval h₀
| (App t₁ t₂) σ l h :=
    have h₁ : t₁.ok bval cval σ l, by {cases h, assumption},
    by { simp [typeof], apply ok_codomain, apply type_ok t₁ σ l, assumption}  
| (Abs s ty t) σ l h := 
    by { simp [typeof, type.ok], cases h, split; assumption }

def eval (bval : ℕ → option Type*) (cval : ℕ → option (Σ T : Type*, T)) : 
  Π (t : term) (σ : list type) (l : list (Σ T : Type*, T)) (h : t.ok bval cval σ l), 
    (t.typeof σ).eval bval (t.type_ok bval cval σ l h)
| (Var n) σ l h := 
    have h₀ : n < σ.length, by cases h; assumption,
    have h₁ : n < l.length, by cases h; assumption,
    have h₂ : (σ.nth_le n h₀).ok bval, by cases h; assumption,
    have h₃ : (σ.nth_le n h₀).eval bval h₂ = (l.nth_le n h₁).fst, by cases h; assumption,
    have h₄ : (typeof (Var n) σ).eval bval ((Var n).type_ok bval cval σ l h) = 
        (l.nth_le n h₁).fst,
      by { rw ← h₃, apply eval_ext, simp [typeof, h₀] },
     cast h₄.symm (l.nth_le n h₁).snd 
| (Const c) σ l h :=
    have h : c.ok bval cval, by cases h; assumption,
    c.eval bval cval h
| (App t₁ t₂) σ l h :=
    have h₁ : t₁.ok bval cval σ l, by cases h; assumption,
    have h₂ : t₂.ok bval cval σ l, by cases h; assumption,
    have h₃ : is_arrow (typeof t₁ σ), by cases h; assumption,
    have h₄ : domain (typeof t₁ σ) = typeof t₂ σ, by cases h; assumption,
    have h₅ : typeof t₁ σ = (domain (typeof t₁ σ) ⇒ codomain (typeof t₁ σ)), from eq_of_is_arrow _ h₃,
    have h₆ : (typeof t₁ σ).ok bval, from t₁.type_ok bval cval σ l h₁, 
    have h₇ : (domain (typeof t₁ σ) ⇒ codomain (typeof t₁ σ)).ok bval, by rw ← h₅; exact h₆,
    have h₈ : (typeof t₁ σ).eval bval h₆ = (domain (typeof t₁ σ) ⇒ codomain (typeof t₁ σ)).eval bval h₇,
      from eval_ext bval _ _ h₅ _ _,
    have h₉ : (domain (typeof t₁ σ)).ok bval, from ok_domain _ _ h₆,
    have h₁₀ : (codomain (typeof t₁ σ)).ok bval, from ok_codomain _ _ h₆,
    have h₁₁ : (typeof t₁ σ).eval bval h₆ =
                  ((domain (typeof t₁ σ)).eval bval h₉ → (codomain (typeof t₁ σ)).eval bval h₁₀), 
      from h₈,
    have h₁₂ : (typeof t₂ σ).ok bval, from t₂.type_ok bval cval σ l h₂,
    have h₁₃ : (typeof t₂ σ).eval bval h₁₂ = (domain (typeof t₁ σ)).eval bval h₉, 
      from eval_ext bval _ _ h₄.symm _ _, 
    let  v₁ := eval t₁ σ l h₁,
         v₂ := eval t₂ σ l h₂ in
    (cast h₁₁ v₁) (cast h₁₃ v₂)
| (Abs s ty t) σ l h := 
    have h₀ : ty.ok bval, by cases h; assumption,
    have h₁ : (typeof t (ty :: σ)).ok bval, by cases h; assumption,
    let T := ty.eval bval h₀ in
    have h₂ : ∀ a : T, t.ok bval cval (ty :: σ) (⟨T, a⟩ :: l), by cases h; assumption,
    have h₃ : ∀ a : T, (typeof t (ty :: σ)).ok bval, 
      from assume a, type_ok bval cval t _ (⟨T, a⟩ :: l) (h₂ a),
    let v := λ a : T, eval t (ty :: σ) (⟨T, a⟩ :: l) (h₂ a) in
    have h₄ : (Π (a : T), type.eval bval (typeof t (ty :: σ)) (h₃ a)) = 
           type.eval bval (typeof (Abs s ty t) σ) ((Abs s ty t).type_ok bval cval σ l h), 
      from rfl, 
    cast h₄ v

end term

end hol

