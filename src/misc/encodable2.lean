import data.equiv.encodable data.equiv.list data.fin data.finset data.fintype

/-
`Wfin α ar` is the type of finitely branching trees with labels from α, where 
a node labeled `a` has `ar a` children. 
-/

inductive Wfin {α : Type*} (ar : α → ℕ)
| mk (a : α) (f : fin (ar a) → Wfin) : Wfin

namespace Wfin

variables {α : Type*} {ar : α → ℕ}

def depth : Wfin ar → ℕ 
| ⟨a, f⟩ := finset.sup finset.univ (λ n, depth (f n)) + 1

def not_depth_le_zero (t : Wfin ar) : ¬ t.depth ≤ 0 :=
by { cases t, apply nat.not_succ_le_zero }

lemma depth_lt_depth_mk (a : α) (f : fin (ar a) → Wfin ar) (i : fin (ar a)) :
  depth (f i) < depth ⟨a, f⟩ :=
nat.lt_succ_of_le (finset.le_sup (finset.mem_univ i))

end Wfin

/-
Show  `Wfin` types are encodable.
-/

namespace encodable

@[reducible] private def Wfin' {α : Type*} (ar : α → ℕ) (n : ℕ) := 
{ t : Wfin ar // t.depth ≤ n}

variables {α : Type*} {ar : α → ℕ}

private def encodable_zero : encodable (Wfin' ar 0) :=
let f    : Wfin' ar 0 → empty := λ ⟨x, h⟩, absurd h (Wfin.not_depth_le_zero _),
    finv : empty → Wfin' ar 0 := by { intro x, cases x} in
have ∀ x, finv (f x) = x, from λ ⟨x, h⟩, absurd h (Wfin.not_depth_le_zero _), 
encodable.of_left_inverse f finv this

private def f (n : ℕ) : Wfin' ar (n + 1) → Σ a : α, fin (ar a) → Wfin' ar n
| ⟨t, h⟩ := 
  begin
    cases t with a f, 
    have h₀ : ∀ i : fin (ar a), Wfin.depth (f i) ≤ n,
      from λ i, nat.le_of_lt_succ (lt_of_lt_of_le (Wfin.depth_lt_depth_mk a f i) h),
    exact ⟨a, λ i : fin (ar a), ⟨f i, h₀ i⟩⟩ 
  end

private def finv (n : ℕ) : 
  (Σ a : α, fin (ar a) → Wfin' ar n) → Wfin' ar (n + 1)
| ⟨a, f⟩ := 
  let f' := λ i : fin (ar a), (f i).val in
  have Wfin.depth ⟨a, f'⟩ ≤ n + 1, 
    from add_le_add_right (finset.sup_le (λ b h, (f b).2)) 1,
  ⟨⟨a, f'⟩, this⟩  

variable [encodable α]

private def encodable_succ (n : nat) (h : encodable (Wfin' ar n)) :
  encodable (Wfin' ar (n + 1)) :=
encodable.of_left_inverse (f n) (finv n)
  (by { intro t, cases t with t h, cases t with a fn, reflexivity })

instance : encodable (Wfin ar) :=
begin 
  haveI h' : Π n, encodable (Wfin' ar n) := 
    λ n, nat.rec_on n encodable_zero encodable_succ, 
  let f    : Wfin ar → Σ n, Wfin' ar n   := λ t, ⟨t.depth, ⟨t, le_refl _⟩⟩,
  let finv : (Σ n, Wfin' ar n) → Wfin ar := λ p, p.2.1,
  have : ∀ t, finv (f t) = t, from λ t, rfl,
  exact encodable.of_left_inverse f finv this
end

end encodable

/-
Make it easier to construct funtions from a small `fin`.
-/

namespace fin
variable {α : Type*}

def mk_fn0 : fin 0 → α 
| ⟨_, h⟩ := absurd h dec_trivial

def mk_fn1 (t : α) : fin 1 → α
| ⟨0, _⟩   := t
| ⟨n+1, h⟩ := absurd h dec_trivial

def mk_fn2 (s t : α) : fin 2 → α
| ⟨0, _⟩   := s
| ⟨1, _⟩   := t
| ⟨n+2, h⟩ := absurd h dec_trivial

attribute [simp] mk_fn0 mk_fn1 mk_fn2
end fin

/-
Show propositional formulas are encodable.
-/

inductive prop_form (α : Type*) 
| var : α → prop_form
| not : prop_form → prop_form
| and : prop_form → prop_form → prop_form
| or  : prop_form → prop_form → prop_form

namespace prop_form

private def constructors (α : Type*) := α ⊕ unit ⊕ unit ⊕ unit

local notation `cvar` a := sum.inl a 
local notation `cnot`   := sum.inr (sum.inl unit.star)
local notation `cand`   := sum.inr (sum.inr (sum.inr unit.star))
local notation `cor`    := sum.inr (sum.inr (sum.inl unit.star))

@[simp]
private def arity (α : Type*) : constructors α → nat
| (cvar a) := 0
| cnot     := 1
| cand     := 2
| cor      := 2

variable {α : Type*}

private def f : prop_form α → Wfin (arity α) 
| (var a)   := ⟨cvar a, fin.mk_fn0⟩
| (not p)   := ⟨cnot, fin.mk_fn1 (f p)⟩
| (and p q) := ⟨cand, fin.mk_fn2 (f p) (f q)⟩       
| (or  p q) := ⟨cor, fin.mk_fn2 (f p) (f q)⟩

private def finv : Wfin (arity α) → prop_form α
| ⟨cvar a, fn⟩ := var a 
| ⟨cnot, fn⟩   := not (finv (fn ⟨0, dec_trivial⟩))
| ⟨cand, fn⟩   := and (finv (fn ⟨0, dec_trivial⟩)) (finv (fn ⟨1, dec_trivial⟩))       
| ⟨cor, fn⟩    := or  (finv (fn ⟨0, dec_trivial⟩)) (finv (fn ⟨1, dec_trivial⟩))       

instance [encodable α] : encodable (prop_form α) :=
begin
  haveI : encodable (constructors α) :=
    by { unfold constructors, apply_instance },
  exact encodable.of_left_inverse f finv 
    (by { intro p, induction p; simp [f, finv, *] })
end

end prop_form
