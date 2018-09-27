import data.encodable data.list

/- 
if `l` is a list of natural numbers, `maxn l` is its maximum. 

It is not clear what the right generalization of this is. 
We need a default element for the max of the empty list. What we really need is
`semilattice_sup with bot`. 
-/

namespace list

def maxn (l : list nat) : nat := l.foldr (λ m n, max m n) 0

@[simp]
theorem maxn_nil : maxn nil = 0 := by simp [maxn]

@[simp] 
theorem maxn_cons (a : nat) (l : list nat) : maxn (a :: l) = max a (l.maxn) :=
by simp [maxn]

lemma le_maxn (l : list nat) : ∀ a ∈ l, a ≤ maxn l :=
begin
  induction l with a l ih; simp,
  split, { apply le_max_left },
  intros a h, apply le_max_right_of_le,
  exact ih a h
end

lemma nth_le_le_maxn (l : list nat) (n : nat) (h : n < l.length) : nth_le l n h ≤ maxn l :=
by { apply le_maxn, apply nth_le_mem }

lemma maxn_le (l : list nat) (n : nat) : (∀ a ∈ l, a ≤ n) → l.maxn ≤ n :=
begin
  induction l with a l ih; simp [nat.zero_le],
  intros h h', 
  exact max_le h (ih h')
end

lemma maxn_le_of_nth_le_le (l : list nat) (n : nat) 
    (h : ∀ i (h : i < l.length), l.nth_le i h ≤ n) : 
  l.maxn ≤ n :=
begin
  apply maxn_le, intros a h', 
  rcases list.mem_iff_nth_le.mp h' with ⟨i, ⟨h₀, h₁⟩⟩,
  rw ← h₁, exact h i h₀  
end

theorem nth_le_of_fn' {α : Type*} {n} (f : fin n → α) (i : ℕ) (h : i < n) :
  nth_le (of_fn f) i ((length_of_fn f).symm ▸ h) = f ⟨i, h⟩ :=
by apply nth_le_of_fn f ⟨i, h⟩ 

end list

/-
`Wfin α ar` is the type of finitely branching trees with labels from α, where 
a node labeled `a` has `ar a` children. 
-/

inductive Wfin {α : Type*} (ar : α → ℕ)
| mk (a : α) (f : fin (ar a) → Wfin) : Wfin

namespace Wfin

variables {α : Type*} {ar : α → ℕ}

def depth : Wfin ar → ℕ 
| ⟨a, f⟩ := (list.of_fn (λ n, depth (f n))).maxn + 1

def not_depth_le_zero (t : Wfin ar) : ¬ t.depth ≤ 0 :=
by { cases t, rw [depth], apply nat.not_succ_le_zero }

lemma depth_lt_depth_mk (a : α) (f : fin (ar a) → Wfin ar) (i : fin (ar a)) :
  depth (f i) < depth ⟨a, f⟩ :=
begin
  unfold depth, apply nat.lt_succ_of_le,
  have : i.val < list.length (list.of_fn (λ (n : fin (ar a)), depth (f n))),
    by rw list.length_of_fn; exact i.is_lt,
  have h₁ := list.nth_le_le_maxn (list.of_fn (λ (n : fin (ar a)), depth (f n))) i.1 this,
  rw list.nth_le_of_fn at h₁, exact h₁
end
 
end Wfin

/-
Show  `Wfin` types are encodable.
-/

namespace encodable

@[reducible] private def Wfin' {α : Type*} (ar : α → ℕ) (n : ℕ) := 
{ t : Wfin ar // t.depth ≤ n}

variables {α : Type*} {ar : α → ℕ}

private def encodable_zero : encodable (Wfin' ar 0) :=
let f : Wfin' ar 0 → empty :=
      by { intro x, cases x with x h, exfalso, exact Wfin.not_depth_le_zero _ h },
    finv : empty → Wfin' ar 0 := 
      by { intro x, cases x} in
have ∀ x, finv (f x) = x, 
  by { intro x, cases x with x h, exfalso, exact Wfin.not_depth_le_zero _ h },
encodable.of_left_inverse _ _ this

private def f (n : ℕ) : Wfin' ar (n + 1) → Σ a : α, fin (ar a) → Wfin' ar n
| ⟨t, h⟩ := 
  begin
    cases t with a f, 
    have h₀ : ∀ i : fin (ar a), Wfin.depth (f i) ≤ n,
      from assume i, nat.le_of_lt_succ (lt_of_lt_of_le (Wfin.depth_lt_depth_mk _ _ _) h),
    exact ⟨a, λ i : fin (ar a), ⟨f i, h₀ i⟩⟩ 
  end

private def finv (n : ℕ) : 
  (Σ a : α, fin (ar a) → Wfin' ar n) → Wfin' ar (n + 1)
| ⟨a, f⟩ := 
  let f' := λ i : fin (ar a), (f i).val in
  have Wfin.depth ⟨a, f'⟩ ≤ n + 1, 
    begin
      unfold Wfin.depth, 
      apply add_le_add_right, 
      apply list.maxn_le_of_nth_le_le,
      intros i h, 
      rw list.length_of_fn at h,
      rw list.nth_le_of_fn' _ i h,
      apply (f ⟨i, h⟩).2
    end,
  ⟨⟨a, f'⟩, this⟩  

variable [encodable α]

private def encodable_succ (n : nat) (h : encodable (Wfin' ar n)) :
  encodable (Wfin' ar (n + 1)) :=
encodable.of_left_inverse (f n) (finv n)
  (by { intro t, cases t with t h, cases t with a fn, reflexivity })

instance : encodable (Wfin ar) :=
have h : encodable (Σ n, Wfin' ar n),
  begin
    apply_with encodable.sigma {instances := ff}, apply_instance, 
    intro n, 
    induction n with n ih,
    { apply encodable_zero },
    exact encodable_succ n ih
  end,
let f : Wfin ar → Σ n, Wfin' ar n := λ t, ⟨t.depth, ⟨t, le_refl _⟩⟩,
    finv : (Σ n, Wfin' ar n) → Wfin ar := λ p, p.2.1 in
have ∀ t, finv (f t) = t, from assume t, rfl,
@encodable.of_left_inverse _ _ h _ _ this

end encodable

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

private def mk_zero : fin 0 → Wfin (arity α)
| ⟨_, h⟩ := absurd h dec_trivial

private def mk_one (p : Wfin (arity α)) : fin 1 → Wfin (arity α)
| ⟨0, _⟩   := p
| ⟨n+1, h⟩ := absurd h dec_trivial

private def mk_two (p q : Wfin (arity α)) : fin 2 → Wfin (arity α)
| ⟨0, _⟩   := p
| ⟨1, _⟩   := q
| ⟨n+2, h⟩ := absurd h dec_trivial

private def f : prop_form α → Wfin (arity α) 
| (var a) := ⟨cvar a, mk_zero⟩
| (not p) := ⟨cnot, mk_one (f p)⟩
| (and p q) := ⟨cand, mk_two (f p) (f q)⟩       
| (or  p q) := ⟨cor, mk_two (f p) (f q)⟩

private def finv : Wfin (arity α) → prop_form α
| ⟨cvar a, fn⟩ := var a 
| ⟨cnot, fn⟩   := not (finv (fn ⟨0, dec_trivial⟩))
| ⟨cand, fn⟩   := and (finv (fn ⟨0, dec_trivial⟩)) (finv (fn ⟨1, dec_trivial⟩))       
| ⟨cor, fn⟩    := or (finv (fn ⟨0, dec_trivial⟩)) (finv (fn ⟨1, dec_trivial⟩))       

def encodable_constructors [encodable α] : encodable (constructors α) :=
by { unfold constructors, apply_instance }

local attribute [instance] encodable_constructors

instance [encodable α] : encodable (prop_form α) :=
encodable.of_left_inverse f finv 
  (by {intro p, induction p; simp [f, finv, mk_zero, mk_one, mk_two, *]})

end prop_form

