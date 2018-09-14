axiom vm_checked {P : Prop} : P

open tactic

/-- Uses the vm to cerify a goal of the form t = tt, where t is a closed boolean term -/
meta def vm_check_tt : tactic unit := do
tgt ← target,
match tgt with
| `(%%t = tt) := do et ← eval_expr bool t,
                    match et with
                    | tt := applyc ``vm_checked
                    | ff := fail "goal is false"
                    end
| _           := fail "goal must be of the form t = tt"
end

def of_to_bool_eq_tt {P : Prop} [h₁ : decidable P] (h₂ : to_bool P = tt) : P :=
match h₁, h₂ with
| (decidable.is_true h_P), h₂   := h_P
| (decidable.is_false h_nP), h₂ := by contradiction
end

/-
meta def vm_check : tactic unit := do
tgt ← target,
apply `(@of_to_bool_eq_tt %%tgt) <|> fail "could not infer decidability",
vm_check_tt
-/

-- in analogy to dec_trivial
notation `vm_check` := of_to_bool_eq_tt (by vm_check_tt)
