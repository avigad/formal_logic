import .syntax

namespace fol
open hol

def eval_arity (L : fol.language) (val : fin L.num_sorts → Type*) : 
  Π t : type, t.in_fo_language L = tt → Type*
| (type.Var n)         h := by { simp [type.in_fo_language] at h, contradiction } 
| (type.Basic b)       h := 
    begin
      cases b with n; 
        simp [type.in_fo_language, type.is_sort, type.is_prop] at h; try { contradiction },
      { exact (val ⟨n, h⟩) },
      exact Prop
    end
| (type.Arr t₁ t₂)     h :=
    begin
      simp [type.in_fo_language] at h,
      exact ((eval_arity t₁ h.left) → (eval_arity t₂ h.right)) 
    end
| (type.Constructor c) h := by { simp [type.in_fo_language] at h, contradiction } 
| (type.App t₁ t₂)     h := by { simp [type.in_fo_language] at h, contradiction } 

structure model (L : language) :=
(sort_val : fin L.num_sorts → Type*)
(symbol_val : Π i : fin L.num_symbols, eval_arity L sort_val (L.arity i) (L.arity_in_fo_language i))

end fol