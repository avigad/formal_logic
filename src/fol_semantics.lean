import .fol

namespace fol
open hol

def arity_val (L : fol.language) (val : fin L.num_sorts → Type*) : 
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
      exact ((arity_val t₁ h.left) → (arity_val t₂ h.right)) 
    end
| (type.Constructor c) h := by { simp [type.in_fo_language] at h, contradiction } 
| (type.App t₁ t₂)     h := by { simp [type.in_fo_language] at h, contradiction } 

structure model (L : language) :=
(sort_val : fin L.num_sorts → Type*)
(symbol_val : Π i : fin L.num_symbols, arity_val L sort_val (L.arity i) (L.arity_in_fo_language i))

end fol