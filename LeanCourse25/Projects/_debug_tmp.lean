import Mathlib

namespace Debug

abbrev Matα (α : Type) [CommRing α] (m : Nat) := Matrix (Fin m) (Fin m) α

section

variable {α : Type} [CommRing α] [Field α]
variable (A : Matα α 2) (h11 : A 1 1 ≠ 0)

example : (A 1 1)⁻¹ * A 1 1 = (1 : α) := by
  by_cases h0 : A 1 1 = 0
  · exact (h11 h0).elim
  · simp [h0]

end

end Debug
