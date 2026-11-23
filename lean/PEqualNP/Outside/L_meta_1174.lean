import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1174

open PEqualNP.CircuitLowerBounds

def gs : List Gate :=
  [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.or, [9, 4]⟩, ⟨GateOp.and, [0, 10]⟩,
    ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.and, [5, 13]⟩, ⟨GateOp.or, [11, 12]⟩,
    ⟨GateOp.or, [15, 14]⟩]

def circ : Circuit := ⟨gs, 16⟩

end PEqualNP.Outside.L_meta_1174

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_1174 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6) || (x 5 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1174.circ, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_1174.circ, PEqualNP.Outside.L_meta_1174.gs,
      List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide
