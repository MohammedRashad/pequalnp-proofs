import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3266
open PEqualNP.CircuitLowerBounds

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem len_foldl (gs : List Gate) (a : List Bool) :
    (gs.foldl stepW a).length = a.length + gs.length := by
  induction gs generalizing a with
  | nil => simp
  | cons g gs ih => simp [List.foldl, ih, stepW]; omega

theorem getD_snoc (A : List Bool) (x : Bool) (w : ℕ) :
    (A ++ [x]).getD w false =
      if w < A.length then A.getD w false else if w = A.length then x else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split_ifs with h1 h2
  · rfl
  · subst h2; simp
  · have : w - A.length ≠ 0 := by omega
    rw [List.getElem?_eq_none]
    · rfl
    · simp; omega

def rset (g : Gate) : Finset ℕ :=
  match g.op with
  | GateOp.not => (g.inputs.take 1).toFinset
  | _ => g.inputs.toFinset

theorem rset_card (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    (rset g).card ≤ 1 + (if (!g.op.eval [false]) = true then 1 else 0) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨h1, h2⟩ := hg
  simp only at h1 h2
  rcases h1 with h | h | h <;> subst h
  · have := List.toFinset_card_le inputs
    simp [rset, GateOp.eval]; omega
  · have := List.toFinset_card_le inputs
    simp [rset, GateOp.eval]; omega
  · have := List.toFinset_card_le (inputs.take 1)
    have h3 : (inputs.take 1).length ≤ 1 := by simp
    simp only [rset, GateOp.eval]
    simp
    omega

theorem gate_eq (g : Gate) (u v : List Bool)
    (h : ∀ i ∈ rset g, u.getD i false = v.getD i false) :
    g.op.eval (g.inputs.map fun i => u.getD i false) =
      g.op.eval (g.inputs.map fun i => v.getD i false) := by
  obtain ⟨op, inputs⟩ := g
  have hm : (∀ i ∈ inputs, u.getD i false = v.getD i false) →
      op.eval (inputs.map fun i => u.getD i false) =
        op.eval (inputs.map fun i => v.getD i false) := by
    intro hh
    have : (inputs.map fun i => u.getD i false) = (inputs.map fun i => v.getD i false) :=
      List.map_congr_left hh
    rw [this]
  cases op with
  | not =>
    simp only [rset] at h
    cases inputs with
    | nil => rfl
    | cons i rest =>
      have := h i (by simp)
      simp only [GateOp.eval, List.map_cons, List.headD_cons, this]
  | and => exact hm (fun i hi => h i (by simpa [rset] using hi))
  | or => exact hm (fun i hi => h i (by simpa [rset] using hi))
  | mod m => exact hm (fun i hi => h i (by simpa [rset] using hi))
  | maj => exact hm (fun i hi => h i (by simpa [rset] using hi))

theorem stepW_getD (A : List Bool) (g : Gate) (w : ℕ) :
    (stepW A g).getD w false =
      if w < A.length then A.getD w false
      else if w = A.length then g.op.eval (g.inputs.map fun i => A.getD i false) else false :=
  getD_snoc _ _ _

theorem key (n : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) (W : Finset ℕ) :
    ∃ S : Finset ℕ, S.card ≤ gs.countP (fun g => !g.op.eval [false]) + W.card ∧
      ∀ a b : List Bool, a.length = n → b.length = n →
        (∀ i ∈ S, a.getD i false = b.getD i false) →
        ∀ w ∈ W, (gs.foldl stepW a).getD w false = (gs.foldl stepW b).getD w false := by
  induction gs using List.reverseRecOn generalizing W with
  | nil =>
    refine ⟨W, by simp, ?_⟩
    intro a b _ _ hab w hw
    exact hab w hw
  | append_singleton init g ih =>
    have hinit : ∀ g' ∈ init, (g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not) ∧
        g'.inputs.length ≤ 2 := fun g' hg' => hgs g' (List.mem_append_left _ hg')
    have hg := hgs g (by simp)
    obtain ⟨S, hS1, hS2⟩ := ih hinit
      (W.erase (n + init.length) ∪ (if n + init.length ∈ W then rset g else ∅))
    refine ⟨S, ?_, ?_⟩
    · have hc := rset_card g hg
      have hW' : (W.erase (n + init.length) ∪
          (if n + init.length ∈ W then rset g else ∅)).card ≤
          W.card + (if (!g.op.eval [false]) = true then 1 else 0) := by
        by_cases hL : n + init.length ∈ W
        · rw [if_pos hL]
          have h1 := Finset.card_union_le (W.erase (n + init.length)) (rset g)
          have h2 := Finset.card_erase_of_mem hL
          have h3 : 0 < W.card := Finset.card_pos.mpr ⟨_, hL⟩
          omega
        · rw [if_neg hL, Finset.union_empty, Finset.erase_eq_of_notMem hL]
          omega
      rw [List.countP_append]
      simp only [List.countP_cons, List.countP_nil] at hS1 ⊢
      omega
    · intro a b ha hb hab w hw
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hla : (init.foldl stepW a).length = n + init.length := by rw [len_foldl, ha]
      have hlb : (init.foldl stepW b).length = n + init.length := by rw [len_foldl, hb]
      rw [stepW_getD, stepW_getD, hla, hlb]
      split_ifs with h1 h2
      · exact hS2 a b ha hb hab w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by omega, hw⟩))
      · apply gate_eq
        intro i hi
        apply hS2 a b ha hb hab i
        have hL : n + init.length ∈ W := h2 ▸ hw
        rw [if_pos hL]
        exact Finset.mem_union_right _ hi
      · rfl

end PEqualNP.Outside.L_meta_3266

theorem PEqualNP.Outside.L_meta_3266 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → ∃ (x4 : Finset ℕ), x4.card ≤ List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => !x5.op.eval [Bool.false]) x2.gates + (1 : ℕ) ∧ ∀ (x5 x6 : List Bool), x5.length = x1 → x6.length = x1 → (∀ x9 ∈ x4, x5.getD x9 Bool.false = x6.getD x9 Bool.false) → x2.eval x5 = x2.eval x6 := by
  intro n C hC
  obtain ⟨S, h1, h2⟩ := PEqualNP.Outside.L_meta_3266.key n C.gates
    (fun g hg => by simpa using hC g hg) {C.output}
  refine ⟨S, by simpa using h1, fun a b ha hb hab => h2 a b ha hb hab C.output (by simp)⟩
