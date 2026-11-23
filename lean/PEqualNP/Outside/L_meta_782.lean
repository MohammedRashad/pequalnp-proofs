import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_782

open PEqualNP.CircuitLowerBounds

def stepF (l : List Bool) (g : Gate) : List Bool :=
  l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepF x := rfl

lemma foldl_prefix (gs : List Gate) : ∀ l : List Bool, ∃ r : List Bool,
    gs.foldl stepF l = l ++ r ∧ r.length = gs.length := by
  induction gs with
  | nil => intro l; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro l
    obtain ⟨r, hr, hl⟩ := ih (stepF l g)
    refine ⟨g.op.eval (g.inputs.map fun i => l.getD i false) :: r, ?_, ?_⟩
    · rw [List.foldl_cons, hr]; simp [stepF]
    · simp [hl]

lemma getD_app_left (l r : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ r).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_out (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

def V (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma V_input (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) (h : w < n) :
    V C n x w = x ⟨w, h⟩ := by
  obtain ⟨r, hr, -⟩ := foldl_prefix C.gates (List.ofFn x)
  unfold V
  rw [wires_eq, hr, getD_app_left _ _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

lemma V_high (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) (h : n + C.gates.length ≤ w) :
    V C n x w = false := by
  obtain ⟨r, hr, hl⟩ := foldl_prefix C.gates (List.ofFn x)
  unfold V
  rw [wires_eq, hr]
  apply getD_out
  simp [hl]; omega

lemma V_gate (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    V C n x (n + j) = (C.gates[j]).op.eval ((C.gates[j]).inputs.map
      fun u => if u < n + j then V C n x u else false) := by
  set P := (C.gates.take j).foldl stepF (List.ofFn x) with hP
  obtain ⟨r0, hr0, hl0⟩ := foldl_prefix (C.gates.take j) (List.ofFn x)
  have hPl : P.length = n + j := by
    rw [hP, hr0]; simp [hl0, List.length_take, Nat.min_eq_left hj.le]
  obtain ⟨r, hr, -⟩ := foldl_prefix (C.gates.drop (j + 1)) (stepF P C.gates[j])
  have hW : C.wires (List.ofFn x) = P ++ ([(C.gates[j]).op.eval
      ((C.gates[j]).inputs.map fun i => P.getD i false)] ++ r) := by
    rw [wires_eq]
    conv_lhs => rw [← List.take_append_drop j C.gates, List.drop_eq_getElem_cons hj]
    rw [List.foldl_append, List.foldl_cons, ← hP, hr]
    simp [stepF]
  have hPV : ∀ i, P.getD i false = if i < n + j then V C n x i else false := by
    intro i
    split_ifs with hi
    · unfold V; rw [hW, getD_app_left _ _ _ (by omega)]
    · exact getD_out _ _ (by omega)
  rw [show V C n x (n + j) = (C.wires (List.ofFn x)).getD (n + j) false from rfl, hW]
  conv_lhs => rw [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega)]
  simp only [hPl, Nat.sub_self]
  simp only [List.cons_append, List.getElem?_cons_zero, Option.getD_some]
  congr 2
  funext i
  exact hPV i

def ea (n : ℕ) (a : Fin n) : Fin n → Bool := fun b => decide (b = a)

def T (C : Circuit) (n : ℕ) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun a => V C n (ea n a) w = true)

def priv (C : Circuit) (n : ℕ) (S : Finset (Fin n)) (w : ℕ) : Prop :=
  T C n w ⊆ S ∧ 2 ≤ (T C n w).card

def ins (C : Circuit) (n : ℕ) (w : ℕ) : List ℕ :=
  (C.gates.getD (w - n) ⟨GateOp.and, []⟩).inputs

lemma gate_at (C : Circuit) (n w : ℕ) (hn : n ≤ w) (hw : w < n + C.gates.length) :
    ∃ g ∈ C.gates, ins C n w = g.inputs ∧ ∀ y : Fin n → Bool,
      V C n y w = g.op.eval (g.inputs.map fun u => if u < w then V C n y u else false) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hj : j < C.gates.length := by omega
  refine ⟨C.gates[j], List.getElem_mem hj, ?_, fun y => V_gate C n y j hj⟩
  simp [ins, List.getD_eq_getElem?_getD, hj]

lemma eval2 (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (u v : ℕ)
    (hi : g.inputs = [u, v]) (f : ℕ → Bool) :
    g.op.eval (g.inputs.map f) = true ↔
      (g.op = GateOp.and ∧ f u = true ∧ f v = true) ∨
        (g.op = GateOp.or ∧ (f u = true ∨ f v = true)) := by
  rcases hop with h | h <;> simp [hi, h, GateOp.eval]

lemma V_mono (C : Circuit) (n : ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (x y : Fin n → Bool) (hxy : ∀ q, x q = true → y q = true) :
    ∀ w, V C n x w = true → V C n y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw
  by_cases h1 : w < n
  · rw [V_input _ _ _ _ h1] at hw ⊢; exact hxy _ hw
  by_cases h2 : n + C.gates.length ≤ w
  · rw [V_high _ _ _ _ h2] at hw; exact absurd hw (by simp)
  obtain ⟨g, hgm, -, hV⟩ := gate_at C n w (by omega) (by omega)
  obtain ⟨hop, hl⟩ := hg g hgm
  obtain ⟨u, v, huv⟩ := List.length_eq_two.mp hl
  rw [hV, eval2 g hop u v huv] at hw
  rw [hV, eval2 g hop u v huv]
  have key : ∀ t, (if t < w then V C n x t else false) = true →
      (if t < w then V C n y t else false) = true := by
    intro t ht
    split_ifs at ht ⊢ with h
    exact ih t h ht
  rcases hw with ⟨h, a, b⟩ | ⟨h, a | b⟩
  · exact Or.inl ⟨h, key _ a, key _ b⟩
  · exact Or.inr ⟨h, Or.inl (key _ a)⟩
  · exact Or.inr ⟨h, Or.inr (key _ b)⟩

lemma priv_range (C : Circuit) (n : ℕ) (S : Finset (Fin n)) (w : ℕ) (h : priv C n S w) :
    n ≤ w ∧ w < n + C.gates.length := by
  obtain ⟨-, h2⟩ := h
  constructor
  · by_contra hlt
    push Not at hlt
    have hs : T C n w ⊆ {⟨w, hlt⟩} := by
      intro a ha
      simp only [T, Finset.mem_filter, V_input _ _ _ _ hlt, ea, decide_eq_true_eq] at ha
      simp [ha.2]
    have := Finset.card_le_card hs
    simp at this
    omega
  · by_contra hge
    push Not at hge
    have hs : T C n w = ∅ := by
      ext a
      simp [T, V_high _ _ _ _ hge]
    rw [hs] at h2
    simp at h2

lemma pickA {n : ℕ} (P : ℕ → Fin n → Prop) (S : Finset (Fin n)) (E : Finset ℕ)
    (hE : ∀ e ∈ E, ∃ a, P e a ∧ a ∉ S) :
    ∃ A : Finset (Fin n), A.card ≤ E.card ∧ (∀ a ∈ A, a ∉ S) ∧ ∀ e ∈ E, ∃ a ∈ A, P e a := by
  classical
  induction E using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp, by simp⟩
  | insert e E he ih =>
    obtain ⟨A, h1, h2, h3⟩ := ih (fun e' he' => hE e' (Finset.mem_insert_of_mem he'))
    obtain ⟨a, ha, haS⟩ := hE e (Finset.mem_insert_self e E)
    refine ⟨insert a A, ?_, ?_, ?_⟩
    · have := Finset.card_insert_le a A
      have h4 := Finset.card_insert_of_notMem he
      omega
    · intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact haS
      · exact h2 b hb
    · intro e' he'
      rcases Finset.mem_insert.mp he' with rfl | he'
      · exact ⟨a, Finset.mem_insert_self _ _, ha⟩
      · obtain ⟨b, hb, hpb⟩ := h3 e' he'
        exact ⟨b, Finset.mem_insert_of_mem hb, hpb⟩

lemma core (C : Circuit) (n : ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (S : Finset (Fin n)) (root k c : ℕ) (hroot : priv C n S root)
    (hprom : ∀ x : Fin n → Bool, (Finset.univ.filter (fun q => x q = true)).card ≤ k →
      (∀ q ∈ S, x q = false) → V C n x root = false)
    (hck : c ≤ k) (hcL : c + 1 ≤ (T C n root).card) :
    ∃ Q : Finset ℕ, (∀ w ∈ Q, priv C n S w) ∧ c ≤ Q.card := by
  classical
  let Step : ℕ → ℕ → Prop := fun q g => priv C n S g ∧ priv C n S q ∧ q < g ∧ q ∈ ins C n g
  let Rt : ℕ → Prop := fun q => Relation.ReflTransGen Step q root
  let Q := (Finset.range (n + C.gates.length)).filter (fun q => priv C n S q ∧ Rt q)
  let E := (Finset.range (n + C.gates.length)).filter
    (fun e => ¬ priv C n S e ∧ ∃ g ∈ Q, e ∈ ins C n g ∧ e < g)
  refine ⟨Q, fun w hw => (Finset.mem_filter.mp hw).2.1, ?_⟩
  have memQ : ∀ q, priv C n S q → Rt q → q ∈ Q := by
    intro q hq hR
    simp only [Q, Finset.mem_filter, Finset.mem_range]
    exact ⟨(priv_range C n S q hq).2, hq, hR⟩
  have hrootQ : root ∈ Q := memQ root hroot Relation.ReflTransGen.refl
  have hins : ∀ g, priv C n S g → ∃ u v, ins C n g = [u, v] := by
    intro g hpg
    obtain ⟨h1, h2⟩ := priv_range C n S g hpg
    obtain ⟨gg, hgm, hi, -⟩ := gate_at C n g h1 h2
    obtain ⟨u, v, huv⟩ := List.length_eq_two.mp (hg gg hgm).2
    exact ⟨u, v, hi.trans huv⟩
  have hcount : E.card ≤ Q.card + 1 := by
    let f : ℕ × ℕ → ℕ := fun p => (ins C n p.1).getD p.2 0
    have slot : ∀ g ∈ Q, ∀ t ∈ ins C n g, t ∈ (Q ×ˢ Finset.range 2).image f := by
      intro g hgQ t ht
      obtain ⟨u, v, huv⟩ := hins g (Finset.mem_filter.mp hgQ).2.1
      rw [huv] at ht
      rw [Finset.mem_image]
      rcases List.mem_pair.mp ht with rfl | rfl
      · exact ⟨(g, 0), by simp [hgQ], by simp [f, huv]⟩
      · exact ⟨(g, 1), by simp [hgQ], by simp [f, huv]⟩
    have hsub : Q.erase root ∪ E ⊆ (Q ×ˢ Finset.range 2).image f := by
      intro t ht
      rcases Finset.mem_union.mp ht with ht | ht
      · obtain ⟨hne, htQ⟩ := Finset.mem_erase.mp ht
        have hR : Rt t := (Finset.mem_filter.mp htQ).2.2
        rcases Relation.ReflTransGen.cases_head hR with h | ⟨g, hstep, hg'⟩
        · exact absurd h hne
        · exact slot g (memQ g hstep.1 hg') t hstep.2.2.2
      · obtain ⟨-, -, g, hgQ, hte, -⟩ := Finset.mem_filter.mp ht
        exact slot g hgQ t hte
    have hdisj : Disjoint (Q.erase root) E := by
      rw [Finset.disjoint_left]
      intro t h1 h2
      exact (Finset.mem_filter.mp h2).2.1 (Finset.mem_filter.mp (Finset.mem_erase.mp h1).2).2.1
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem hrootQ] at h1
    have h2 := Finset.card_image_le (s := Q ×ˢ Finset.range 2) (f := f)
    rw [Finset.card_product, Finset.card_range] at h2
    have h3 : 1 ≤ Q.card := Finset.card_pos.mpr ⟨root, hrootQ⟩
    omega
  have hE : c + 1 ≤ E.card := by
    by_contra hlt
    push Not at hlt
    let El := E.filter (fun e => ¬ T C n e ⊆ S)
    obtain ⟨A, hA1, hA2, hA3⟩ := pickA (fun e a => a ∈ T C n e) S El (by
      intro e he
      have h := (Finset.mem_filter.mp he).2
      rw [Finset.not_subset] at h
      obtain ⟨a, h1, h2⟩ := h
      exact ⟨a, h1, h2⟩)
    let x : Fin n → Bool := fun q => decide (q ∈ A)
    have hxroot : V C n x root = false := by
      apply hprom
      · have hA : Finset.univ.filter (fun q => x q = true) = A := by
          ext q
          simp [x]
        rw [hA]
        have hEl : El.card ≤ E.card := Finset.card_filter_le _ _
        omega
      · intro q hq
        simp only [x, decide_eq_false_iff_not]
        exact fun h => hA2 q h hq
    have hxEl : ∀ e ∈ E, ¬ T C n e ⊆ S → V C n x e = true := by
      intro e he hnot
      obtain ⟨a, haA, hae⟩ := hA3 e (Finset.mem_filter.mpr ⟨he, hnot⟩)
      have hv : V C n (ea n a) e = true := (Finset.mem_filter.mp hae).2
      refine V_mono C n hg (ea n a) x ?_ e hv
      intro q hq
      simp only [ea, decide_eq_true_eq] at hq
      subst hq
      simp [x, haA]
    have dich : ∀ w, priv C n S w → Rt w → ∀ a, V C n (ea n a) w = true →
        (∃ e ∈ E, T C n e = {a}) ∨ V C n x w = true := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
      intro hpw hRw a hva
      obtain ⟨hn, hN⟩ := priv_range C n S w hpw
      obtain ⟨g, hgm, hi, hV⟩ := gate_at C n w hn hN
      obtain ⟨hop, hl⟩ := hg g hgm
      obtain ⟨u, v, huv⟩ := List.length_eq_two.mp hl
      have hwQ : w ∈ Q := memQ w hpw hRw
      have operand : ∀ t ∈ g.inputs, (if t < w then V C n (ea n a) t else false) = true →
          (∃ e ∈ E, T C n e = {a}) ∨ (if t < w then V C n x t else false) = true := by
        intro t htin ht
        have htin' : t ∈ ins C n w := by rw [hi]; exact htin
        split_ifs at ht ⊢ with htw
        · by_cases hpt : priv C n S t
          · have hRt : Rt t := Relation.ReflTransGen.head ⟨hpw, hpt, htw, htin'⟩ hRw
            exact ih t htw hpt hRt a ht
          · have htE : t ∈ E := by
              simp only [E, Finset.mem_filter, Finset.mem_range]
              exact ⟨by omega, hpt, w, hwQ, htin', htw⟩
            by_cases hsub : T C n t ⊆ S
            · left
              refine ⟨t, htE, ?_⟩
              have hat : a ∈ T C n t := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩
              have hc : (T C n t).card ≤ 1 := by
                by_contra h
                push Not at h
                exact hpt ⟨hsub, h⟩
              rw [Finset.eq_singleton_iff_unique_mem]
              exact ⟨hat, fun b hb => Finset.card_le_one.mp hc b hb a hat⟩
            · right
              exact hxEl t htE hsub
      rw [hV, eval2 g hop u v huv] at hva
      rw [hV, eval2 g hop u v huv]
      have hu : u ∈ g.inputs := by simp [huv]
      have hv : v ∈ g.inputs := by simp [huv]
      rcases hva with ⟨h, h1, h2⟩ | ⟨h, h1 | h2⟩
      · rcases operand u hu h1 with r | r1
        · exact Or.inl r
        rcases operand v hv h2 with r | r2
        · exact Or.inl r
        exact Or.inr (Or.inl ⟨h, r1, r2⟩)
      · rcases operand u hu h1 with r | r1
        · exact Or.inl r
        · exact Or.inr (Or.inr ⟨h, Or.inl r1⟩)
      · rcases operand v hv h2 with r | r2
        · exact Or.inl r
        · exact Or.inr (Or.inr ⟨h, Or.inr r2⟩)
    have hall : ∀ a ∈ T C n root, ∃ e ∈ E, T C n e = {a} := by
      intro a ha
      rcases dich root hroot Relation.ReflTransGen.refl a (Finset.mem_filter.mp ha).2 with h | h
      · exact h
      · rw [hxroot] at h
        exact absurd h (by simp)
    let E' := E.filter (fun e => (T C n e).card = 1)
    have hsubT : T C n root ⊆ E'.biUnion (T C n) := by
      intro a ha
      obtain ⟨e, he, hTe⟩ := hall a ha
      rw [Finset.mem_biUnion]
      exact ⟨e, Finset.mem_filter.mpr ⟨he, by rw [hTe]; simp⟩, by rw [hTe]; simp⟩
    have h1 := (Finset.card_le_card hsubT).trans Finset.card_biUnion_le
    have h2 : ∑ e ∈ E', (T C n e).card = E'.card := by
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2)
    have h3 : E'.card ≤ E.card := Finset.card_filter_le _ _
    omega
  omega

end PEqualNP.Outside.L_meta_782

theorem PEqualNP.Outside.L_meta_782 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size := by
  intro n m k S C o c hS hL hg hLS hprom hck hcL
  have hT : ∀ i, PEqualNP.Outside.L_meta_782.T C n (o i) = Finset.univ.filter (fun a : Fin n =>
      (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true) :=
    fun i => rfl
  have core_i : ∀ i, ∃ Q : Finset ℕ, (∀ w ∈ Q, PEqualNP.Outside.L_meta_782.priv C n (S i) w) ∧
      c i ≤ Q.card := by
    intro i
    apply PEqualNP.Outside.L_meta_782.core C n hg (S i) (o i) k (c i)
    · refine ⟨?_, ?_⟩
      · intro a ha
        exact hLS i a (Finset.mem_filter.mp ha).2
      · rw [hT]
        exact hL i
    · exact hprom i
    · exact hck i
    · rw [hT]
      exact hcL i
  choose Q hQ1 hQ2 using core_i
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j ∈ (Finset.univ : Finset (Fin m)),
      i ≠ j → Disjoint (Q i) (Q j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro w hwi hwj
    obtain ⟨hs1, hc1⟩ := hQ1 i w hwi
    obtain ⟨hs2, -⟩ := hQ1 j w hwj
    have := Finset.card_le_card (Finset.subset_inter hs1 hs2)
    have := hS i j hij
    omega
  calc ∑ i, c i ≤ ∑ i, (Q i).card := Finset.sum_le_sum (fun i _ => hQ2 i)
    _ = (Finset.univ.biUnion Q).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.Ico n (n + C.gates.length)).card := by
        apply Finset.card_le_card
        intro w hw
        obtain ⟨i, -, hwi⟩ := Finset.mem_biUnion.mp hw
        obtain ⟨h1, h2⟩ := PEqualNP.Outside.L_meta_782.priv_range C n (S i) w (hQ1 i w hwi)
        exact Finset.mem_Ico.mpr ⟨h1, h2⟩
    _ = C.size := by simp [PEqualNP.CircuitLowerBounds.Circuit.size]
