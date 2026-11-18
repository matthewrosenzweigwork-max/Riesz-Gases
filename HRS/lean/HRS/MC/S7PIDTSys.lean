import HRS.MC.S7PIDTGauss
import HRS.MC.S7PIDTMom
import HRS.MC.S7PIDTId

/-!
# Packet PI-D, sub-packet T (part 10): the Gaussian system of a pair of dyadic node families

Given square-integrable `ℝ^r`-valued node families `g_i, g'_i` (`i ≤ N = 2^ν`) on `I` with
`∫_I ‖g_j - g_i‖² ≤ κ (j-i)/N`, `∫_I ‖g_i‖² ≤ κ` (and the same for `g'` with `κ'`), we produce one probability space with
finite Gaussian families `Y_i, Y'_i` such that

* (identity) `∫_I M[Φ g, Φ' g'] = E M[Φ Y, Φ' Y']` for all continuous linear maps `Φ, Φ'` of the node vector and bounded bilinear `M`;
* (sup) measurable majorants `S, S'` of all `‖Y_i‖`, `‖Y'_i‖` with `E S² ≤ 162 κ`, `E S'² ≤ 162 κ'`;
* (incr) measurable majorants `δ, δ'` of all one-step increments with `(E δ²)² ≤ 3 κ² / N`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDT

open HRS HRS.Sec7 HRS.MC.Sec7.PID

/-- ℕ-indexed extension of a finite family (constant after the last index) -/
def S7PIDT_ext {E Ω : Type*} (ν : ℕ) (Z : Fin (2 ^ ν + 1) → Ω → E) (k : ℕ) : Ω → E :=
  Z ⟨min k (2 ^ ν), Nat.lt_succ_of_le (min_le_right _ _)⟩

lemma S7PIDT_ext_eq {E Ω : Type*} (ν : ℕ) (Z : Fin (2 ^ ν + 1) → Ω → E) (k : ℕ) (hk : k ≤ 2 ^ ν) :
    S7PIDT_ext ν Z k = Z ⟨k, Nat.lt_succ_of_le hk⟩ := by
  simp only [S7PIDT_ext, min_eq_left hk]

/-- sup and maximal increment of one Gaussian family -/
theorem S7PIDT_side {r : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (ν : ℕ)
    (Yf : Fin (2 ^ ν + 1) → Ω → EuclideanSpace ℝ (Fin r)) (hm : ∀ i, Measurable (Yf i))
    (hL : ∀ i, MemLp (Yf i) 4 P) (κ : ℝ) (hκ : 0 ≤ κ)
    (hv4 : ∀ a b : Fin (2 ^ ν + 1), a.1 ≤ b.1 →
      ∫ ω, ‖Yf b ω - Yf a ω‖ ^ 4 ∂P ≤ 3 * (κ * (((b.1 : ℝ) - a.1) / 2 ^ ν)) ^ 2)
    (h0 : ∫ ω, ‖Yf 0 ω‖ ^ 2 ∂P ≤ κ) :
    (∃ S : Ω → ℝ, Measurable S ∧ (∀ ω, 0 ≤ S ω) ∧ (∀ ω, ∀ k ≤ 2 ^ ν, ‖S7PIDT_ext ν Yf k ω‖ ≤ S ω) ∧
        Integrable (fun ω => S ω ^ 2) P ∧ ∫ ω, S ω ^ 2 ∂P ≤ 162 * κ) ∧
      (∃ δ : Ω → ℝ, Measurable δ ∧ (∀ ω, 0 ≤ δ ω) ∧
        (∀ ω, ∀ k < 2 ^ ν, ‖S7PIDT_ext ν Yf (k + 1) ω - S7PIDT_ext ν Yf k ω‖ ≤ δ ω) ∧
        Integrable (fun ω => δ ω ^ 2) P ∧ (∫ ω, δ ω ^ 2 ∂P) ^ 2 ≤ 3 * κ ^ 2 / 2 ^ ν) := by
  set Z := S7PIDT_ext ν Yf with hZ
  have hZm : ∀ a b, Measurable fun ω => ‖Z a ω - Z b ω‖ := fun a b =>
    ((hm _).sub (hm _)).norm
  have hI4 : ∀ a b, a ≤ 2 ^ ν → b ≤ 2 ^ ν → Integrable (fun ω => ‖Z a ω - Z b ω‖ ^ 4) P := by
    intro a b ha hb
    rw [hZ, S7PIDT_ext_eq ν Yf a ha, S7PIDT_ext_eq ν Yf b hb]
    exact ((hL _).sub (hL _)).integrable_norm_pow (by norm_num)
  have hv : ∀ a b : ℕ, a ≤ b → b ≤ 2 ^ ν →
      ∫ ω, ‖Z b ω - Z a ω‖ ^ 4 ∂P ≤ 3 * (κ * (((b : ℝ) - a) / 2 ^ ν)) ^ 2 := by
    intro a b hab hb
    rw [hZ, S7PIDT_ext_eq ν Yf a (hab.trans hb), S7PIDT_ext_eq ν Yf b hb]
    exact hv4 _ _ hab
  have hZ00 : Z 0 = Yf 0 := by
    rw [hZ, S7PIDT_ext_eq ν Yf 0 (Nat.zero_le _)]; rfl
  have h0int : Integrable (fun ω => ‖Z 0 ω‖ ^ 2) P := by
    rw [hZ00]; exact ((hL 0).mono_exponent (by norm_num)).norm.integrable_sq
  refine ⟨?_, ?_⟩
  · refine S7PIDT_sup P ν Z hZm ?_ κ hκ hI4 hv h0int (by rw [hZ00]; exact h0)
    rw [hZ00]; exact (hm 0).norm
  · exact S7PIDT_del P ν Z hZm κ hI4 hv

theorem S7PIDT_sys {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {r : ℕ} (ν : ℕ) (I : Set ℝ)
    (g g' : ℕ → ℝ → EuclideanSpace ℝ (Fin r)) (κ κ' : ℝ) (hκ : 0 ≤ κ) (hκ' : 0 ≤ κ')
    (hg : ∀ i ≤ 2 ^ ν, MemLp (g i) 2 (volume.restrict I))
    (hg' : ∀ i ≤ 2 ^ ν, MemLp (g' i) 2 (volume.restrict I))
    (hv : ∀ i j, i ≤ j → j ≤ 2 ^ ν →
      ∫ u in I, ‖g j u - g i u‖ ^ 2 ≤ κ * (((j : ℝ) - i) / 2 ^ ν))
    (hv' : ∀ i j, i ≤ j → j ≤ 2 ^ ν →
      ∫ u in I, ‖g' j u - g' i u‖ ^ 2 ≤ κ' * (((j : ℝ) - i) / 2 ^ ν))
    (h0 : ∀ i ≤ 2 ^ ν, ∫ u in I, ‖g i u‖ ^ 2 ≤ κ) (h0' : ∀ i ≤ 2 ^ ν, ∫ u in I, ‖g' i u‖ ^ 2 ≤ κ') :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (Y Y' : ℕ → Ω → EuclideanSpace ℝ (Fin r)),
      (∀ (Φ Φ' : (Fin (2 ^ ν + 1) → EuclideanSpace ℝ (Fin r)) →L[ℝ] X) (M : X [×2]→L[ℝ] ℝ),
        Integrable (fun ω => M ![Φ (fun i => Y i.1 ω), Φ' (fun i => Y' i.1 ω)]) P ∧
        ∫ u in I, M ![Φ (fun i => g i.1 u), Φ' (fun i => g' i.1 u)] =
          ∫ ω, M ![Φ (fun i => Y i.1 ω), Φ' (fun i => Y' i.1 ω)] ∂P) ∧
      (∃ S S' : Ω → ℝ, Measurable S ∧ Measurable S' ∧ (∀ ω, 0 ≤ S ω) ∧ (∀ ω, 0 ≤ S' ω) ∧
        (∀ ω, ∀ k ≤ 2 ^ ν, ‖Y k ω‖ ≤ S ω) ∧ (∀ ω, ∀ k ≤ 2 ^ ν, ‖Y' k ω‖ ≤ S' ω) ∧
        Integrable (fun ω => S ω ^ 2) P ∧ Integrable (fun ω => S' ω ^ 2) P ∧
        ∫ ω, S ω ^ 2 ∂P ≤ 162 * κ ∧ ∫ ω, S' ω ^ 2 ∂P ≤ 162 * κ') ∧
      (∃ δ δ' : Ω → ℝ, Measurable δ ∧ Measurable δ' ∧ (∀ ω, 0 ≤ δ ω) ∧ (∀ ω, 0 ≤ δ' ω) ∧
        (∀ ω, ∀ k < 2 ^ ν, ‖Y (k + 1) ω - Y k ω‖ ≤ δ ω) ∧
        (∀ ω, ∀ k < 2 ^ ν, ‖Y' (k + 1) ω - Y' k ω‖ ≤ δ' ω) ∧
        Integrable (fun ω => δ ω ^ 2) P ∧ Integrable (fun ω => δ' ω ^ 2) P ∧
        (∫ ω, δ ω ^ 2 ∂P) ^ 2 ≤ 3 * κ ^ 2 / 2 ^ ν ∧ (∫ ω, δ' ω ^ 2 ∂P) ^ 2 ≤ 3 * κ' ^ 2 / 2 ^ ν) := by
  classical
  obtain ⟨Ω, hΩ, P, hP, Yf, Yf', hYm, hYm', hcross, h4, h4', h2, h2', hL, hL'⟩ :=
    S7PIDT_gauss_vec (ι := Fin (2 ^ ν + 1)) I (fun i => g i.1) (fun i => g' i.1)
      (fun i => hg i.1 (Nat.lt_succ_iff.1 i.2)) (fun i => hg' i.1 (Nat.lt_succ_iff.1 i.2))
  have hext := fun (Z : Fin (2 ^ ν + 1) → Ω → EuclideanSpace ℝ (Fin r)) (k : ℕ) (hk : k ≤ 2 ^ ν) =>
    S7PIDT_ext_eq ν Z k hk
  set ext := fun (Z : Fin (2 ^ ν + 1) → Ω → EuclideanSpace ℝ (Fin r)) => S7PIDT_ext ν Z with hextdef
  have hv4 : ∀ a b : Fin (2 ^ ν + 1), a.1 ≤ b.1 →
      ∫ ω, ‖Yf b ω - Yf a ω‖ ^ 4 ∂P ≤ 3 * (κ * (((b.1 : ℝ) - a.1) / 2 ^ ν)) ^ 2 := by
    intro a b hab
    refine (h4 b a).trans ?_
    have h1 := hv a.1 b.1 hab (Nat.lt_succ_iff.1 b.2)
    have h2 : 0 ≤ ∫ u in I, ‖g b.1 u - g a.1 u‖ ^ 2 := integral_nonneg fun u => by positivity
    have := pow_le_pow_left₀ h2 h1 2
    linarith
  have hv4' : ∀ a b : Fin (2 ^ ν + 1), a.1 ≤ b.1 →
      ∫ ω, ‖Yf' b ω - Yf' a ω‖ ^ 4 ∂P ≤ 3 * (κ' * (((b.1 : ℝ) - a.1) / 2 ^ ν)) ^ 2 := by
    intro a b hab
    refine (h4' b a).trans ?_
    have h1 := hv' a.1 b.1 hab (Nat.lt_succ_iff.1 b.2)
    have h2 : 0 ≤ ∫ u in I, ‖g' b.1 u - g' a.1 u‖ ^ 2 := integral_nonneg fun u => by positivity
    have := pow_le_pow_left₀ h2 h1 2
    linarith
  have h00 : ∫ ω, ‖Yf 0 ω‖ ^ 2 ∂P ≤ κ := by
    rw [h2 0]; exact h0 0 (Nat.zero_le _)
  have h00' : ∫ ω, ‖Yf' 0 ω‖ ^ 2 ∂P ≤ κ' := by
    rw [h2' 0]; exact h0' 0 (Nat.zero_le _)
  obtain ⟨⟨S, hSm, hS0, hSb, hSi, hSI⟩, ⟨δ, hδm, hδ0, hδb, hδi, hδI⟩⟩ := S7PIDT_side P ν Yf hYm hL κ hκ hv4 h00
  obtain ⟨⟨S', hSm', hS0', hSb', hSi', hSI'⟩, ⟨δ', hδm', hδ0', hδb', hδi', hδI'⟩⟩ :=
    S7PIDT_side P ν Yf' hYm' hL' κ' hκ' hv4' h00'
  refine ⟨Ω, hΩ, P, hP, S7PIDT_ext ν Yf, S7PIDT_ext ν Yf', ?_, ⟨S, S', hSm, hSm', hS0, hS0', hSb, hSb', hSi, hSi', hSI, hSI'⟩,
    ⟨δ, δ', hδm, hδm', hδ0, hδ0', hδb, hδb', hδi, hδi', hδI, hδI'⟩⟩
  · intro Φ Φ' M
    have h := S7PIDT_id I (fun i => g i.1) (fun i => g' i.1) (fun i => hg i.1 (Nat.lt_succ_iff.1 i.2))
      (fun i => hg' i.1 (Nat.lt_succ_iff.1 i.2)) P Yf Yf'
      (fun i => (hL i).mono_exponent (by norm_num)) (fun i => (hL' i).mono_exponent (by norm_num)) hcross Φ Φ' M
    have e1 : ∀ ω, (fun i : Fin (2 ^ ν + 1) => S7PIDT_ext ν Yf i.1 ω) = fun i => Yf i ω := by
      intro ω; funext i; rw [S7PIDT_ext_eq ν Yf i.1 (Nat.lt_succ_iff.1 i.2)]
    have e2 : ∀ ω, (fun i : Fin (2 ^ ν + 1) => S7PIDT_ext ν Yf' i.1 ω) = fun i => Yf' i ω := by
      intro ω; funext i; rw [S7PIDT_ext_eq ν Yf' i.1 (Nat.lt_succ_iff.1 i.2)]
    simp only [e1, e2]
    exact ⟨h.1, h.2.2⟩

end HRS.MC.Sec7.S7PIDT

end
