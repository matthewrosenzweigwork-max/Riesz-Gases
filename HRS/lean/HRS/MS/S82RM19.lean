import HRS.MS.S82RM18

/-!
# S8.2 R02 (S82R), M19: telescoping over changed coordinates
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Function
open scoped ENNReal BigOperators

namespace HRS.MS.S82R
open HRS.External

variable {E : Type*} [MeasurableSpace E]

/-- hybrid configuration: coordinates in `s` from `y`, the others from `x` -/
def s82r_hyb {n : ℕ} (x y : Fin n → E) (s : Finset (Fin n)) : Fin n → E :=
  fun ℓ => open Classical in if ℓ ∈ s then y ℓ else x ℓ

lemma s82r_phiC_budget {μ : Measure E} [IsProbabilityMeasure μ] (V : WeakPotential μ) {ψ0 : E → ℝ}
    {M M₁ : ℝ} (hψ : IsField μ ψ0 M M₁) {n : ℕ} {lam : ℝ} (hlam : 0 ≤ lam) {P : ℝ}
    (hP : lam * n * V.γ ≤ P) (i : Fin n) (c : Fin n → E) :
    Measurable (s82r_PhiC V ψ0 lam i c) ∧ (∀ z, s82r_PhiC V ψ0 lam i c z ≤ M) ∧
      Integrable (s82r_PhiC V ψ0 lam i c) μ ∧ -(M₁ + P) ≤ ∫ z, s82r_PhiC V ψ0 lam i c z ∂μ := by
  obtain ⟨h1, h2, h3, h4⟩ := s82r_budget V hψ (m := 0) (Fin.elim0 : Fin 0 → E)
    (Fin.elim0 : Fin 0 → ℝ) (fun e => e.elim0) ∅ hlam i c
  simp only [Finset.sum_empty, sub_zero, zero_mul, add_zero] at h1 h2 h3 h4
  refine ⟨h1, h2, h3, le_trans ?_ h4⟩
  linarith

lemma s82r_hyb_update {n : ℕ} (x y : Fin n → E) (s : Finset (Fin n)) (j : Fin n) (hj : j ∉ s) :
    s82r_hyb x y (insert j s) = update (s82r_hyb x y s) j (y j) := by
  classical
  funext ℓ
  by_cases h : ℓ = j
  · subst h; simp [s82r_hyb]
  · simp [s82r_hyb, h, Function.update_of_ne h]

lemma s82r_hyb_eq {n : ℕ} (x y : Fin n → E) (s : Finset (Fin n)) (j : Fin n) (hj : j ∉ s) :
    s82r_hyb x y s j = x j := by
  classical
  simp [s82r_hyb, hj]

lemma s82r_PhiC_split {μ : Measure E} (V : WeakPotential μ) (ψ : E → ℝ) (lam : ℝ) {n : ℕ} (i j : Fin n)
    (hj : j ∈ Finset.univ.erase i) (c : Fin n → E) :
    s82r_PhiC V ψ lam i c = fun z =>
      (ψ z - lam * ∑ l ∈ (Finset.univ.erase i).erase j, V.q z (c l)) - lam * V.q z (c j) := by
  funext z
  unfold s82r_PhiC
  rw [← Finset.add_sum_erase _ _ hj]
  ring

end HRS.MS.S82R

end
