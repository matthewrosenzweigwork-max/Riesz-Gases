import HRS.MS.S82RM17

/-!
# S8.2 R02 (S82R), M18: telescoping over fractional pins
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Function
open scoped ENNReal BigOperators

namespace HRS.MS.S82R
open HRS.External

variable {E : Type*} [MeasurableSpace E]

/-- The one-site exponent `ψ - λ Σ_{l ≠ i} q(·, c_l)`. -/
def s82r_PhiC {μ : Measure E} (V : WeakPotential μ) (ψ : E → ℝ) (lam : ℝ) {n : ℕ} (i : Fin n)
    (c : Fin n → E) : E → ℝ := fun z => ψ z - lam * ∑ l ∈ Finset.univ.erase i, V.q z (c l)

/-- The field with the fractional pins in `s`. -/
def s82r_Fld {μ : Measure E} (V : WeakPotential μ) {m : ℕ} (p : Fin m → E) (t : Fin m → ℝ)
    (s : Finset (Fin m)) (ψ : E → ℝ) : E → ℝ := fun z => ψ z - ∑ ℓ ∈ s, t ℓ * V.q z (p ℓ)

lemma s82r_pins_chain {μ : Measure E} [IsProbabilityMeasure μ] (V : WeakPotential μ) {ψ0 : E → ℝ}
    {M M₁ : ℝ} (hψ : IsField μ ψ0 M M₁) {m n : ℕ} (p : Fin m → E) (t : Fin m → ℝ)
    (ht : ∀ ℓ, 0 ≤ t ℓ) {lam : ℝ} (hlam : 0 ≤ lam) (i : Fin n) (y : Fin n → E) {P : ℝ}
    (hP : (∑ ℓ, t ℓ) * V.γ + lam * n * V.γ ≤ P) (s : Finset (Fin m)) (z : E) :
    |s82r_nd μ (s82r_PhiC V ψ0 lam i y) z - s82r_nd μ (s82r_PhiC V (s82r_Fld V p t s ψ0) lam i y) z| ≤
      ∑ ℓ ∈ s, (Real.exp (M + (M₁ + P)) * s82r_d V (t ℓ) z (p ℓ) +
        Real.exp (M + (M₁ + P)) ^ 2 * (t ℓ * V.γ)) := by
  classical
  have hsub : ∀ s' : Finset (Fin m), (∑ ℓ ∈ s', t ℓ) ≤ ∑ ℓ, t ℓ := fun s' =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun ℓ _ _ => ht ℓ
  have hbud : ∀ s' : Finset (Fin m), Measurable (s82r_PhiC V (s82r_Fld V p t s' ψ0) lam i y) ∧
      (∀ z, s82r_PhiC V (s82r_Fld V p t s' ψ0) lam i y z ≤ M) ∧
      Integrable (s82r_PhiC V (s82r_Fld V p t s' ψ0) lam i y) μ ∧
      -(M₁ + P) ≤ ∫ z, s82r_PhiC V (s82r_Fld V p t s' ψ0) lam i y z ∂μ := by
    intro s'
    obtain ⟨h1, h2, h3, h4⟩ := s82r_budget V hψ p t ht s' hlam i y
    refine ⟨h1, h2, h3, ?_⟩
    have := mul_le_mul_of_nonneg_right (hsub s') V.γ_nonneg
    refine le_trans ?_ h4
    nlinarith [this]
  induction s using Finset.induction_on with
  | empty =>
      have : s82r_PhiC V (s82r_Fld V p t ∅ ψ0) lam i y = s82r_PhiC V ψ0 lam i y := by
        funext z; simp [s82r_PhiC, s82r_Fld]
      rw [this]; simp
  | insert j s hj ih =>
      have hstep : s82r_PhiC V (s82r_Fld V p t (insert j s) ψ0) lam i y =
          fun z => s82r_PhiC V (s82r_Fld V p t s ψ0) lam i y z - t j * V.q z (p j) := by
        funext z; simp only [s82r_PhiC, s82r_Fld, Finset.sum_insert hj]; ring
      obtain ⟨hm, hM, hi, hint⟩ := hbud s
      obtain ⟨hm', hM', hi', hint'⟩ := hbud (insert j s)
      rw [hstep] at hi' hint'
      have key := s82r_oc_pin V hm hM (ht j) (p j) hi hi' hint hint' z
      have eK : Real.exp ((M₁ + P) + M) = Real.exp (M + (M₁ + P)) := by rw [add_comm]
      have eK2 : Real.exp (M + 2 * (M₁ + P) + M) = Real.exp (M + (M₁ + P)) ^ 2 := by
        rw [sq, ← Real.exp_add]; ring_nf
      rw [eK, eK2] at key
      rw [Finset.sum_insert hj, hstep]
      calc |s82r_nd μ (s82r_PhiC V ψ0 lam i y) z - s82r_nd μ (fun z => s82r_PhiC V (s82r_Fld V p t s ψ0) lam i y z
              - t j * V.q z (p j)) z|
          ≤ |s82r_nd μ (s82r_PhiC V ψ0 lam i y) z - s82r_nd μ (s82r_PhiC V (s82r_Fld V p t s ψ0) lam i y) z| +
            |s82r_nd μ (s82r_PhiC V (s82r_Fld V p t s ψ0) lam i y) z - s82r_nd μ (fun z =>
              s82r_PhiC V (s82r_Fld V p t s ψ0) lam i y z - t j * V.q z (p j)) z| := abs_sub_le _ _ _
        _ ≤ _ := by
          rw [add_comm]
          exact add_le_add key ih

end HRS.MS.S82R

end
