import HRS.MS.S82RM16

/-!
# S8.2 R02 (S82R), M17: pin addition and the integral budget of the one-site exponents
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Function
open scoped ENNReal BigOperators

namespace HRS.MS.S82R
open HRS.External

variable {E : Type*} [MeasurableSpace E]

lemma s82r_oc_pin {μ : Measure E} [IsProbabilityMeasure μ] (V : WeakPotential μ) {Ψ : E → ℝ}
    (hΨm : Measurable Ψ) {M M2 : ℝ} (hΨM : ∀ z, Ψ z ≤ M) {t : ℝ} (ht : 0 ≤ t) (p : E)
    (hi₁ : Integrable Ψ μ) (hi₂ : Integrable (fun z => Ψ z - t * V.q z p) μ)
    (h₁ : -M2 ≤ ∫ z, Ψ z ∂μ) (h₂ : -M2 ≤ ∫ z, (Ψ z - t * V.q z p) ∂μ) (z : E) :
    |s82r_nd μ Ψ z - s82r_nd μ (fun z => Ψ z - t * V.q z p) z| ≤
      Real.exp (M2 + M) * s82r_d V t z p + Real.exp (M + 2 * M2 + M) * (t * V.γ) := by
  have hm2 : Measurable (fun z => Ψ z - t * V.q z p) :=
    hΨm.sub ((V.measurable_q.comp (measurable_id.prodMk measurable_const)).const_mul t)
  have hM2 : ∀ z, Ψ z - t * V.q z p ≤ M := fun z => by
    have := mul_nonneg ht (V.q_nonneg z p); linarith [hΨM z]
  have hd := s82r_nd_diff μ hΨm hm2 hi₁ hi₂ hΨM hM2 h₁ h₂ z
  have hΔ : ∀ y, |Real.exp (Ψ y) - Real.exp (Ψ y - t * V.q y p)| ≤ Real.exp M * s82r_d V t y p := by
    intro y
    have e : Real.exp (Ψ y) - Real.exp (Ψ y - t * V.q y p) = Real.exp (Ψ y) * s82r_d V t y p := by
      unfold s82r_d
      have : Real.exp (Ψ y - t * V.q y p) = Real.exp (Ψ y) * Real.exp (-(t * V.q y p)) := by
        rw [← Real.exp_add]; ring_nf
      rw [this]; ring
    rw [e, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (s82r_d_nonneg V ht y p))]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (hΨM y)) (s82r_d_nonneg V ht y p)
  have hdi : Integrable (fun y => s82r_d V t y p) μ :=
    Integrable.of_bound (s82r_d_meas V t p).aestronglyMeasurable 1 (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (s82r_d_nonneg V ht z p)]; exact s82r_d_lt_one V t z p)
  have hint : ∫ y, |Real.exp (Ψ y) - Real.exp (Ψ y - t * V.q y p)| ∂μ ≤ Real.exp M * (t * V.γ) := by
    calc ∫ y, |Real.exp (Ψ y) - Real.exp (Ψ y - t * V.q y p)| ∂μ
        ≤ ∫ y, Real.exp M * s82r_d V t y p ∂μ :=
          integral_mono_of_nonneg (ae_of_all _ fun y => abs_nonneg _) (hdi.const_mul _) (ae_of_all _ hΔ)
      _ = Real.exp M * ∫ y, s82r_d V t y p ∂μ := integral_const_mul _ _
      _ ≤ Real.exp M * (t * V.γ) :=
          mul_le_mul_of_nonneg_left (s82r_d_int V ht p) (Real.exp_pos _).le
  refine hd.trans (add_le_add ?_ ?_)
  · calc Real.exp M2 * |Real.exp (Ψ z) - Real.exp (Ψ z - t * V.q z p)|
        ≤ Real.exp M2 * (Real.exp M * s82r_d V t z p) :=
          mul_le_mul_of_nonneg_left (hΔ z) (Real.exp_pos _).le
      _ = _ := by rw [Real.exp_add]; ring
  · calc Real.exp (M + 2 * M2) * ∫ y, |Real.exp (Ψ y) - Real.exp (Ψ y - t * V.q y p)| ∂μ
        ≤ Real.exp (M + 2 * M2) * (Real.exp M * (t * V.γ)) :=
          mul_le_mul_of_nonneg_left hint (Real.exp_pos _).le
      _ = Real.exp (M + 2 * M2 + M) * (t * V.γ) := by rw [Real.exp_add (M + 2 * M2) M]; ring

/-- The exponent `ψ - Σ_{ℓ∈s} t_ℓ q(·,p_ℓ) - λ Σ_{l≠i} q(·,c_l)` is integrable, bounded above by `M`
and has mean at least `-(M₁ + Σ_s t_ℓ γ + λ n γ)`. -/
lemma s82r_budget {μ : Measure E} [IsProbabilityMeasure μ] (V : WeakPotential μ) {ψ : E → ℝ}
    {M M₁ : ℝ} (hψ : IsField μ ψ M M₁) {m n : ℕ} (p : Fin m → E) (t : Fin m → ℝ)
    (ht : ∀ ℓ, 0 ≤ t ℓ) (s : Finset (Fin m)) {lam : ℝ} (hlam : 0 ≤ lam) (i : Fin n) (c : Fin n → E) :
    Measurable (fun z => ψ z - ∑ ℓ ∈ s, t ℓ * V.q z (p ℓ) - lam * ∑ l ∈ Finset.univ.erase i, V.q z (c l)) ∧
    (∀ z, ψ z - ∑ ℓ ∈ s, t ℓ * V.q z (p ℓ) - lam * ∑ l ∈ Finset.univ.erase i, V.q z (c l) ≤ M) ∧
    Integrable (fun z => ψ z - ∑ ℓ ∈ s, t ℓ * V.q z (p ℓ) - lam * ∑ l ∈ Finset.univ.erase i, V.q z (c l)) μ ∧
    -(M₁ + (∑ ℓ ∈ s, t ℓ) * V.γ + lam * n * V.γ) ≤
      ∫ z, (ψ z - ∑ ℓ ∈ s, t ℓ * V.q z (p ℓ) - lam * ∑ l ∈ Finset.univ.erase i, V.q z (c l)) ∂μ := by
  have hqm : ∀ w : E, Measurable (fun z => V.q z w) := fun w =>
    V.measurable_q.comp (measurable_id.prodMk measurable_const)
  have hqi : ∀ w : E, Integrable (fun z => V.q z w) μ := integrable_q_left V
  have hS1 : Integrable (fun z => ∑ ℓ ∈ s, t ℓ * V.q z (p ℓ)) μ :=
    integrable_finset_sum _ fun ℓ _ => (hqi (p ℓ)).const_mul _
  have hS2 : Integrable (fun z => ∑ l ∈ Finset.univ.erase i, V.q z (c l)) μ :=
    integrable_finset_sum _ fun l _ => hqi (c l)
  have hint : Integrable (fun z => ψ z - ∑ ℓ ∈ s, t ℓ * V.q z (p ℓ) -
      lam * ∑ l ∈ Finset.univ.erase i, V.q z (c l)) μ :=
    (hψ.integrable.sub hS1).sub (hS2.const_mul lam)
  refine ⟨?_, fun z => ?_, hint, ?_⟩
  · exact (hψ.measurable.sub (Finset.measurable_sum _ fun ℓ _ => (hqm (p ℓ)).const_mul _)).sub
      ((Finset.measurable_sum _ fun l _ => hqm (c l)).const_mul lam)
  · have h1 : 0 ≤ ∑ ℓ ∈ s, t ℓ * V.q z (p ℓ) :=
      Finset.sum_nonneg fun ℓ _ => mul_nonneg (ht ℓ) (V.q_nonneg _ _)
    have h2 : 0 ≤ lam * ∑ l ∈ Finset.univ.erase i, V.q z (c l) :=
      mul_nonneg hlam (Finset.sum_nonneg fun l _ => V.q_nonneg _ _)
    linarith [hψ.le z]
  · have hA : Integrable (fun z => ψ z - ∑ ℓ ∈ s, t ℓ * V.q z (p ℓ)) μ := hψ.integrable.sub hS1
    have hB : Integrable (fun z => lam * ∑ l ∈ Finset.univ.erase i, V.q z (c l)) μ := hS2.const_mul lam
    rw [integral_sub hA hB, integral_sub hψ.integrable hS1, integral_const_mul]
    have b1 : ∫ z, ∑ ℓ ∈ s, t ℓ * V.q z (p ℓ) ∂μ ≤ (∑ ℓ ∈ s, t ℓ) * V.γ := by
      rw [integral_finset_sum _ fun ℓ _ => (hqi (p ℓ)).const_mul _, Finset.sum_mul]
      refine Finset.sum_le_sum fun ℓ _ => ?_
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (integral_q_left_le V _) (ht ℓ)
    have b2 : ∫ z, ∑ l ∈ Finset.univ.erase i, V.q z (c l) ∂μ ≤ n * V.γ := by
      rw [integral_finset_sum _ fun l _ => hqi (c l)]
      calc ∑ l ∈ Finset.univ.erase i, ∫ z, V.q z (c l) ∂μ ≤ ∑ _l ∈ Finset.univ.erase i, V.γ :=
            Finset.sum_le_sum fun l _ => integral_q_left_le V _
        _ ≤ ∑ _l : Fin n, V.γ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun _ _ _ => V.γ_nonneg
        _ = n * V.γ := by simp
    have := hψ.ge
    nlinarith [mul_le_mul_of_nonneg_left b2 hlam]

end HRS.MS.S82R

end
