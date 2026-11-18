import HRS.Main.A34Aux1

/-!
# Packet A34, helper 2: the noise integrand `h_{t,φ}` and its `L²` calculus

`a34_h D ρ q t φ (r,x) = √ρ(r,x) · a33_g D ρ q t φ (r,x) = √(2qρ) 1_{r ≤ t} ∇U^{r,t}φ(x)`, viewed in
`L²([0,T]×𝕋^d; ℝ^d)` (base measure `a33_mu0`).  Contents: the identification of the covariance
`surrogateCov` with `‖h‖²`, the `L²` triangle inequality, the coupling estimate of
`‖h₁ - h₂‖²`, and the `H¹` bound `∫|∇u|² ≤ ‖u‖²_{H¹}`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A34

open HRS HRS.PDE HRS.PDE.ET HRS.A33

variable {d : ℕ}

/-- the noise integrand `√(2qρ) 1_{r ≤ t} ∇U^{r,t}φ` -/
def a34_h (D : DynData d) (ρ : ℝ → Torus d → ℝ) (q t : ℝ) (φ : Torus d → ℝ) :
    ℝ × Torus d → Euc d := fun p => Real.sqrt (ρ p.1 p.2) • a33_g D ρ q t φ p

theorem a34_norm_toLp_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} {h : α → Euc d}
    (hm : MemLp h 2 μ) : ‖hm.toLp h‖ ^ 2 = ∫ a, ‖h a‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hm.coeFn_toLp] with a ha
  rw [ha, real_inner_self_eq_norm_sq]

/-- `L²` triangle inequality for the root of the energy. -/
theorem a34_sqrt_tri {α : Type*} [MeasurableSpace α] {μ : Measure α} {h₁ h₂ : α → Euc d}
    (hm₁ : MemLp h₁ 2 μ) (hm₂ : MemLp h₂ 2 μ) :
    |Real.sqrt (∫ a, ‖h₁ a‖ ^ 2 ∂μ) - Real.sqrt (∫ a, ‖h₂ a‖ ^ 2 ∂μ)| ≤
      Real.sqrt (∫ a, ‖h₁ a - h₂ a‖ ^ 2 ∂μ) := by
  have hm : MemLp (h₁ - h₂) 2 μ := hm₁.sub hm₂
  have e1 : Real.sqrt (∫ a, ‖h₁ a‖ ^ 2 ∂μ) = ‖hm₁.toLp h₁‖ := by
    rw [← a34_norm_toLp_sq hm₁, Real.sqrt_sq (norm_nonneg _)]
  have e2 : Real.sqrt (∫ a, ‖h₂ a‖ ^ 2 ∂μ) = ‖hm₂.toLp h₂‖ := by
    rw [← a34_norm_toLp_sq hm₂, Real.sqrt_sq (norm_nonneg _)]
  have e3 : Real.sqrt (∫ a, ‖h₁ a - h₂ a‖ ^ 2 ∂μ) = ‖hm₁.toLp h₁ - hm₂.toLp h₂‖ := by
    have h3 := a34_norm_toLp_sq hm
    have h4 : hm.toLp (h₁ - h₂) = hm₁.toLp h₁ - hm₂.toLp h₂ := MemLp.toLp_sub hm₁ hm₂
    rw [h4] at h3
    have h5 : (∫ a, ‖h₁ a - h₂ a‖ ^ 2 ∂μ) = ∫ a, ‖(h₁ - h₂) a‖ ^ 2 ∂μ := rfl
    rw [h5, ← h3, Real.sqrt_sq (norm_nonneg _)]
  rw [e1, e2, e3]
  exact abs_norm_sub_norm_le _ _

/-- a.e. bounded a.e.-measurable functions into `Euc d` have integrable squared norm. -/
theorem a34_integrable_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {u : α → Euc d} (hu : AEMeasurable u μ) {K : ℝ} (hK : ∀ᵐ p ∂μ, ‖u p‖ ≤ K) :
    Integrable (fun p => ‖u p‖ ^ 2) μ := by
  refine Integrable.of_bound (C := K ^ 2) (hu.norm.pow_const 2).aestronglyMeasurable ?_
  filter_upwards [hK] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) hp 2

/-- Coupling estimate for `‖a₁u₁ - a₂u₂‖²`. -/
theorem a34_E1 {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {a₁ a₂ : α → ℝ} {u₁ u₂ : α → Euc d} (hu₁ : AEMeasurable u₁ μ) (hu₂ : AEMeasurable u₂ μ)
    (ha₁ : AEMeasurable a₁ μ) (ha₂ : AEMeasurable a₂ μ)
    {K : ℝ} (hK₁ : ∀ᵐ p ∂μ, ‖u₁ p‖ ≤ K)
    (hK₂ : ∀ᵐ p ∂μ, ‖u₂ p‖ ≤ K) {ε B : ℝ} (hB : 0 ≤ B) (ha : ∀ᵐ p ∂μ, (a₁ p - a₂ p) ^ 2 ≤ ε)
    (hb : ∀ᵐ p ∂μ, a₂ p ^ 2 ≤ B) {Y : ℝ} (hY : ∫ p, ‖u₁ p - u₂ p‖ ^ 2 ∂μ ≤ Y)
    {M : ℝ} (hM : ∀ᵐ p ∂μ, ‖a₁ p • u₁ p - a₂ p • u₂ p‖ ≤ M) :
    ∫ p, ‖a₁ p • u₁ p - a₂ p • u₂ p‖ ^ 2 ∂μ ≤ 2 * K ^ 2 * ε * μ.real Set.univ + 2 * B * Y := by
  have hm1 : AEMeasurable (fun p => a₁ p • u₁ p - a₂ p • u₂ p) μ :=
    (ha₁.smul hu₁).sub (ha₂.smul hu₂)
  have hI1 := a34_integrable_sq (μ := μ) hm1 hM
  have hbd2 : ∀ᵐ p ∂μ, ‖u₁ p - u₂ p‖ ≤ K + K := by
    filter_upwards [hK₁, hK₂] with p h1 h2
    exact (norm_sub_le _ _).trans (add_le_add h1 h2)
  have hI2 : Integrable (fun p => ‖u₁ p - u₂ p‖ ^ 2) μ :=
    a34_integrable_sq (μ := μ) (hu₁.sub hu₂) hbd2
  have hpt : ∀ᵐ p ∂μ, ‖a₁ p • u₁ p - a₂ p • u₂ p‖ ^ 2 ≤
      2 * K ^ 2 * ε + 2 * B * ‖u₁ p - u₂ p‖ ^ 2 := by
    filter_upwards [hK₁, ha, hb] with p hk1 hap hbp
    have e : a₁ p • u₁ p - a₂ p • u₂ p = (a₁ p - a₂ p) • u₁ p + a₂ p • (u₁ p - u₂ p) := by
      rw [sub_smul, smul_sub]; abel
    rw [e]
    have h1 : ‖(a₁ p - a₂ p) • u₁ p + a₂ p • (u₁ p - u₂ p)‖ ≤
        |a₁ p - a₂ p| * ‖u₁ p‖ + |a₂ p| * ‖u₁ p - u₂ p‖ := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs]
      · rw [norm_smul, Real.norm_eq_abs]
    have h2 : ‖(a₁ p - a₂ p) • u₁ p + a₂ p • (u₁ p - u₂ p)‖ ^ 2 ≤
        2 * ((a₁ p - a₂ p) ^ 2 * ‖u₁ p‖ ^ 2) + 2 * (a₂ p ^ 2 * ‖u₁ p - u₂ p‖ ^ 2) := by
      have hx := sq_nonneg (|a₁ p - a₂ p| * ‖u₁ p‖ - |a₂ p| * ‖u₁ p - u₂ p‖)
      have h0 := norm_nonneg ((a₁ p - a₂ p) • u₁ p + a₂ p • (u₁ p - u₂ p))
      have : ‖(a₁ p - a₂ p) • u₁ p + a₂ p • (u₁ p - u₂ p)‖ ^ 2 ≤
          (|a₁ p - a₂ p| * ‖u₁ p‖ + |a₂ p| * ‖u₁ p - u₂ p‖) ^ 2 :=
        pow_le_pow_left₀ h0 h1 2
      refine this.trans ?_
      have e1 : (|a₁ p - a₂ p| * ‖u₁ p‖) ^ 2 = (a₁ p - a₂ p) ^ 2 * ‖u₁ p‖ ^ 2 := by
        rw [mul_pow, sq_abs]
      have e2 : (|a₂ p| * ‖u₁ p - u₂ p‖) ^ 2 = a₂ p ^ 2 * ‖u₁ p - u₂ p‖ ^ 2 := by
        rw [mul_pow, sq_abs]
      nlinarith [e1, e2]
    refine h2.trans ?_
    have h3 : (a₁ p - a₂ p) ^ 2 * ‖u₁ p‖ ^ 2 ≤ ε * K ^ 2 :=
      mul_le_mul hap (pow_le_pow_left₀ (norm_nonneg _) hk1 2) (sq_nonneg _)
        ((sq_nonneg _).trans hap)
    have h4 : a₂ p ^ 2 * ‖u₁ p - u₂ p‖ ^ 2 ≤ B * ‖u₁ p - u₂ p‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hbp (sq_nonneg _)
    nlinarith [h3, h4]
  calc ∫ p, ‖a₁ p • u₁ p - a₂ p • u₂ p‖ ^ 2 ∂μ
      ≤ ∫ p, (2 * K ^ 2 * ε + 2 * B * ‖u₁ p - u₂ p‖ ^ 2) ∂μ :=
        integral_mono_ae hI1 ((integrable_const _).add (hI2.const_mul _)) hpt
    _ = 2 * K ^ 2 * ε * μ.real Set.univ + 2 * B * ∫ p, ‖u₁ p - u₂ p‖ ^ 2 ∂μ := by
        rw [integral_add (integrable_const _) (hI2.const_mul _), integral_const,
          integral_const_mul]
        simp [smul_eq_mul, mul_comm]
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hY (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hB)
        linarith

end HRS.A34
