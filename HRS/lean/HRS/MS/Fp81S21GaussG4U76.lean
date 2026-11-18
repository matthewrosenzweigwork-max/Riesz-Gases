import HRS.MS.Fp81S21GaussG4U75

/-! A centered scalar Duhamel estimate using only product integrability and
pointwise time Cauchy--Schwarz. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3

/-- Centering commutes with a scalar time integral under product integrability.
The squared centered norm is controlled by the time length squared times a
uniform per-time centered bound. -/
theorem fp81s21_g4_centered_time_integral_bound
    {Q : Type*} [MeasurableSpace Q] {d : ℕ}
    (ν : Measure Q) (μ : Measure (Euc d)) [IsFiniteMeasure ν]
    [IsProbabilityMeasure μ]
    (g : Q → Euc d → ℝ) (D : Euc d → ℝ)
    (B K : ℝ) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hgmeas : Measurable (Function.uncurry g))
    (hgprod : Integrable (Function.uncurry g) (ν.prod μ))
    (hgbound : ∀ q x, |g q x| ≤ B)
    (hDuhamel : ∀ x, D x = ∫ q, g q x ∂ν)
    (hcenter : ∀ᵐ q ∂ν,
      (∫ x, (HRS.Whole.projMean μ (g q) x)^2 ∂μ) ≤ K) :
    (∫ x, (HRS.Whole.projMean μ D x)^2 ∂μ) ≤
      K * (ν.real Set.univ)^2 := by
  let m : Q → ℝ := fun q => ∫ x, g q x ∂μ
  let c : Q → Euc d → ℝ := fun q x => g q x - m q
  have hmStrong : StronglyMeasurable m := by
    dsimp [m]
    exact hgmeas.stronglyMeasurable.integral_prod_right'
  have hmMeas : Measurable m := hmStrong.measurable
  have hμreal : μ.real Set.univ = 1 := by simp [Measure.real]
  have hgSliceMeas : ∀ q, Measurable (g q) := by
    intro q
    exact hgmeas.comp (measurable_const.prodMk measurable_id)
  have hgSlice : ∀ q, Integrable (g q) μ := by
    intro q
    exact Integrable.of_bound (hgSliceMeas q).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact hgbound q x)
  have hmBound : ∀ q, |m q| ≤ B := by
    intro q
    calc
      |m q| ≤ ∫ x, |g q x| ∂μ := by
        dsimp [m]
        exact abs_integral_le_integral_abs
      _ ≤ ∫ _x, B ∂μ := integral_mono_ae (hgSlice q).abs (integrable_const B)
        (Filter.Eventually.of_forall fun x => hgbound q x)
      _ = B := by simp [hμreal]
  have hcMeas : Measurable (Function.uncurry c) := by
    dsimp [c, Function.uncurry]
    exact hgmeas.sub (hmMeas.comp measurable_fst)
  have hcBound : ∀ q x, |c q x| ≤ 2 * B := by
    intro q x
    dsimp [c]
    calc
      |g q x - m q| ≤ |g q x| + |m q| := abs_sub _ _
      _ ≤ B + B := add_le_add (hgbound q x) (hmBound q)
      _ = 2 * B := by ring
  haveI : IsFiniteMeasure (ν.prod μ) := inferInstance
  have hcProd : Integrable (Function.uncurry c) (ν.prod μ) :=
    Integrable.of_bound hcMeas.aestronglyMeasurable (2 * B)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]
        exact hcBound z.1 z.2)
  have hcSqMeas : Measurable (fun z : Q × Euc d => (c z.1 z.2)^2) :=
    hcMeas.pow_const 2
  have hcSqProd : Integrable (fun z : Q × Euc d => (c z.1 z.2)^2) (ν.prod μ) :=
    Integrable.of_bound hcSqMeas.aestronglyMeasurable (4 * B^2)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_pow]
        have habs := abs_nonneg (c z.1 z.2)
        nlinarith [hcBound z.1 z.2])
  have hcTimeMeas : ∀ x, Measurable (fun q => c q x) := by
    intro x
    exact hcMeas.comp (measurable_id.prodMk measurable_const)
  have hcTime : ∀ x, Integrable (fun q => c q x) ν := by
    intro x
    exact Integrable.of_bound (hcTimeMeas x).aestronglyMeasurable (2 * B)
      (Filter.Eventually.of_forall fun q => by
        rw [Real.norm_eq_abs]
        exact hcBound q x)
  have hcMean : ∀ q x,
      HRS.Whole.projMean μ (g q) x = c q x := by
    intro q x
    simp [c, m, HRS.Whole.projMean, HRS.Whole.pair]
  have hcenter' : ∀ᵐ q ∂ν, (∫ x, (c q x)^2 ∂μ) ≤ K := by
    filter_upwards [hcenter] with q hq
    simpa only [hcMean q] using hq
  have hDInt : Integrable D μ := by
    apply hgprod.integral_prod_right.congr
    filter_upwards with x
    exact (hDuhamel x).symm
  have hmInt : Integrable m ν := by
    simpa [m] using hgprod.integral_prod_left
  have hmeanD : (∫ x, D x ∂μ) = ∫ q, m q ∂ν := by
    calc
      (∫ x, D x ∂μ) = ∫ x, ∫ q, g q x ∂ν ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        exact hDuhamel x
      _ = ∫ z, Function.uncurry g z ∂(ν.prod μ) :=
        (integral_prod_symm (Function.uncurry g) hgprod).symm
      _ = ∫ q, m q ∂ν := by
        simpa [m] using integral_prod (Function.uncurry g) hgprod
  have hsplit : ∀ x,
      (∫ q, g q x ∂ν) = (∫ q, c q x ∂ν) + (∫ q, m q ∂ν) := by
    intro x
    rw [← integral_add (hcTime x) hmInt]
    apply integral_congr_ae
    filter_upwards with q
    simp [c]
  have hcenterIdentity : ∀ x,
      HRS.Whole.projMean μ D x = ∫ q, c q x ∂ν := by
    intro x
    unfold HRS.Whole.projMean HRS.Whole.pair
    rw [hDuhamel x, hmeanD, hsplit x]
    ring
  let F : Euc d → ℝ := fun x => ∫ q, c q x ∂ν
  let H : Euc d → ℝ := fun x => ∫ q, (c q x)^2 ∂ν
  have hFInt : Integrable F μ := by
    simpa [F] using hcProd.integral_prod_right
  have hHInt : Integrable H μ := by
    simpa [H] using hcSqProd.integral_prod_right
  have hFBound : ∀ x, |F x| ≤ 2 * B * ν.real Set.univ := by
    intro x
    calc
      |F x| ≤ ∫ q, |c q x| ∂ν := by
        dsimp [F]
        exact abs_integral_le_integral_abs
      _ ≤ ∫ _q, 2 * B ∂ν := integral_mono_ae (hcTime x).abs
        (integrable_const (2 * B))
        (Filter.Eventually.of_forall fun q => hcBound q x)
      _ = 2 * B * ν.real Set.univ := by simp [mul_comm]
  have hF2Int : Integrable (fun x => F x^2) μ :=
    Integrable.of_bound ((hFInt.aestronglyMeasurable.aemeasurable.pow_const 2).aestronglyMeasurable)
      ((2 * B * ν.real Set.univ)^2)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_pow]
        have habs := abs_nonneg (F x)
        nlinarith [hFBound x])
  have hRhsInt : Integrable (fun x => ν.real Set.univ * H x) μ :=
    hHInt.const_mul (ν.real Set.univ)
  have hpoint : ∀ x, F x^2 ≤ ν.real Set.univ * H x := by
    intro x
    have hcxLp : MemLp (fun q => c q x) 2 ν :=
      MemLp.of_bound (hcTimeMeas x).aestronglyMeasurable (2 * B)
        (Filter.Eventually.of_forall fun q => by
          rw [Real.norm_eq_abs]
          exact hcBound q x)
    have hcs := fp81s21_g4_time_cauchy_schwarz ν (fun q => c q x) hcxLp
    simpa [F, H] using hcs
  calc
    (∫ x, (HRS.Whole.projMean μ D x)^2 ∂μ) = ∫ x, F x^2 ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hcenterIdentity x]
    _ ≤ ∫ x, ν.real Set.univ * H x ∂μ :=
      integral_mono_ae hF2Int hRhsInt (Filter.Eventually.of_forall hpoint)
    _ = ν.real Set.univ * ∫ x, H x ∂μ := by simp only [integral_const_mul]
    _ = ν.real Set.univ * (∫ q, ∫ x, (c q x)^2 ∂μ ∂ν) := by
      rw [← integral_integral_swap hcSqProd]
    _ ≤ ν.real Set.univ * (∫ q, K ∂ν) := by
      apply mul_le_mul_of_nonneg_left _ measureReal_nonneg
      exact integral_mono_ae (hcSqProd.integral_prod_left) (integrable_const K) hcenter'
    _ = K * (ν.real Set.univ)^2 := by
      rw [integral_const]
      ring

#print axioms fp81s21_g4_centered_time_integral_bound
end HRS.Fp81.S21
