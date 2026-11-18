import HRS.MS.PoincAux1

/-!
# C-POI, part 2: Maurey-Pisier interpolation (pointwise part)

For `f ∈ C¹(Euc d)` and `q = (x, y)`, with `R_θ q = (cos θ x + sin θ y, -sin θ x + cos θ y)`
(`ContinuousLinearMap.rotation θ`), the path `θ ↦ f (R_θ q).1` runs from `f x` to `f y` on `[0, π/2]`
with derivative `cpoi_G f θ q = ⟪∇f (R_θ q).1, (R_θ q).2⟫`; hence
`(f y - f x)² ≤ (π/2) ∫_0^{π/2} (cpoi_G f θ q)² dθ` (`cpoi_pointwise`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace HRS.MS.Poinc

variable {d : ℕ}

/-- The derivative of `θ ↦ f (R_θ q).1`. -/
def cpoi_G (f : Euc d → ℝ) (θ : ℝ) (q : Euc d × Euc d) : ℝ :=
  ⟪gradient f ((ContinuousLinearMap.rotation θ q).1), (ContinuousLinearMap.rotation θ q).2⟫

theorem cpoi_continuous_gradient {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (gradient f) := by
  have h : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have : gradient f = fun x => (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ f x) := rfl
  rw [this]
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp h

theorem cpoi_continuous_G {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (fun p : ℝ × (Euc d × Euc d) => cpoi_G f p.1 p.2) := by
  unfold cpoi_G
  simp only [ContinuousLinearMap.rotation_apply]
  have hg := cpoi_continuous_gradient hf
  fun_prop

theorem cpoi_continuous_G_left {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) (q : Euc d × Euc d) :
    Continuous fun θ : ℝ => cpoi_G f θ q := by
  unfold cpoi_G
  simp only [ContinuousLinearMap.rotation_apply]
  have hg := cpoi_continuous_gradient hf
  fun_prop

theorem cpoi_hasDerivAt {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) (q : Euc d × Euc d) (θ : ℝ) :
    HasDerivAt (fun θ => f (ContinuousLinearMap.rotation θ q).1) (cpoi_G f θ q) θ := by
  have h1 : HasDerivAt (fun θ : ℝ => (ContinuousLinearMap.rotation θ q).1)
      (ContinuousLinearMap.rotation θ q).2 θ := by
    simp only [ContinuousLinearMap.rotation_apply]
    have a1 := (Real.hasDerivAt_cos θ).smul_const q.1
    have a2 := (Real.hasDerivAt_sin θ).smul_const q.2
    convert a1.add a2 using 1
  have h2 : HasFDerivAt f (fderiv ℝ f (ContinuousLinearMap.rotation θ q).1)
      (ContinuousLinearMap.rotation θ q).1 :=
    ((hf.differentiable one_ne_zero) _).hasFDerivAt
  have := h2.comp_hasDerivAt θ h1
  have e : cpoi_G f θ q = fderiv ℝ f (ContinuousLinearMap.rotation θ q).1
      (ContinuousLinearMap.rotation θ q).2 := by
    unfold cpoi_G gradient
    rw [InnerProductSpace.toDual_symm_apply]
  rw [e]
  exact this

/-- Cauchy-Schwarz on an interval for a continuous function. -/
theorem cpoi_cs {u : ℝ → ℝ} (hu : Continuous u) {L : ℝ} (hL : 0 < L) :
    (∫ θ in (0 : ℝ)..L, u θ) ^ 2 ≤ L * ∫ θ in (0 : ℝ)..L, u θ ^ 2 := by
  set c := (∫ θ in (0 : ℝ)..L, u θ) / L with hc
  have hi : IntervalIntegrable u volume 0 L := hu.intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun θ => u θ ^ 2) volume 0 L := (hu.pow 2).intervalIntegrable _ _
  have hnn : 0 ≤ ∫ θ in (0 : ℝ)..L, (u θ - c) ^ 2 :=
    intervalIntegral.integral_nonneg hL.le (fun θ _ => sq_nonneg _)
  have e : ∫ θ in (0 : ℝ)..L, (u θ - c) ^ 2 =
      (∫ θ in (0 : ℝ)..L, u θ ^ 2) - 2 * c * (∫ θ in (0 : ℝ)..L, u θ) + c ^ 2 * L := by
    have : ∀ θ, (u θ - c) ^ 2 = u θ ^ 2 - 2 * c * u θ + c ^ 2 := fun θ => by ring
    simp_rw [this]
    rw [intervalIntegral.integral_add (hi2.sub (hi.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_sub hi2 (hi.const_mul _), intervalIntegral.integral_const_mul]
    simp
    ring
  rw [e] at hnn
  have : c * L = ∫ θ in (0 : ℝ)..L, u θ := by rw [hc]; field_simp
  nlinarith [this]

/-- The Maurey-Pisier pointwise estimate. -/
theorem cpoi_pointwise {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) (q : Euc d × Euc d) :
    (f q.2 - f q.1) ^ 2 ≤
      (Real.pi / 2) * ∫ θ in (0 : ℝ)..(Real.pi / 2), cpoi_G f θ q ^ 2 := by
  have hc : Continuous fun θ : ℝ => cpoi_G f θ q :=
    cpoi_continuous_G_left hf q
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun θ => f (ContinuousLinearMap.rotation θ q).1) (f' := fun θ => cpoi_G f θ q)
    (a := 0) (b := Real.pi / 2) (fun θ _ => cpoi_hasDerivAt hf q θ)
    (hc.intervalIntegrable _ _)
  have e0 : (ContinuousLinearMap.rotation 0 q).1 = q.1 := by
    simp [ContinuousLinearMap.rotation_apply]
  have e1 : (ContinuousLinearMap.rotation (Real.pi / 2) q).1 = q.2 := by
    simp [ContinuousLinearMap.rotation_apply]
  simp only [e0, e1] at hftc
  rw [← hftc]
  exact cpoi_cs hc (by positivity)

end HRS.MS.Poinc

end
