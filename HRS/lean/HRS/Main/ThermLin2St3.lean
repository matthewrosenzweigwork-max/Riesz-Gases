import HRS.Main.ThermLin2St2

/-!
# THERMLIN2, packet St, part 3: the covariance identity behind `tl2_stationary_fdd` (D3)

`C_β(U_a φ_a, U_b φ_b) + 2β⁻¹ ∫_0^{t_a∧t_b} ∫ ∇U_{σ,t_a}φ_a · ∇U_{σ,t_b}φ_b ρβ = stationaryLagCov(a,b)`,
from `tl2_lyapunov_proof` (D2) and the semigroup property of the frozen propagator.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.PDE HRS.PDE.MFSemigroup HRS.Uniform

variable {d : ℕ}

/-- `C_β(P f, g) = C_β(f, g)`: the covariance only sees `projMean` of the first argument. -/
theorem tl2St_cov_projMean_left {d : ℕ} (g : Torus d → ℝ) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (β : ℝ) (f ψ : Torus d → ℝ) (hf : Continuous f) :
    susceptibilityCov g μ β (projMean μ f) ψ = susceptibilityCov g μ β f ψ := by
  have hint : Integrable f μ := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have hpair : pair μ (projMean μ f) = 0 := by
    unfold pair projMean
    rw [integral_sub hint (integrable_const _), integral_const]
    simp [pair]
  have hpp : projMean μ (projMean μ f) = projMean μ f := by
    funext x
    simp only [projMean] at hpair ⊢
    rw [hpair]; ring
  unfold susceptibilityCov
  rw [hpp]

/-- The reflection `σ ↦ t - σ` in the energy integral. -/
theorem tl2St_reflect (F : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ σ in Set.Icc 0 t, F (t - σ) = ∫ σ in Set.Icc 0 t, F σ := by
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht,
    ← intervalIntegral.integral_of_le ht, intervalIntegral.integral_comp_sub_left F t]
  simp

/-- The covariance identity for `t_a ≤ t_b`. -/
theorem tl2St_entry_le (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) {φa φb : Torus d → ℝ}
    (hφa : Torus.IsSmooth φa) (hφb : Torus.IsSmooth φb) {ta tb : ℝ} (hta : 0 ≤ ta) (hab : ta ≤ tb) :
    susceptibilityCov (periodicRiesz d S.s) (withDensityReal ρβ) S.β (tl2Ub S ρβ 0 ta φa) (tl2Ub S ρβ 0 tb φb) +
      2 * S.β⁻¹ * ∫ σ in Set.Icc 0 ta, ∫ x,
        inner ℝ (Torus.grad (propagator S.dyn (fun _ => ρβ) σ ta φa) x)
          (Torus.grad (propagator S.dyn (fun _ => ρβ) σ tb φb) x) * ρβ x =
    susceptibilityCov (periodicRiesz d S.s) (withDensityReal ρβ) S.β φa (equilibriumSemigroup S.dyn ρβ (tb - ta) φb) := by
  have : IsProbabilityMeasure (withDensityReal ρβ) := HRS.isProb_withDensityReal h.1
  have hδ : 0 ≤ tb - ta := by linarith
  have hg' : Torus.IsSmooth (tl2Ub S ρβ 0 (tb - ta) φb) := tl2Ly_smooth S h hφb le_rfl hδ
  have hL := tl2_lyapunov_proof S h hφa hg' hta
  have e1 : tl2Ub S ρβ 0 ta (tl2Ub S ρβ 0 (tb - ta) φb) = tl2Ub S ρβ 0 tb φb := by
    rw [← tl2Ly_semigroup S h hφb hδ hta]; congr 1; ring
  have hint : ∫ σ in Set.Icc 0 ta, ∫ x,
        inner ℝ (Torus.grad (propagator S.dyn (fun _ => ρβ) σ ta φa) x)
          (Torus.grad (propagator S.dyn (fun _ => ρβ) σ tb φb) x) * ρβ x =
      ∫ σ in Set.Icc 0 ta, tl2LyE S ρβ φa (tl2Ub S ρβ 0 (tb - ta) φb) σ := by
    rw [← tl2St_reflect (tl2LyE S ρβ φa (tl2Ub S ρβ 0 (tb - ta) φb)) hta]
    refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
    have s1 : propagator S.dyn (fun _ => ρβ) σ ta φa = tl2Ub S ρβ 0 (ta - σ) φa :=
      tl2Ly_shift S h hφa hσ.1 hσ.2
    have s2 : propagator S.dyn (fun _ => ρβ) σ tb φb = tl2Ub S ρβ 0 (tb - σ) φb :=
      tl2Ly_shift S h hφb hσ.1 (hσ.2.trans hab)
    have s3 : tl2Ub S ρβ 0 (ta - σ) (tl2Ub S ρβ 0 (tb - ta) φb) = tl2Ub S ρβ 0 (tb - σ) φb := by
      rw [← tl2Ly_semigroup S h hφb hδ (by linarith [hσ.2])]; congr 1; ring
    rw [s1, s2]
    unfold tl2LyE
    rw [s3]
  rw [hint]
  have e2 : susceptibilityCov (periodicRiesz d S.s) (withDensityReal ρβ) S.β φa
      (equilibriumSemigroup S.dyn ρβ (tb - ta) φb) =
      susceptibilityCov (periodicRiesz d S.s) (withDensityReal ρβ) S.β φa
        (tl2Ub S ρβ 0 (tb - ta) φb) := by
    unfold equilibriumSemigroup
    exact tl2Ly_cov_projMean _ _ _ φa _ (HRS.StaticLimitAux.continuous_of_smooth hg')
  rw [e2, hL, e1]
  unfold tl2LyE
  rfl

/-- The covariance identity for `t_b < t_a`. -/
theorem tl2St_entry_gt (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) {φa φb : Torus d → ℝ}
    (hφa : Torus.IsSmooth φa) (hφb : Torus.IsSmooth φb) {ta tb : ℝ} (htb : 0 ≤ tb) (hab : tb ≤ ta) :
    susceptibilityCov (periodicRiesz d S.s) (withDensityReal ρβ) S.β (tl2Ub S ρβ 0 ta φa) (tl2Ub S ρβ 0 tb φb) +
      2 * S.β⁻¹ * ∫ σ in Set.Icc 0 tb, ∫ x,
        inner ℝ (Torus.grad (propagator S.dyn (fun _ => ρβ) σ ta φa) x)
          (Torus.grad (propagator S.dyn (fun _ => ρβ) σ tb φb) x) * ρβ x =
    susceptibilityCov (periodicRiesz d S.s) (withDensityReal ρβ) S.β (equilibriumSemigroup S.dyn ρβ (ta - tb) φa) φb := by
  have : IsProbabilityMeasure (withDensityReal ρβ) := HRS.isProb_withDensityReal h.1
  have hδ : 0 ≤ ta - tb := by linarith
  have hf' : Torus.IsSmooth (tl2Ub S ρβ 0 (ta - tb) φa) := tl2Ly_smooth S h hφa le_rfl hδ
  have hL := tl2_lyapunov_proof S h hf' hφb htb
  have e1 : tl2Ub S ρβ 0 tb (tl2Ub S ρβ 0 (ta - tb) φa) = tl2Ub S ρβ 0 ta φa := by
    rw [← tl2Ly_semigroup S h hφa hδ htb]; congr 1; ring
  have hint : ∫ σ in Set.Icc 0 tb, ∫ x,
        inner ℝ (Torus.grad (propagator S.dyn (fun _ => ρβ) σ ta φa) x)
          (Torus.grad (propagator S.dyn (fun _ => ρβ) σ tb φb) x) * ρβ x =
      ∫ σ in Set.Icc 0 tb, tl2LyE S ρβ (tl2Ub S ρβ 0 (ta - tb) φa) φb σ := by
    rw [← tl2St_reflect (tl2LyE S ρβ (tl2Ub S ρβ 0 (ta - tb) φa) φb) htb]
    refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
    have s1 : propagator S.dyn (fun _ => ρβ) σ ta φa = tl2Ub S ρβ 0 (ta - σ) φa :=
      tl2Ly_shift S h hφa hσ.1 (hσ.2.trans hab)
    have s2 : propagator S.dyn (fun _ => ρβ) σ tb φb = tl2Ub S ρβ 0 (tb - σ) φb :=
      tl2Ly_shift S h hφb hσ.1 hσ.2
    have s3 : tl2Ub S ρβ 0 (tb - σ) (tl2Ub S ρβ 0 (ta - tb) φa) = tl2Ub S ρβ 0 (ta - σ) φa := by
      rw [← tl2Ly_semigroup S h hφa hδ (by linarith [hσ.2])]; congr 1; ring
    rw [s1, s2]
    unfold tl2LyE
    rw [s3]
  rw [hint]
  have e2 : susceptibilityCov (periodicRiesz d S.s) (withDensityReal ρβ) S.β
      (equilibriumSemigroup S.dyn ρβ (ta - tb) φa) φb =
      susceptibilityCov (periodicRiesz d S.s) (withDensityReal ρβ) S.β
        (tl2Ub S ρβ 0 (ta - tb) φa) φb := by
    unfold equilibriumSemigroup
    exact tl2St_cov_projMean_left _ _ _ _ φb (HRS.StaticLimitAux.continuous_of_smooth hf')
  rw [e2, hL, e1]
  unfold tl2LyE
  rfl

end HRS.ThermLin.Plan2
