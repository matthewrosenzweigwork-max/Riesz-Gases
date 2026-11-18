import HRS.MS.S11Q3A3

/-!
# S11.3 / S11.4 (worker S11Q3), A4: the potential `Γ_t = g * ρ_t` of a regular family

`s11q3_Gam φ x = ∫ g(z) φ(x - z) dz`.  For `s11q3_Reg d ρ D c B`: `Γ_t ∈ C²` with `D_xΓ_t e = ∫ g(z) D_xρ_t(x-z) e dz`,
`D²_xΓ_t v e = ∫ g(z) D²_xρ_t(x-z) v e dz`; the clamped family `Γ̄_t = Γ_{max t 0}` is a `s11q3_Jet2`;
`∂_tΓ = g * D` (two-sided for `t > 0`, right derivative for `t ≥ 0`), with `g * D` continuous on `[0,∞) × ℝ^d`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S11Q3

open HRS HRS.Whole HRS.MS.MovForce HRS.MS.S113BD

variable {d : ℕ} {s : ℝ}

/-- `g * φ`. -/
def s11q3_Gam (d : ℕ) (s : ℝ) (φ : Euc d → ℝ) (x : Euc d) : ℝ := ∫ z, rieszKernel d s z * φ (x - z)

theorem s11q3_Gam_eq (φ : Euc d → ℝ) : s11q3_Gam d s φ = HRS.Whole.convFun (rieszKernel d s) φ :=
  funext fun x => (mv1_convFun_eq _ _ x).symm

theorem s11q3_movGauss2 {f : Euc d → ℝ} {c B : ℝ} (hc : 0 < c) (h0 : ∀ x, |f x| ≤ B * Real.exp (-c * ‖x‖ ^ 2))
    (h1 : ∀ x, ‖fderiv ℝ f x‖ ≤ B * Real.exp (-c * ‖x‖ ^ 2))
    (h2 : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ B * Real.exp (-c * ‖x‖ ^ 2)) : MovGauss 2 f := by
  intro j hj
  refine ⟨B, c, hc, fun x => ?_⟩
  interval_cases j
  · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]; exact h0 x
  · rw [norm_iteratedFDeriv_one]; exact h1 x
  · rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]; exact h2 x

section Gam

variable {ρ D : ℝ → Euc d → ℝ} {c B : ℝ}

theorem s11q3_Reg.movGauss2 (R : s11q3_Reg d ρ D c B) {t : ℝ} (ht : 0 ≤ t) : MovGauss 2 (ρ t) :=
  s11q3_movGauss2 R.hc (R.g0 t ht) (R.g1 t ht) (R.g2 t ht)

theorem s11q3_Gam_contDiff (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (R : s11q3_Reg d ρ D c B) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ 2 (s11q3_Gam d s (ρ t)) := by
  rw [s11q3_Gam_eq]
  have := mv1_conv_contDiff hd hs0 hsd 2 (ρ t) (by exact_mod_cast R.cd t ht) (R.movGauss2 ht)
  exact_mod_cast this

theorem s11q3_Gam_fderiv (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (R : s11q3_Reg d ρ D c B) {t : ℝ} (ht : 0 ≤ t)
    (x e : Euc d) :
    fderiv ℝ (s11q3_Gam d s (ρ t)) x e = ∫ z, rieszKernel d s z * fderiv ℝ (ρ t) (x - z) e := by
  have hcd : ContDiff ℝ 1 (ρ t) := (R.cd t ht).of_le (by norm_num)
  obtain ⟨L, hL, hLe, -⟩ := mv1_hasFDerivAt_convFun hd hs0 hsd R.hc R.hB hcd (R.g0 t ht) (R.g1 t ht) x
  rw [s11q3_Gam_eq, hL.fderiv]
  exact hLe e

theorem s11q3_Gam_fderiv2 (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (R : s11q3_Reg d ρ D c B) {t : ℝ} (ht : 0 ≤ t)
    (x v e : Euc d) :
    fderiv ℝ (fderiv ℝ (s11q3_Gam d s (ρ t))) x v e =
      ∫ z, rieszKernel d s z * fderiv ℝ (fderiv ℝ (ρ t)) (x - z) v e := by
  have hρ2 := R.cd t ht
  have hΓ2 := s11q3_Gam_contDiff hd hs0 hsd R ht
  have hfρ : ContDiff ℝ 1 (fderiv ℝ (ρ t)) := hρ2.fderiv_right (m := 1) (by norm_num)
  have hfρd : Differentiable ℝ (fderiv ℝ (ρ t)) := hfρ.differentiable (by norm_num)
  set he : Euc d → ℝ := fun y => fderiv ℝ (ρ t) y e with hhe
  have hhe1 : ContDiff ℝ 1 he := (ContinuousLinearMap.apply ℝ ℝ e).contDiff.comp hfρ
  have hhe_fd : ∀ y, HasFDerivAt he ((ContinuousLinearMap.apply ℝ ℝ e).comp (fderiv ℝ (fderiv ℝ (ρ t)) y)) y := fun y =>
    (ContinuousLinearMap.apply ℝ ℝ e).hasFDerivAt.comp y (hfρd y).hasFDerivAt
  have hbe : ‖e‖ * B * 1 ≥ 0 := by have := R.hB; positivity
  have hb0 : ∀ y, |he y| ≤ (B * ‖e‖) * Real.exp (-c * ‖y‖ ^ 2) := fun y => by
    have h1 := (fderiv ℝ (ρ t) y).le_opNorm e
    have h2 := R.g1 t ht y
    rw [← Real.norm_eq_abs]
    calc ‖he y‖ ≤ ‖fderiv ℝ (ρ t) y‖ * ‖e‖ := h1
      _ ≤ (B * Real.exp (-c * ‖y‖ ^ 2)) * ‖e‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = _ := by ring
  have hb1 : ∀ y, ‖fderiv ℝ he y‖ ≤ (B * ‖e‖) * Real.exp (-c * ‖y‖ ^ 2) := fun y => by
    rw [(hhe_fd y).fderiv]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h3 : ‖ContinuousLinearMap.apply ℝ ℝ e‖ ≤ ‖e‖ := ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun f => by
      simpa [mul_comm] using f.le_opNorm e)
    calc ‖ContinuousLinearMap.apply ℝ ℝ e‖ * ‖fderiv ℝ (fderiv ℝ (ρ t)) y‖
        ≤ ‖e‖ * (B * Real.exp (-c * ‖y‖ ^ 2)) :=
          mul_le_mul h3 (R.g2 t ht y) (ContinuousLinearMap.opNorm_nonneg _) (norm_nonneg _)
      _ = _ := by ring
  have hB' : 0 ≤ B * ‖e‖ := mul_nonneg R.hB (norm_nonneg _)
  obtain ⟨L, hL, hLe, -⟩ := mv1_hasFDerivAt_convFun hd hs0 hsd R.hc hB' hhe1 hb0 hb1 x
  have hfun : (fun y => fderiv ℝ (s11q3_Gam d s (ρ t)) y e) = HRS.Whole.convFun (rieszKernel d s) he := by
    funext y
    rw [s11q3_Gam_fderiv hd hs0 hsd R ht y e, mv1_convFun_eq]
  have hΓ' : DifferentiableAt ℝ (fderiv ℝ (s11q3_Gam d s (ρ t))) x :=
    ((hΓ2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  have hA : HasFDerivAt (fun y => fderiv ℝ (s11q3_Gam d s (ρ t)) y e)
      ((ContinuousLinearMap.apply ℝ ℝ e).comp (fderiv ℝ (fderiv ℝ (s11q3_Gam d s (ρ t))) x)) x :=
    (ContinuousLinearMap.apply ℝ ℝ e).hasFDerivAt.comp x hΓ'.hasFDerivAt
  rw [hfun] at hA
  have hLeq := hA.unique hL
  have := congrArg (fun T : Euc d →L[ℝ] ℝ => T v) hLeq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] at this
  rw [this, hLe v]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  beta_reduce
  rw [(hhe_fd (x - z)).fderiv]
  simp

end Gam

end HRS.MS.S11Q3

end
