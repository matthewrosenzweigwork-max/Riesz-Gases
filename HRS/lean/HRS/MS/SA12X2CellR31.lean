import HRS.MH.AdjRdE3R3

/-!
# S.A.12 R31 (SA12X2): `r3_absorbed_pair`

Corollary of the proved cell interpolation `HRS.MH.AdjointRdP.r3_core1`: choose the scale
`r = (2 ε /(Cn+1))^(1/(d-s))`, so that `Cn r^(d-s) ≤ 2ε` and `Cf r^(d-s-2) = C ε^(-θ/(2-θ))`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12

open HRS HRS.Whole HRS.MH.AdjointRd

theorem r3_absorbed_pair (d : ℕ) (hd : 1 ≤ d) (s : ℝ)
    (hs0 : 0 ≤ s) (hsd : s < d) (hs2 : (d : ℝ) < s+2) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
      ∀ φ ψ : Euc d → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      ∀ u w : Euc d, ‖u‖ ≤ 1 → ‖w‖ ≤ 1 →
      |∫ x, φ x * fderiv ℝ
        (fun x => ∫ y, rieszKernel d s (x-y)*fderiv ℝ ψ y u) x w| ≤
        ε*((∫ x, (fderiv ℝ φ x w)^2)+(∫ y, (fderiv ℝ ψ y u)^2)) +
        C*(1+ε^(-((s+2-d)/((d : ℝ)-s))))*
          ((∫ x, φ x^2)+(∫ y, ψ y^2)) := by
  obtain ⟨Cn, Cf, hCn, hCf, hcore⟩ := HRS.MH.AdjointRdP.r3_core1 hd hs0 hsd hs2
  have hds : (0:ℝ) < (d:ℝ) - s := by linarith
  have hne : (d:ℝ) - s ≠ 0 := hds.ne'
  have hC1 : (0:ℝ) < Cn + 1 := by linarith
  have hK0 : (0:ℝ) ≤ (2 / (Cn + 1)) ^ (-((s+2-d)/((d:ℝ)-s))) :=
    Real.rpow_nonneg (div_nonneg (by norm_num) hC1.le) _
  refine ⟨Cf/2 * (2 / (Cn + 1)) ^ (-((s+2-d)/((d:ℝ)-s))) + 1, ?_, ?_⟩
  · have := mul_nonneg (div_nonneg hCf (by norm_num : (0:ℝ) ≤ 2)) hK0
    linarith
  intro ε hε φ ψ hφ hφc hψ hψc u w hu hw
  have hεq : 0 ≤ ε ^ (-((s+2-d)/((d:ℝ)-s))) := Real.rpow_nonneg hε.le _
  have hX : 0 ≤ (∫ x, (fderiv ℝ φ x w)^2) + ∫ y, (fderiv ℝ ψ y u)^2 :=
    add_nonneg (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
  have hY : 0 ≤ (∫ x, φ x^2) + ∫ y, ψ y^2 :=
    add_nonneg (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
  have hxpos : 0 < 2 / (Cn + 1) * ε := mul_pos (div_pos two_pos hC1) hε
  have hr0 : 0 < (2 / (Cn + 1) * ε) ^ (1 / ((d:ℝ) - s)) := Real.rpow_pos_of_pos hxpos _
  have hrd : ((2 / (Cn + 1) * ε) ^ (1 / ((d:ℝ) - s))) ^ ((d:ℝ) - s) = 2 / (Cn + 1) * ε := by
    rw [← Real.rpow_mul hxpos.le, one_div, inv_mul_cancel₀ hne, Real.rpow_one]
  have he : 1 / ((d:ℝ) - s) * ((d:ℝ) - s - 2) = -((s+2-d)/((d:ℝ)-s)) := by
    field_simp
    ring
  have hrd2 : ((2 / (Cn + 1) * ε) ^ (1 / ((d:ℝ) - s))) ^ ((d:ℝ) - s - 2)
      = (2 / (Cn + 1)) ^ (-((s+2-d)/((d:ℝ)-s))) * ε ^ (-((s+2-d)/((d:ℝ)-s))) := by
    rw [← Real.rpow_mul hxpos.le, Real.mul_rpow (div_nonneg (by norm_num) hC1.le) hε.le, he]
  have hcore' := hcore _ hr0 φ ψ hφ hφc hψ hψc u w hu hw
  rw [hrd, hrd2] at hcore'
  have hA : Cn * (2 / (Cn + 1) * ε) ≤ 2 * ε := by
    have h2 : Cn * (2 / (Cn + 1)) ≤ 2 := by
      rw [mul_div_assoc', div_le_iff₀ hC1]
      linarith
    calc Cn * (2 / (Cn + 1) * ε) = (Cn * (2 / (Cn + 1))) * ε := by ring
      _ ≤ 2 * ε := mul_le_mul_of_nonneg_right h2 hε.le
  have h1 : (Cn * (2 / (Cn + 1) * ε)) * ((∫ x, (fderiv ℝ φ x w)^2) + ∫ y, (fderiv ℝ ψ y u)^2) / 2 ≤
      ε * ((∫ x, (fderiv ℝ φ x w)^2) + ∫ y, (fderiv ℝ ψ y u)^2) := by
    have := mul_le_mul_of_nonneg_right hA hX
    linarith
  have h2 : (Cf * ((2 / (Cn + 1)) ^ (-((s+2-d)/((d:ℝ)-s))) * ε ^ (-((s+2-d)/((d:ℝ)-s))))) *
      ((∫ x, φ x^2) + ∫ y, ψ y^2) / 2 ≤
      (Cf/2 * (2 / (Cn + 1)) ^ (-((s+2-d)/((d:ℝ)-s))) + 1) * (1 + ε ^ (-((s+2-d)/((d:ℝ)-s)))) *
        ((∫ x, φ x^2) + ∫ y, ψ y^2) := by
    have e : (Cf * ((2 / (Cn + 1)) ^ (-((s+2-d)/((d:ℝ)-s))) * ε ^ (-((s+2-d)/((d:ℝ)-s))))) *
        ((∫ x, φ x^2) + ∫ y, ψ y^2) / 2 =
        (Cf/2 * (2 / (Cn + 1)) ^ (-((s+2-d)/((d:ℝ)-s))) * ε ^ (-((s+2-d)/((d:ℝ)-s)))) *
          ((∫ x, φ x^2) + ∫ y, ψ y^2) := by ring
    rw [e]
    have h3 : Cf/2 * (2 / (Cn + 1)) ^ (-((s+2-d)/((d:ℝ)-s))) * ε ^ (-((s+2-d)/((d:ℝ)-s))) ≤
        (Cf/2 * (2 / (Cn + 1)) ^ (-((s+2-d)/((d:ℝ)-s))) + 1) * (1 + ε ^ (-((s+2-d)/((d:ℝ)-s)))) := by
      nlinarith [mul_nonneg (mul_nonneg (div_nonneg hCf (by norm_num : (0:ℝ) ≤ 2)) hK0) hεq]
    exact mul_le_mul_of_nonneg_right h3 hY
  exact le_trans hcore' (add_le_add h1 h2)

end HRS.MH.AdjointRd.Phase2SA12
