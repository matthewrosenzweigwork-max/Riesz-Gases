import HRS.MS.WadAux17
import HRS.MS.WadAux13

/-!
# S8.3, packet D2'''' (Route A): gradient smoothing of the Mehler semigroup on `C_M`

For `0 < τ ≤ T` and `g` continuous with `|g| ≤ C⟨·⟩^M`:
* `s84_P_fderiv`: `P_τ g ∈ C¹` and `‖D P_τ g(x)‖ ≤ K₁ C τ^{-1/2} ⟨x⟩^M` (`K₁ = K₁(d, M, a, ν, T)`);
* `s84_P_fderiv_holder`: for `‖x'-x‖ ≤ 1/4`, `‖D P_τ g(x') - D P_τ g(x)‖ ≤ K₂ C τ^{-3/4} ‖x'-x‖^{1/2} ⟨x⟩^M`.
The Hölder bound is obtained from `P_τ = P_{τ/2} P_{τ/2}`, `D P_{τ/2} f = e^{-aτ/2} P_{τ/2} Df`
and the Lipschitz smoothing `s83_G_lip`, interpolated with the sup bound.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

/-- The lower constant `s_T = √(2 ν e^{-2aT})` of `σ_τ ≥ s_T √τ`. -/
def s84_sT (a ν T : ℝ) : ℝ := Real.sqrt (2 * ν * Real.exp (-2 * a * T))

theorem s84_sT_pos {a ν T : ℝ} (hν : 0 < ν) : 0 < s84_sT a ν T :=
  Real.sqrt_pos.2 (by positivity)

theorem s84_ms_lower {a ν T τ : ℝ} (ha : 0 < a) (hν : 0 < ν) (hτ : 0 ≤ τ) (hτT : τ ≤ T) :
    s84_sT a ν T * Real.sqrt τ ≤ s83_ms a ν τ := by
  unfold s84_sT s83_ms
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  have h1 : Real.exp (-2 * a * T) ≤ Real.exp (-2 * a * τ) := by
    apply Real.exp_le_exp.2
    nlinarith
  have h2 : (2 * a * τ + 1) * Real.exp (-(2 * a * τ)) ≤ 1 := by
    have := Real.add_one_le_exp (2 * a * τ)
    have h3 : Real.exp (2 * a * τ) * Real.exp (-(2 * a * τ)) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-(2 * a * τ)), mul_le_mul_of_nonneg_right this (Real.exp_pos (-(2 * a * τ))).le]
  have e : Real.exp (-2 * a * τ) = Real.exp (-(2 * a * τ)) := by congr 1; ring
  rw [e] at h1
  rw [le_div_iff₀ ha]
  have h4 : 2 * ν * Real.exp (-2 * a * T) * τ * a ≤ ν * (1 - Real.exp (-(2 * a * τ))) := by
    have hh : 2 * a * τ * Real.exp (-(2 * a * τ)) ≤ 1 - Real.exp (-(2 * a * τ)) := by linarith
    have := mul_le_mul_of_nonneg_left hh hν.le
    calc 2 * ν * Real.exp (-2 * a * T) * τ * a = ν * (2 * a * τ * Real.exp (-2 * a * T)) := by ring
      _ ≤ ν * (2 * a * τ * Real.exp (-(2 * a * τ))) := by
          refine mul_le_mul_of_nonneg_left ?_ hν.le
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ _ := this
  nlinarith [h4]

/-- The gradient constant. -/
def s84_K1 (d : ℕ) (M a ν T : ℝ) : ℝ := 2 ^ M * mom1 d M (Real.sqrt (ν / a)) / s84_sT a ν T

theorem s84_K1_nonneg {a ν T : ℝ} (M : ℝ) (ha : 0 < a) (hν : 0 < ν) : 0 ≤ s84_K1 d M a ν T :=
  div_nonneg (mul_nonneg (by positivity) (s83_mom1_nonneg M (Real.sqrt_nonneg _))) (s84_sT_pos hν).le

/-- **Gradient smoothing of the Mehler semigroup** for a continuous datum of weighted growth. -/
theorem s84_P_fderiv {a ν T M C : ℝ} (ha : 0 < a) (hν : 0 < ν) (hM : 0 ≤ M) {g : Euc d → ℝ}
    (hg : Continuous g) (hw : Wt M C g) {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T) :
    ContDiff ℝ 1 (s83_P a ν τ g) ∧ ∀ x, ‖fderiv ℝ (s83_P a ν τ g) x‖ ≤
      s84_K1 d M a ν T * C * (Real.sqrt τ)⁻¹ * jbracket x ^ M := by
  have hc : |s83_mc a τ| ≤ 1 := s83_abs_mc_le_one ha.le hτ0.le
  have hσ : |s83_ms a ν τ| ≤ Real.sqrt (ν / a) := s83_abs_ms_le ha hν.le hτ0.le
  have hσ0 : s83_ms a ν τ ≠ 0 := (s83_ms_pos ha hν hτ0).ne'
  refine ⟨s84_G_contDiff hg hM hw hc hσ hσ0, fun x => ?_⟩
  have h1 := s84_G_fderiv_norm hg hM hw hc hσ hσ0 x
  refine h1.trans ?_
  have hs := s84_ms_lower ha hν hτ0.le hτT
  have hsT := s84_sT_pos (a := a) (T := T) hν
  have hsq : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ0
  have hσpos : 0 < |s83_ms a ν τ| := abs_pos.2 hσ0
  have hσe : |s83_ms a ν τ| = s83_ms a ν τ := abs_of_nonneg (s83_ms_nonneg _ _ _)
  have hdiv : |s83_mc a τ| / |s83_ms a ν τ| ≤ (s84_sT a ν T)⁻¹ * (Real.sqrt τ)⁻¹ := by
    rw [← mul_inv, div_eq_mul_inv]
    calc |s83_mc a τ| * |s83_ms a ν τ|⁻¹ ≤ 1 * |s83_ms a ν τ|⁻¹ :=
          mul_le_mul_of_nonneg_right hc (inv_nonneg.2 hσpos.le)
      _ ≤ (s84_sT a ν T * Real.sqrt τ)⁻¹ := by
          rw [one_mul]
          exact inv_anti₀ (mul_pos hsT hsq) (by rw [hσe]; exact hs)
  have hK : 0 ≤ C * 2 ^ M * mom1 d M (Real.sqrt (ν / a)) := by
    have := hw.nonneg
    exact mul_nonneg (mul_nonneg this (by positivity)) (s83_mom1_nonneg M (Real.sqrt_nonneg _))
  have hjb : 0 ≤ jbracket x ^ M := Real.rpow_nonneg (s83_jb_pos _).le _
  calc |s83_mc a τ| / |s83_ms a ν τ| * (C * 2 ^ M * mom1 d M (Real.sqrt (ν / a))) * jbracket x ^ M
      ≤ ((s84_sT a ν T)⁻¹ * (Real.sqrt τ)⁻¹) * (C * 2 ^ M * mom1 d M (Real.sqrt (ν / a))) * jbracket x ^ M := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdiv hK) hjb
    _ = s84_K1 d M a ν T * C * (Real.sqrt τ)⁻¹ * jbracket x ^ M := by
        unfold s84_K1; field_simp

end HRS.MS.Wad
