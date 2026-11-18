import HRS.MS.UniqN3aI
import HRS.MS.UniqN1aF

/-!
# N1b of `UniqPlan.md`, part (a): the `L²` bound for `g * D_q² v` at `s = d - 2`

From `n3a_bridge` with `u = h := g * D_q² v ∈ L²` (`w_memLp`): `∫ h² = -symbolForm m_q h v`, and
the symbol `m_q = c(2π⟨ξ,q⟩)²‖ξ‖^{-2}` is bounded by `c(2π)²‖q‖²`, so `∫ h² ≤ (c(2π)²‖q‖²)² ∫ v²`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff ComplexConjugate

namespace HRS.MS.UniqN1b

open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.UniqT3 HRS.MS.UniqN3a

variable {d : ℕ}

theorem n1b_eLpNorm_eq {f : Euc d → ℝ} (hf : MemLp f 2 volume) :
    eLpNorm f 2 volume = ENNReal.ofReal (Real.sqrt (∫ x, f x ^ 2)) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  congr 1
  rw [Real.sqrt_eq_rpow]
  simp only [ENNReal.toReal_ofNat]
  congr 1
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  · norm_num

theorem n1b_symbol_bound {c s : ℝ} (hc : 0 < c) (hsd : s = (d : ℝ) - 2) (q ξ : Euc d) :
    |c * (2 * Real.pi * inner ℝ ξ q) ^ 2 * ‖ξ‖ ^ (s - d)| ≤ c * (2 * Real.pi) ^ 2 * ‖q‖ ^ 2 := by
  have hexp : s - (d : ℝ) = -2 := by rw [hsd]; ring
  rw [hexp]
  by_cases hξ : ξ = 0
  · subst hξ
    simp only [inner_zero_left, mul_zero, norm_zero]
    simp
    positivity
  · have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    have hp : ‖ξ‖ ^ (-2 : ℝ) = (‖ξ‖ ^ 2)⁻¹ := by
      rw [Real.rpow_neg hn.le, Real.rpow_two]
    rw [hp]
    have hcs : (inner ℝ ξ q) ^ 2 ≤ ‖ξ‖ ^ 2 * ‖q‖ ^ 2 := by
      have := abs_real_inner_le_norm ξ q
      calc (inner ℝ ξ q) ^ 2 = |inner ℝ ξ q| ^ 2 := (sq_abs _).symm
        _ ≤ (‖ξ‖ * ‖q‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
        _ = _ := by ring
    have hpos : 0 < ‖ξ‖ ^ 2 := by positivity
    rw [abs_of_nonneg (by positivity)]
    rw [show c * (2 * Real.pi * inner ℝ ξ q) ^ 2 * (‖ξ‖ ^ 2)⁻¹ =
      c * (2 * Real.pi) ^ 2 * ((inner ℝ ξ q) ^ 2 / ‖ξ‖ ^ 2) by field_simp]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [div_le_iff₀ hpos]; linarith

/-- The `L²` bound of `g * D_q² v`, `s = d - 2`. -/
theorem n1b_qq_L2 (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s = (d : ℝ) - 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : Euc d) (v : Euc d → ℝ), ContDiff ℝ 2 v → HasCompactSupport v →
      MemLp (HRS.Whole.convFun (rieszKernel d s) (qq q v)) 2 volume ∧
      ∫ x, (HRS.Whole.convFun (rieszKernel d s) (qq q v) x) ^ 2 ≤ (K * ‖q‖ ^ 2) ^ 2 * ∫ x, v x ^ 2 := by
  have hs2 : (d : ℝ) - 2 ≤ s := hsd.symm.le
  have hsd' : s < d := by rw [hsd]; linarith
  obtain ⟨c, hc, hB⟩ := n3a_bridge hd hs0 hs2 hsd'
  refine ⟨c * (2 * Real.pi) ^ 2, by positivity, fun q v hv hvc => ?_⟩
  have hmem := w_memLp hd hs0 hs2 hsd' hv hvc q
  refine ⟨hmem, ?_⟩
  set h := HRS.Whole.convFun (rieszKernel d s) (qq q v) with hh
  obtain ⟨-, hint, heq⟩ := hB q h v hmem hv hvc
  have hvm : MemLp v 2 volume := hv.continuous.memLp_of_hasCompactSupport hvc
  set A : ℝ := c * (2 * Real.pi) ^ 2 * ‖q‖ ^ 2 with hA
  have hH : ∫ x, h x ^ 2 = -(symbolForm (fun ξ : Euc d => c * (2 * Real.pi * inner ℝ ξ q) ^ 2 *
      ‖ξ‖ ^ (s - d)) h v) := by
    rw [heq]
    have : (fun x => h x * HRS.Whole.convFun (rieszKernel d s)
        (fun y => fderiv ℝ (fun z => fderiv ℝ v z q) y q) x) = fun x => h x ^ 2 := by
      funext x; rw [sq]; rfl
    rw [this]; ring
  set F : Euc d → ℂ := fun ξ => ((c * (2 * Real.pi * inner ℝ ξ q) ^ 2 * ‖ξ‖ ^ (s - d) : ℝ) : ℂ) *
    (fourierL2 h ξ * conj (fourierL2 v ξ)) with hF
  have hsym : symbolForm (fun ξ : Euc d => c * (2 * Real.pi * inner ℝ ξ q) ^ 2 *
      ‖ξ‖ ^ (s - d)) h v = (∫ ξ, F ξ).re := rfl
  have hG : Integrable (fun ξ => (1 / 2 : ℝ) * (‖fourierL2 h ξ‖ ^ 2 +
      A ^ 2 * ‖fourierL2 v ξ‖ ^ 2)) volume :=
    ((integrable_norm_sq_fourierL2 hmem).add
      ((integrable_norm_sq_fourierL2 hvm).const_mul _)).const_mul _
  have hpt : ∀ ξ, ‖F ξ‖ ≤ (1 / 2 : ℝ) * (‖fourierL2 h ξ‖ ^ 2 + A ^ 2 * ‖fourierL2 v ξ‖ ^ 2) := by
    intro ξ
    have hb : |c * (2 * Real.pi * inner ℝ ξ q) ^ 2 * ‖ξ‖ ^ (s - d)| ≤ A :=
      n1b_symbol_bound (d := d) hc hsd q ξ
    simp only [hF]
    rw [norm_mul, norm_mul, Complex.norm_real, RCLike.norm_conj, Real.norm_eq_abs]
    have h1 : |c * (2 * Real.pi * inner ℝ ξ q) ^ 2 * ‖ξ‖ ^ (s - d)| *
        (‖fourierL2 h ξ‖ * ‖fourierL2 v ξ‖) ≤ A * (‖fourierL2 h ξ‖ * ‖fourierL2 v ξ‖) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    nlinarith [sq_nonneg (‖fourierL2 h ξ‖ - A * ‖fourierL2 v ξ‖)]
  have hle : ‖∫ ξ, F ξ‖ ≤ ∫ ξ, (1 / 2 : ℝ) * (‖fourierL2 h ξ‖ ^ 2 +
      A ^ 2 * ‖fourierL2 v ξ‖ ^ 2) :=
    (norm_integral_le_integral_norm _).trans (integral_mono hint.norm hG hpt)
  have hint2 : ∫ ξ, (1 / 2 : ℝ) * (‖fourierL2 h ξ‖ ^ 2 + A ^ 2 * ‖fourierL2 v ξ‖ ^ 2) =
      (1 / 2) * ((∫ x, h x ^ 2) + A ^ 2 * ∫ x, v x ^ 2) := by
    rw [integral_const_mul, integral_add (integrable_norm_sq_fourierL2 hmem)
      ((integrable_norm_sq_fourierL2 hvm).const_mul _), integral_const_mul,
      integral_norm_sq_fourierL2 hmem, integral_norm_sq_fourierL2 hvm]
  have hre : -(∫ ξ, F ξ).re ≤ ‖∫ ξ, F ξ‖ :=
    (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  rw [hint2] at hle
  have := hre.trans hle
  have hH' : ∫ x, h x ^ 2 = -(∫ ξ, F ξ).re := by rw [hH, hsym]
  rw [hH']
  rw [hH'] at this
  nlinarith [this]

end HRS.MS.UniqN1b
