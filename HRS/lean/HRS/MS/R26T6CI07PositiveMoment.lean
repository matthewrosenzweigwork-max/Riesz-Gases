import HRS.MS.R26T6CI07MomentAux
import HRS.MS.R26T6CI07Response

/-!
# S11.1 I07: positive-Riesz screened Lipschitz third moment

Physical bounded-density estimate with a finite third spatial moment.
The full thermal-uniform and logarithmic cases are separate obligations.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
namespace HRS.MS.R26T6C
open HRS HRS.Whole HRS.Whole.Q34
variable {d : ℕ}

theorem r26t6c_positive_riesz_screened_lipschitz_third
    (hd : 2 ≤ d) (s M : ℝ) (hs : 0 < s) (h2s : 2*s < d)
    (rho : Euc d → ℝ) (hrho : HRS.Whole.IsProbDensity rho)
    (hM : ∀ x, rho x ≤ M)
    [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)]
    (hm3 : Integrable (fun x : Euc d => ‖x‖ ^ 3)
      (HRS.Whole.withDensityReal rho))
    (K : Lp ℝ 2 (HRS.Whole.withDensityReal rho) →L[ℝ]
      Lp ℝ 2 (HRS.Whole.withDensityReal rho)) (Mg : ℝ)
    (hK : HRS.MS.S111X2.KRep (HRS.Whole.rieszKernel d s)
      (HRS.Whole.withDensityReal rho) K Mg)
    (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (f : Euc d → ℝ) (L : ℝ≥0) (hL : LipschitzWith L f) :
    let mu := HRS.Whole.withDensityReal rho
    let B := 1 + gamma * (2 * Real.sqrt (M * sphereArea d / ((d : ℝ)-2*s) + 1))
    let h := HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) mu gamma f
    Integrable (fun x => |h x| ^ 3) mu ∧
      (∫ x, |h x| ^ 3 ∂mu) ≤
        B ^ 3 * (8 * (L : ℝ) ^ 3 * ∫ x, ‖x‖ ^ 3 ∂mu) := by
  let mu := HRS.Whole.withDensityReal rho
  let R : ℝ := Real.sqrt (M * sphereArea d / ((d : ℝ)-2*s) + 1)
  let B : ℝ := 1 + gamma * (2 * R)
  let h : Euc d → ℝ :=
    HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) mu gamma f
  let p : Euc d → ℝ := HRS.Whole.projMean mu f
  have hB0 : 0 ≤ B := by dsimp [B, R]; positivity
  have hpCube := r26t6c_centered_lipschitz_third mu hm3 f L hL
  have hpMeas : Measurable p :=
    hL.continuous.measurable.sub measurable_const
  have hp3 : MemLp p 3 mu :=
    r26t6c_memLp_three_of_integrable_cube mu p hpMeas hpCube.1
  have hf3 : MemLp f 3 mu := by
    have hsum : MemLp (fun x => p x + HRS.Whole.pair mu f) 3 mu :=
      hp3.add (memLp_const _)
    convert hsum using 1
    funext x
    simp [p, HRS.Whole.projMean]
  have hres := r26t6c_positive_riesz_response_L3
    hd s M hs h2s rho hrho hM K Mg hK gamma hgamma f hf3
  have htop : ENNReal.ofReal B * eLpNorm p 3 mu ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hp3).ne
  have hnorm : lpNorm h 3 mu ≤ B * lpNorm p 3 mu := by
    have hreal := ENNReal.toReal_mono htop hres.2
    simpa only [h, B, R, p, toReal_eLpNorm,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hB0] using hreal
  have hcube : (∫ x, |h x| ^ 3 ∂mu) ≤
      B ^ 3 * ∫ x, |p x| ^ 3 ∂mu := by
    have hh := pow_le_pow_left₀ (lpNorm_nonneg (f := h) (p := (3 : ENNReal)))
      hnorm 3
    rw [r26t6c_lpNorm_three_pow mu h hres.1, mul_pow,
      r26t6c_lpNorm_three_pow mu p hp3] at hh
    exact hh
  refine ⟨?_, ?_⟩
  · simpa only [Real.norm_eq_abs] using
      (hres.1.integrable_norm_pow (by norm_num : (3 : ℕ) ≠ 0))
  · exact hcube.trans (mul_le_mul_of_nonneg_left hpCube.2 (pow_nonneg hB0 _))

end HRS.MS.R26T6C
