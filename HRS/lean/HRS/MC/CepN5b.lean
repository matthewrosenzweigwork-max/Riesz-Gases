import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Exponential

/-!
# Packet N5b: the scale-function ratio is `< 1` uniformly as `ε ↓ 0`

Calculus only.  The predicate-free scale function `cep_scale` is duplicated verbatim from
`HRS/MC/CepaSpec.lean` (same body) so that this packet does not import the spec file.

Route: with `p = 1 - θ > 0`, `S(z) ≤ z^p / p` (since `e^{-λu} ≤ 1`) and
`S(z) ≥ e^{-λz} z^p / p` (since `e^{-λu} ≥ e^{-λz}` on `[0,z]`), and `e^{-λε} ≥ 1 - λε`.
With `s = (1/2)^p ∈ (0,1)`, `q = (1-s)/2`, `ε₀ = (1-s)/(2(λ+1))` the ratio is `≤ 1 - q`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepN5b

/-- The scale function `S(z) = ∫_0^z u^{-θ} e^{-λ u} du` of the localised Bessel-type gap equation.
Same body as `HRS.MC.Cepa.cep_scale`; duplicated so that this packet does not import the spec file. -/
def cep_scale (θ lam z : ℝ) : ℝ := ∫ u in (0 : ℝ)..z, u ^ (-θ) * Real.exp (-(lam * u))

/-- Explicit value of the power integral. -/
theorem n5b_int_pow {θ : ℝ} (hθ : θ < 1) (z : ℝ) :
    ∫ u in (0 : ℝ)..z, u ^ (-θ) = z ^ (-θ + 1) / (-θ + 1) := by
  rw [integral_rpow (Or.inl (by linarith)), Real.zero_rpow (by linarith : (0:ℝ) < -θ + 1).ne', sub_zero]

/-- Integrability of the scale integrand on `[0, z]`, `z ≥ 0`. -/
theorem n5b_intInt {θ lam : ℝ} (hθ : θ < 1) (hlam : 0 ≤ lam) {z : ℝ} (hz : 0 ≤ z) :
    IntervalIntegrable (fun u : ℝ => u ^ (-θ) * Real.exp (-(lam * u))) MeasureTheory.volume 0 z := by
  refine (intervalIntegral.intervalIntegrable_rpow' (r := -θ) (a := (0:ℝ)) (b := z) (by linarith)).mono_fun ?_ ?_
  · apply Measurable.aestronglyMeasurable
    fun_prop
  · refine (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun u hu => ?_)
    rw [uIoc_of_le hz] at hu
    have hu0 : 0 < u := hu.1
    have h1 : 0 ≤ u ^ (-θ) := Real.rpow_nonneg hu0.le _
    have h2 : Real.exp (-(lam * u)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hlam hu0.le])
    simp only
    rw [Real.norm_of_nonneg (mul_nonneg h1 (Real.exp_pos _).le), Real.norm_of_nonneg h1]
    exact mul_le_of_le_one_right h1 h2

/-- Upper bound `S(z) ≤ z^p / p`. -/
theorem n5b_S_le {θ lam : ℝ} (hθ : θ < 1) (hlam : 0 ≤ lam) {z : ℝ} (hz : 0 ≤ z) :
    cep_scale θ lam z ≤ z ^ (-θ + 1) / (-θ + 1) := by
  rw [← n5b_int_pow hθ z]
  unfold cep_scale
  refine intervalIntegral.integral_mono_on hz (n5b_intInt hθ hlam hz)
    (intervalIntegral.intervalIntegrable_rpow' (r := -θ) (a := (0:ℝ)) (b := z) (by linarith)) (fun u hu => ?_)
  have hu0 : 0 ≤ u := hu.1
  have h1 : 0 ≤ u ^ (-θ) := Real.rpow_nonneg hu0 _
  have h2 : Real.exp (-(lam * u)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hlam hu0])
  exact mul_le_of_le_one_right h1 h2

/-- Lower bound `S(z) ≥ e^{-λz} z^p / p`. -/
theorem n5b_S_ge {θ lam : ℝ} (hθ : θ < 1) (hlam : 0 ≤ lam) {z : ℝ} (hz : 0 ≤ z) :
    Real.exp (-(lam * z)) * (z ^ (-θ + 1) / (-θ + 1)) ≤ cep_scale θ lam z := by
  rw [← n5b_int_pow hθ z, ← intervalIntegral.integral_const_mul]
  unfold cep_scale
  refine intervalIntegral.integral_mono_on hz
    ((intervalIntegral.intervalIntegrable_rpow' (r := -θ) (a := (0:ℝ)) (b := z) (by linarith)).const_mul _)
    (n5b_intInt hθ hlam hz) (fun u hu => ?_)
  have hu0 : 0 ≤ u := hu.1
  have huz : u ≤ z := hu.2
  have h1 : 0 ≤ u ^ (-θ) := Real.rpow_nonneg hu0 _
  have h2 : Real.exp (-(lam * z)) ≤ Real.exp (-(lam * u)) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left huz hlam])
  calc Real.exp (-(lam * z)) * u ^ (-θ)
      ≤ Real.exp (-(lam * u)) * u ^ (-θ) := mul_le_mul_of_nonneg_right h2 h1
    _ = u ^ (-θ) * Real.exp (-(lam * u)) := mul_comm _ _

/-- Pure algebra closing step. -/
theorem n5b_alg (s e X A B : ℝ) (hs0 : 0 < s) (hX : 0 < X) (he : (1 + s) / 2 ≤ e)
    (hA : A ≤ s * X) (hB : e * X ≤ B) : A ≤ (1 - (1 - s) / 2) * B := by
  have hc : 0 ≤ (1 + s) / 2 := by linarith
  have h1 : s * X ≤ (1 + s) / 2 * ((1 + s) / 2) * X := by
    nlinarith [mul_nonneg (sq_nonneg (1 - s)) hX.le]
  have h2 : (1 + s) / 2 * ((1 + s) / 2) * X ≤ (1 + s) / 2 * B := by
    have h3 : (1 + s) / 2 * X ≤ e * X := mul_le_mul_of_nonneg_right he hX.le
    calc (1 + s) / 2 * ((1 + s) / 2) * X = (1 + s) / 2 * ((1 + s) / 2 * X) := by ring
      _ ≤ (1 + s) / 2 * (e * X) := mul_le_mul_of_nonneg_left h3 hc
      _ ≤ (1 + s) / 2 * B := mul_le_mul_of_nonneg_left hB hc
  have h4 : (1 - (1 - s) / 2) = (1 + s) / 2 := by ring
  rw [h4]
  linarith

/-- **N5b (the scale-function ratio is `< 1`, uniformly as `ε ↓ 0`)**: for `θ < 1` and `λ ≥ 0` there are
`ε₀, q > 0` with `S(ε/2)/S(ε) ≤ 1 - q` for all `0 < ε ≤ ε₀`.  (Explicitly `S(ε/2)/S(ε) → 2^{-(1-θ)}`.)
Calculus only. -/
theorem cep_N5b_scale_ratio_proof {θ lam : ℝ} (hθ : θ < 1) (hlam : 0 ≤ lam) :
    ∃ ε₀ q : ℝ, 0 < ε₀ ∧ 0 < q ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → cep_scale θ lam (ε / 2) / cep_scale θ lam ε ≤ 1 - q := by
  have hp0 : (0:ℝ) < -θ + 1 := by linarith
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = (1 / 2 : ℝ) ^ (-θ + 1) := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs_def]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hs1 : s < 1 := by rw [hs_def]; exact Real.rpow_lt_one (by norm_num) (by norm_num) hp0
  refine ⟨(1 - s) / (2 * (lam + 1)), (1 - s) / 2, ?_, by linarith, ?_⟩
  · exact div_pos (by linarith) (mul_pos two_pos (by linarith))
  intro ε hε hεε₀
  have hK : ε * (2 * (lam + 1)) ≤ 1 - s :=
    (le_div_iff₀ (mul_pos two_pos (by linarith))).mp hεε₀
  have hle_lam : lam * ε ≤ (1 - s) / 2 := by nlinarith [hK, hε, hlam]
  have hX : 0 < ε ^ (-θ + 1) / (-θ + 1) := div_pos (Real.rpow_pos_of_pos hε _) hp0
  have hdiv : (ε / 2) ^ (-θ + 1) = s * ε ^ (-θ + 1) := by
    rw [hs_def, show ε / 2 = 1 / 2 * ε by ring, Real.mul_rpow (by norm_num) hε.le]
  have he : (1 + s) / 2 ≤ Real.exp (-(lam * ε)) := by
    linarith [Real.add_one_le_exp (-(lam * ε))]
  have hB := n5b_S_ge hθ hlam hε.le
  have hSpos : 0 < cep_scale θ lam ε :=
    lt_of_lt_of_le (mul_pos (lt_of_lt_of_le (by linarith) he) hX) hB
  have hA : cep_scale θ lam (ε / 2) ≤ s * (ε ^ (-θ + 1) / (-θ + 1)) := by
    calc cep_scale θ lam (ε / 2) ≤ (ε / 2) ^ (-θ + 1) / (-θ + 1) := n5b_S_le hθ hlam (by linarith)
      _ = s * (ε ^ (-θ + 1) / (-θ + 1)) := by rw [hdiv, mul_div_assoc]
  rw [div_le_iff₀ hSpos]
  exact n5b_alg s _ _ _ _ hs0 hX he hA hB

end HRS.MC.CepN5b
