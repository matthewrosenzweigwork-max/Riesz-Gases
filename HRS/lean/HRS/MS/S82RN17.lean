import HRS.MS.S82RN16
import HRS.Equilibrium.PinLinf

/-!
# S8.2 R02 (S82R), N17: the sup-norm part of `PinComparison` (`||f_N - 1||_inf <= C delta_N`)
Absorption via the cavity equation: the calibration smallness `beta * (q*mu) <= 1/1000` makes the row term
`lam n (q*(f_nu - 1))` at most `(||f_N - 1||_inf + C/N)/1000`, so the sup norm is absorbed.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82R
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.External

variable {d : ℕ}

lemma s82r_top_le {E : Type*} [MeasurableSpace E] {μ : Measure E} {f : E → ℝ} (hf : Measurable f)
    {B : ℝ} (h : ∀ᵐ x ∂μ, |f x| ≤ B) : eLpNorm f ∞ μ ≤ ENNReal.ofReal B := by
  rw [eLpNorm_exponent_top hf.aestronglyMeasurable]
  exact eLpNormEssSup_le_of_ae_bound (by simpa [Real.norm_eq_abs] using h)

lemma s82r_ae_le_top {E : Type*} [MeasurableSpace E] {μ : Measure E} {f : E → ℝ} (hf : Measurable f)
    {e : ℝ} (he0 : 0 ≤ e) (hX : eLpNorm f ∞ μ = ENNReal.ofReal e) : ∀ᵐ x ∂μ, |f x| ≤ e := by
  have h := ae_le_eLpNormEssSup (f := f) (μ := μ)
  rw [← eLpNorm_exponent_top hf.aestronglyMeasurable, hX] at h
  filter_upwards [h] with x hx
  rw [Real.enorm_eq_ofReal_abs] at hx
  exact (ENNReal.ofReal_le_ofReal_iff he0).1 hx

/-- The cavity marginal at `n` particles via the empty-pin presentation. -/
lemma s82r_cavMarg_fin0 {μ : Measure (Euc d)} (V : WeakPotential μ) (lam : ℝ) (n : ℕ) [NeZero n] :
    (pinnedLaw V lam n (fun i : Fin 0 => i.elim0)).map (fun y => y 0) = RefMarg.cavMarg V lam n := by
  unfold RefMarg.cavMarg
  rw [s82r_pinnedLaw_zero V lam n, RefMarg.pinnedLaw_empty V lam n (fun e : Empty => e.elim)]

/-- Like `s82r_part2_ident`, with the formula for the field. -/
lemma s82r_part1_ident (hd : 2 ≤ d) {beta : ℝ} (hbeta : 0 < beta) {q : Euc d → ℝ}
    (hq : ShortRangePole d q) {rho : Euc d → ℝ} {h : ℕ → Euc d → ℝ}
    (hsr : ∀ x, beta * HRS.Whole.convMeasure q (HRS.Whole.withDensityReal rho) x ≤ 1 / 1000)
    {G c : ℝ} (hG : 0 < G) (hρ : HRS.Whole.IsProbDensity rho)
    (hρG : HRS.Whole.HasR2GaussianUpper G c rho) {N : ℕ} {t : ℝ}
    (hhm : Measurable (h N)) (hh : ∀ x, |h N x| ≤ t) (hN0 : 0 < N) :
    ∃ V : WeakPotential (HRS.Whole.withDensityReal rho), V.M = 1 / 1000 + t ∧ V.M' = t ∧
      V.γ = 1 / (1000 * beta) ∧ (∀ x y, V.q x y = q (x - y)) ∧
      IsField (HRS.Whole.withDensityReal rho) V.φ (1 / 1000 + t) t ∧
      (∀ x, V.φ x = beta * HRS.Whole.convMeasure q (HRS.Whole.withDensityReal rho) x + h N x) ∧
      (haveI : NeZero N := ⟨hN0.ne'⟩;
        refMarginal q h (HRS.Whole.withDensityReal rho) beta N = RefMarg.cavMarg V (beta / N) N) := by
  haveI := s82r_isProb hρ
  refine ⟨s82r_potW hd hbeta hq hsr hG hρ hρG hhm hh, rfl, rfl, rfl, fun x y => rfl,
    s82r_isFieldW hd hbeta hq hsr hG hρ hρG hhm hh, fun x => rfl, ?_⟩
  exact s82r_refMarg_eq hN0 (s82r_potW hd hbeta hq hsr hG hρ hρG hhm hh) rfl (fun x y => rfl) hbeta.le

end HRS.MS.S82R

end
