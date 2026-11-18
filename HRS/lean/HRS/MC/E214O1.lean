import Mathlib

/-!
# Packet E214O, part 1: generic analysis (weighted `L^p` integral bound, exponential weights)

* `o_exp_weight_le` : `e^{-c(a-v)} e^{-c'v} ≤ e^{cT} e^{-min(c,c') a}` on `[0,a+T]`.
* `o_eLpNorm_integral_le` : Minkowski/Jensen for an integral over `Ioc 0 n` of a jointly measurable family with a
  uniform `L^p(P)`-bound: `‖∫_0^n G^v dv‖_{L^p(P)} ≤ n B`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MC.E214O

theorem o_exp_weight_le {c c' a T v : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c') (hT : 0 ≤ T) (ha : 0 ≤ a) (hv0 : 0 ≤ v)
    (hv : v ≤ a + T) :
    Real.exp (-c * (a - v)) * Real.exp (-c' * v) ≤ Real.exp (c * T) * Real.exp (-(min c c') * a) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 := min_le_left c c'
  have h2 := min_le_right c c'
  have h3 : 0 ≤ c * T := mul_nonneg hc hT
  rcases le_total v a with h | h
  · nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h), mul_nonneg (sub_nonneg.2 h2) hv0]
  · nlinarith [mul_nonneg (sub_nonneg.2 h2) ha, mul_nonneg hc (sub_nonneg.2 hv), mul_nonneg hc (sub_nonneg.2 h),
      mul_nonneg hc' (sub_nonneg.2 h)]

/-- Jensen on a finite interval measure, `ℝ≥0∞` form:
`(∫⁻ ‖f‖ₑ)^p ≤ ν(univ)^{p-1} ∫⁻ ‖f‖ₑ^p`. -/
theorem o_lintegral_enorm_rpow_le {ν : Measure ℝ} {f : ℝ → ℝ} (hf : AEStronglyMeasurable f ν) {p : ℝ}
    (hp : 1 ≤ p) :
    (∫⁻ v, ‖f v‖ₑ ∂ν) ^ p ≤ (∫⁻ v, ‖f v‖ₑ ^ p ∂ν) * ν Set.univ ^ (p - 1) := by
  have h := eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ (p := 1) (q := p) one_pos hp hf
  unfold eLpNorm' at h
  simp only [ENNReal.rpow_one, div_one, one_div] at h
  have h2 := ENNReal.rpow_le_rpow h (show 0 ≤ p by linarith)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at h2
  have e1 : p⁻¹ * p = 1 := inv_mul_cancel₀ (by linarith)
  have e2 : (1 - p⁻¹) * p = p - 1 := by field_simp
  rw [e1, e2, ENNReal.rpow_one] at h2
  exact h2

/-- **Minkowski/Jensen for the interval integral**: if the jointly measurable family `G v` has `L^p(P)`-norm at most `B`
for a.e. `v ∈ (0,n]`, then `‖ω ↦ ∫_0^n G v ω dv‖_{L^p(P)} ≤ n B`. -/
theorem o_eLpNorm_integral_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P] {n : ℝ} (hn : 0 < n)
    {p : ℝ} (hp : 1 ≤ p) (G : ℝ → Ω → ℝ)
    (hG : AEMeasurable (fun x : Ω × ℝ => G x.2 x.1) (P.prod (volume.restrict (Set.Ioc 0 n)))) {B : ℝ}
    (hB : 0 ≤ B)
    (hGB : ∀ᵐ v ∂(volume.restrict (Set.Ioc 0 n)), eLpNorm (G v) (ENNReal.ofReal p) P ≤ ENNReal.ofReal B) :
    eLpNorm (fun ω => ∫ v in Set.Ioc 0 n, G v ω) (ENNReal.ofReal p) P ≤ ENNReal.ofReal (n * B) := by
  have hp0 : 0 < p := by linarith
  set ν : Measure ℝ := volume.restrict (Set.Ioc 0 n) with hν
  have : IsFiniteMeasure ν := ⟨by simp [hν]⟩
  have hGm : AEStronglyMeasurable (fun x : Ω × ℝ => G x.2 x.1) (P.prod ν) := hG.aestronglyMeasurable
  have hFm : AEStronglyMeasurable (fun ω => ∫ v, G v ω ∂ν) P := hGm.integral_prod_right'
  have hslice : ∀ᵐ ω ∂P, AEStronglyMeasurable (fun v => G v ω) ν := hGm.prodMk_left
  have hνu : ν Set.univ = ENNReal.ofReal n := by simp [hν]
  have hpt : ∀ᵐ ω ∂P, ‖∫ v, G v ω ∂ν‖ₑ ^ p ≤ (∫⁻ v, ‖G v ω‖ₑ ^ p ∂ν) * ν Set.univ ^ (p - 1) := by
    filter_upwards [hslice] with ω hω
    calc ‖∫ v, G v ω ∂ν‖ₑ ^ p ≤ (∫⁻ v, ‖G v ω‖ₑ ∂ν) ^ p :=
          ENNReal.rpow_le_rpow (enorm_integral_le_lintegral_enorm _) hp0.le
      _ ≤ _ := o_lintegral_enorm_rpow_le hω hp
  have hfin : ν Set.univ ^ (p - 1) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by linarith) (measure_ne_top _ _)
  have hswap : ∫⁻ ω, ∫⁻ v, ‖G v ω‖ₑ ^ p ∂ν ∂P = ∫⁻ v, ∫⁻ ω, ‖G v ω‖ₑ ^ p ∂P ∂ν :=
    lintegral_lintegral_swap (f := fun ω v => ‖G v ω‖ₑ ^ p) (hG.enorm.pow_const p)
  have hinner : ∀ᵐ v ∂ν, ∫⁻ ω, ‖G v ω‖ₑ ^ p ∂P ≤ ENNReal.ofReal B ^ p := by
    filter_upwards [hGB] with v hv
    have hm := aestronglyMeasurable_of_eLpNorm_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hv)
    rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top hm,
      ENNReal.toReal_ofReal hp0.le] at hv
    rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' hp0]
    exact ENNReal.rpow_le_rpow hv hp0.le
  have hint : ∫⁻ ω, ‖∫ v, G v ω ∂ν‖ₑ ^ p ∂P ≤ ENNReal.ofReal (n * B) ^ p := by
    calc ∫⁻ ω, ‖∫ v, G v ω ∂ν‖ₑ ^ p ∂P ≤ ∫⁻ ω, (∫⁻ v, ‖G v ω‖ₑ ^ p ∂ν) * ν Set.univ ^ (p - 1) ∂P :=
          lintegral_mono_ae hpt
      _ = (∫⁻ ω, ∫⁻ v, ‖G v ω‖ₑ ^ p ∂ν ∂P) * ν Set.univ ^ (p - 1) := lintegral_mul_const' _ _ hfin
      _ = (∫⁻ v, ∫⁻ ω, ‖G v ω‖ₑ ^ p ∂P ∂ν) * ν Set.univ ^ (p - 1) := by rw [hswap]
      _ ≤ (∫⁻ v, ENNReal.ofReal B ^ p ∂ν) * ν Set.univ ^ (p - 1) := by
          exact mul_le_mul' (lintegral_mono_ae hinner) le_rfl
      _ = ENNReal.ofReal (n * B) ^ p := by
          have hpn : ENNReal.ofReal n ^ p = ENNReal.ofReal n ^ (p - 1) * ENNReal.ofReal n := by
            have := ENNReal.rpow_add (p - 1) 1 (x := ENNReal.ofReal n) (by simp [hn]) ENNReal.ofReal_ne_top
            rw [ENNReal.rpow_one] at this
            rw [← this]; ring_nf
          rw [lintegral_const, hνu, ENNReal.ofReal_mul hn.le, ENNReal.mul_rpow_of_nonneg _ _ hp0.le, hpn]
          ring
  rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top hFm, ENNReal.toReal_ofReal hp0.le]
  unfold eLpNorm'
  calc _ ≤ (ENNReal.ofReal (n * B) ^ p) ^ (1 / p) := ENNReal.rpow_le_rpow hint (by positivity)
    _ = _ := by rw [← ENNReal.rpow_mul]; field_simp; simp

/-- `a e^{-κ a/2} ≤ 2/κ`, hence `(a+T+1) e^{-κ a} ≤ (2/κ + T + 1) e^{-κ a/2}`. -/
theorem o_lin_exp_le {κ T a : ℝ} (hκ : 0 < κ) (hT : 0 ≤ T) (ha : 0 ≤ a) :
    (a + T + 1) * Real.exp (-κ * a) ≤ (2 / κ + T + 1) * Real.exp (-(κ / 2) * a) := by
  have hu0 : 0 < Real.exp (-(κ / 2) * a) := Real.exp_pos _
  have hu1 : Real.exp (-(κ / 2) * a) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hexp : Real.exp (-κ * a) = Real.exp (-(κ / 2) * a) * Real.exp (-(κ / 2) * a) := by
    rw [← Real.exp_add]; ring_nf
  have h1 : a * Real.exp (-(κ / 2) * a) ≤ 2 / κ := by
    have hg : κ / 2 * a + 1 ≤ Real.exp (κ / 2 * a) := Real.add_one_le_exp _
    have hinv : Real.exp (-(κ / 2) * a) * Real.exp (κ / 2 * a) = 1 := by
      rw [← Real.exp_add]; simp
    rw [le_div_iff₀ hκ]
    have : κ / 2 * a ≤ Real.exp (κ / 2 * a) := by linarith
    have h3 := mul_le_mul_of_nonneg_left this hu0.le
    rw [hinv] at h3
    nlinarith
  rw [hexp]
  nlinarith [mul_nonneg hT hu0.le, mul_le_mul_of_nonneg_left hu1 (mul_nonneg hT hu0.le)]

/-- A bound on the `L^q` norm from a bound on the `q`-th moment. -/
theorem o_eLpNorm_of_moment {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] (μ : Measure Ω)
    (f : Ω → E) (hf : AEStronglyMeasurable f μ) {q : ℝ} (hq : 0 < q)
    (hint : Integrable (fun ω => ‖f ω‖ ^ q) μ) {C : ℝ} (hC : ∫ ω, ‖f ω‖ ^ q ∂μ ≤ C) :
    eLpNorm f (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (C ^ (1 / q)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hq).ne' ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hq.le]
  have h1 : ∫⁻ ω, ‖f ω‖ₑ ^ q ∂μ = ENNReal.ofReal (∫ ω, ‖f ω‖ ^ q ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ω => Real.rpow_nonneg (norm_nonneg _) _)]
    refine lintegral_congr fun ω => ?_
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq.le]
  rw [h1]
  have hC0 : 0 ≤ ∫ ω, ‖f ω‖ ^ q ∂μ := integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  rw [ENNReal.ofReal_rpow_of_nonneg hC0 (by positivity)]
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hC0 hC (by positivity))

end HRS.MC.E214O

end
