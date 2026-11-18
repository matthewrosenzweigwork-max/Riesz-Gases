import HRS.Commutator.Torus.TSAMPAux19

/-!
# T-SAMP helpers, part 20: the abstract sampling inequality (near/far splitting)
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

lemma tsamp_aux_pow (N C : ℝ≥0∞) {p : ℝ} (hp : 0 < p) : (N * C ^ (1 / p)) ^ p = N ^ p * C := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne',
    ENNReal.rpow_one]

theorem tsamp_sampling_abstract {m : ℕ} (hm : 1 ≤ m) {p q : ℝ} (hpq : p.HolderConjugate q)
    {g Θ kn u : Torus d → ℝ≥0∞} (hg : Measurable g) (hΘ : Measurable Θ) (hkn : Measurable kn)
    (hΘ1 : ∫⁻ z, Θ z ≠ ⊤) {r : ℝ} (hsupp : ∀ z, kn z ≠ 0 → KernelGrad.tdist z 0 < r)
    (hu : ∀ x x' : Torus d, KernelGrad.tdist x x' ≤ d / m →
      u x ≤ (∫⁻ y, Θ (x' - y) * g y) + ∫⁻ y, kn (x - y) * g y) :
    ∑ j : Fin d → Fin m, (⨆ x ∈ cellT m j, u x) ^ p ≤
      (m : ℝ≥0∞) ^ d * (2 ^ (p - 1) *
        ((∫⁻ z, Θ z) ^ p + ((∫⁻ z, kn z ^ q) ^ (1 / q)) ^ p *
          volume {z : Torus d | KernelGrad.tdist z 0 ≤ d / m + r}) * ∫⁻ y, g y ^ p) := by
  have hp1 : 1 < p := hpq.lt
  have hp0 : 0 < p := by linarith
  set R : ℝ := d / m + r with hR
  set N : ℝ≥0∞ := (∫⁻ z, kn z ^ q) ^ (1 / q) with hN
  set far : Torus d → ℝ≥0∞ := fun x' => ∫⁻ y, Θ (x' - y) * g y with hfar
  set C : Torus d → ℝ≥0∞ := fun x' => ∫⁻ y in tsampBall R x', g y ^ p with hC
  have hfarm : Measurable far := by
    have : Measurable (fun q : Torus d × Torus d => Θ (q.1 - q.2) * g q.2) :=
      (hΘ.comp (measurable_fst.sub measurable_snd)).mul (hg.comp measurable_snd)
    exact this.lintegral_prod_right'
  have hCm : Measurable C := by
    have hset : MeasurableSet {q : Torus d × Torus d | KernelGrad.tdist q.1 q.2 ≤ R} :=
      measurableSet_le (by
        have : Continuous fun q : Torus d × Torus d => KernelGrad.tdist q.1 q.2 := by
          simp_rw [CoercAux.tdist_eq_sqrt]; fun_prop
        exact this.measurable) measurable_const
    have hF : Measurable (fun q : Torus d × Torus d =>
        {q : Torus d × Torus d | KernelGrad.tdist q.1 q.2 ≤ R}.indicator (fun q => g q.2 ^ p) q) :=
      ((hg.comp measurable_snd).pow_const p).indicator hset
    have e : C = fun x' => ∫⁻ y, {q : Torus d × Torus d | KernelGrad.tdist q.1 q.2 ≤ R}.indicator
        (fun q => g q.2 ^ p) (x', y) := by
      funext x'
      have hBx : MeasurableSet (tsampBall (d := d) R x') := measurableSet_le (by
        have : Continuous fun y : Torus d => KernelGrad.tdist x' y := by
          simp_rw [CoercAux.tdist_eq_sqrt]; fun_prop
        exact this.measurable) measurable_const
      simp only [hC]
      rw [← lintegral_indicator hBx]
      refine lintegral_congr fun y => ?_
      by_cases hh : KernelGrad.tdist x' y ≤ R <;> simp [Set.indicator, tsampBall, hh]
    rw [e]
    exact hF.lintegral_prod_right'
  have hΦ : ∀ j : Fin d → Fin m, ∀ x' ∈ cellT m j, ⨆ x ∈ cellT m j, u x ≤ far x' + N * C x' ^ (1 / p) := by
    intro j x' hx'
    refine iSup₂_le fun x hx => ?_
    have hxx := tsamp_cell_diam hm hx hx'
    refine (hu x x' hxx).trans (add_le_add le_rfl ?_)
    exact tsamp_near_holder hpq hkn hg hsupp (by rw [hR]; linarith)
  have h1 := tsamp_sum_sup_le hm (u := u) (Φ := fun x' => far x' + N * C x' ^ (1 / p)) hp0 hΦ
  refine h1.trans (mul_le_mul' le_rfl ?_)
  -- the `p`-th power
  have hpt : ∀ x', (far x' + N * C x' ^ (1 / p)) ^ p ≤ 2 ^ (p - 1) * (far x' ^ p + N ^ p * C x') := by
    intro x'
    refine (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp1.le).trans (mul_le_mul' le_rfl ?_)
    exact add_le_add le_rfl (le_of_eq (tsamp_aux_pow N (C x') hp0))
  calc ∫⁻ x', (far x' + N * C x' ^ (1 / p)) ^ p
      ≤ ∫⁻ x', 2 ^ (p - 1) * (far x' ^ p + N ^ p * C x') := lintegral_mono hpt
    _ = 2 ^ (p - 1) * ((∫⁻ x', far x' ^ p) + N ^ p * ∫⁻ x', C x') := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_add_left (hfarm.pow_const p),
          lintegral_const_mul _ hCm]
    _ ≤ 2 ^ (p - 1) * ((∫⁻ z, Θ z) ^ p * (∫⁻ y, g y ^ p) +
          N ^ p * (volume {z : Torus d | KernelGrad.tdist z 0 ≤ R} * ∫⁻ y, g y ^ p)) := by
        refine mul_le_mul' le_rfl (add_le_add ?_ (mul_le_mul' le_rfl (le_of_eq ?_)))
        · exact tsamp_young_enn hΘ hg hp1 hΘ1
        · exact tsamp_ball_lintegral R (hg.pow_const p)
    _ = 2 ^ (p - 1) * ((∫⁻ z, Θ z) ^ p + N ^ p * volume {z : Torus d | KernelGrad.tdist z 0 ≤ R}) *
          ∫⁻ y, g y ^ p := by ring

end HRS.Commutator.TorusNote
