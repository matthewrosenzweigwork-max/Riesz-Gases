import HRS.MS.CzHlsAux1

/-!
# S.A.16 (SA16Q), E6 part 7: Hardy-Littlewood-Sobolev for convolution against a pointwise-bounded kernel

`sa16q_hls_conv`: if `|k y| ≤ c |y|^{σ-d}` for `y ≠ 0` and `v x = ∫ k y f(x-y) dy`, then
`‖v‖_p ≤ C c ‖f‖_q` (`1 < q < p`, `1/p = 1/q - σ/d`, `σ > 0`, `C` independent of `c, k, f, v`);
`sa16q_exps`: the exponent `q` with `1/q = 1/p + σ/d`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA HRS.CZ.Hls HRS.Commutator.Whole

section Hls
variable {d : ℕ}

theorem sa16q_hls_conv (hd : 1 ≤ d) {σ p q : ℝ} (hσ : 0 < σ) (hq : 1 < q) (hqp : q < p)
    (hrel : 1 / p = 1 / q - σ / d) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 ≤ c → ∀ (k f v : Euc d → ℝ), AEStronglyMeasurable f volume →
      AEStronglyMeasurable v volume → (∀ y : Euc d, y ≠ 0 → |k y| ≤ c * ‖y‖ ^ (σ - (d : ℝ))) →
      (∀ x, v x = ∫ y, k y * f (x - y)) →
      eLpNorm v (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * c) * eLpNorm f (ENNReal.ofReal q) volume := by
  obtain ⟨C, hC, hK⟩ := riesz_pot_Lp_of_le hd hσ hq hqp hrel
  refine ⟨C, hC, fun c hc k f v hf hv hk hvk => ?_⟩
  set u : Euc d → ℝ := fun y => c * f y with hu
  have hum : AEStronglyMeasurable u volume := hf.const_mul c
  have hle : ∀ᵐ x ∂(volume : Measure (Euc d)), ‖v x‖ₑ ≤ cmxHLS_I σ (fun y => ‖u y‖ₑ) x := by
    refine Eventually.of_forall fun x => ?_
    rw [hlsg_pot_eq_z, hvk x]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    refine lintegral_mono_ae ?_
    filter_upwards [HRS.Commutator.Whole.ae_ne_zero_euc hd] with y hy
    rw [enorm_mul]
    have h1 : ‖k y‖ₑ ≤ ENNReal.ofReal c * ENNReal.ofReal (‖y‖ ^ (σ - (d : ℝ))) := by
      rw [← ENNReal.ofReal_mul hc, Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (hk y hy)
    have h2 : ‖u (x - y)‖ₑ = ENNReal.ofReal c * ‖f (x - y)‖ₑ := by
      simp only [hu]
      rw [enorm_mul, Real.enorm_eq_ofReal hc]
    rw [h2]
    calc ‖k y‖ₑ * ‖f (x - y)‖ₑ
        ≤ ENNReal.ofReal c * ENNReal.ofReal (‖y‖ ^ (σ - (d : ℝ))) * ‖f (x - y)‖ₑ := by gcongr
      _ = _ := by ring
  have hmain := hK u v hum hv hle
  have hnorm : eLpNorm u (ENNReal.ofReal q) volume = ENNReal.ofReal c * eLpNorm f (ENNReal.ofReal q) volume := by
    have : u = c • f := by funext y; simp [hu]
    rw [this, eLpNorm_const_smul, Real.enorm_eq_ofReal hc]
  rw [hnorm] at hmain
  calc eLpNorm v (ENNReal.ofReal p) volume
      ≤ ENNReal.ofReal C * (ENNReal.ofReal c * eLpNorm f (ENNReal.ofReal q) volume) := hmain
    _ = ENNReal.ofReal (C * c) * eLpNorm f (ENNReal.ofReal q) volume := by
        rw [ENNReal.ofReal_mul hC.le, mul_assoc]

/-- the HLS exponent -/
lemma sa16q_exps (hd : 1 ≤ d) {p σ : ℝ} (hp : 0 < p) (hσ : 0 < σ) (hlt : 1 / p + σ / d < 1) :
    ∃ q : ℝ, 1 < q ∧ q < p ∧ 1 / p = 1 / q - σ / d ∧ 1 / q = 1 / p + σ / d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hpos : 0 < 1 / p + σ / d := by positivity
  have e : 1 / (1 / p + σ / d)⁻¹ = 1 / p + σ / d := by simp
  refine ⟨(1 / p + σ / d)⁻¹, ?_, ?_, ?_, e⟩
  · rw [lt_inv_comm₀ one_pos hpos, inv_one]; exact hlt
  · rw [inv_lt_comm₀ hpos hp]
    have h1 : 0 < σ / d := by positivity
    have h2 : 1 / p = p⁻¹ := one_div p
    linarith
  · rw [e]; ring

end Hls

end HRS.Whole.AppendixA.Phase2SA16Q
