import HRS.Commutator.Whole.ExternalAuxHLS9

/-!
# The Riesz potential of the fractional derivative and the Fubini pairing (packet X-HLS, part 10)
-/

open MeasureTheory Filter Topology Metric Real Set
open scoped ENNReal NNReal FourierTransform ContDiff

noncomputable section

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ}

lemma cmxHLS_exps {σ p q : ℝ} (hd : 1 ≤ d) (hσ : 0 < σ) (hp : 1 < p) (hpq : p < q)
    (hrel : 1 / q = 1 / p - σ / d) :
    σ * p < d ∧ 1 < q.conjExponent ∧ q.conjExponent < p.conjExponent ∧
      1 / p.conjExponent = 1 / q.conjExponent - σ / d := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hq1 : 1 < q := hp.trans hpq
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hHp := Real.HolderConjugate.conjExponent hp
  have hHq := Real.HolderConjugate.conjExponent hq1
  have e1 := hHp.inv_add_inv_eq_one
  have e2 := hHq.inv_add_inv_eq_one
  have hp'0 : 0 < p.conjExponent := by have := hHp.symm.lt; linarith
  have hq'0 : 0 < q.conjExponent := by have := hHq.symm.lt; linarith
  have hrel' : 1 / p.conjExponent = 1 / q.conjExponent - σ / d := by
    rw [one_div, one_div] at hrel ⊢
    linarith
  refine ⟨?_, hHq.symm.lt, ?_, hrel'⟩
  · have h1 : 0 < 1 / q := by positivity
    have : σ / d < 1 / p := by linarith
    rw [div_lt_div_iff₀ hdpos hp0] at this
    linarith
  · have h1 : 0 < σ / d := by positivity
    have : 1 / p.conjExponent < 1 / q.conjExponent := by linarith
    rwa [one_div_lt_one_div hp'0 hq'0] at this

/-- The Riesz potential `∫ |x-y|^{σ-d} w(y) dy`. -/
def cmxHLS_RP (σ : ℝ) (w : Euc d → ℝ) (x : Euc d) : ℝ := ∫ y : Euc d, ‖x - y‖ ^ (σ - (d : ℝ)) * w y

lemma cmxHLS_RP_measurable (σ : ℝ) {w : Euc d → ℝ} (hw : Measurable w) :
    Measurable (cmxHLS_RP σ w) := by
  have hm : Measurable fun p : Euc d × Euc d => ‖p.1 - p.2‖ ^ (σ - (d : ℝ)) * w p.2 :=
    ((measurable_norm.comp (measurable_fst.sub measurable_snd)).pow_const _).mul
      (hw.comp measurable_snd)
  exact (StronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Euc d)))
    hm.stronglyMeasurable).measurable

lemma cmxHLS_RP_enorm_le (σ : ℝ) (w : Euc d → ℝ) (x : Euc d) :
    ‖cmxHLS_RP σ w x‖ₑ ≤ cmxHLS_I σ (fun y => ((‖w y‖₊ : ℝ≥0) : ℝ≥0∞)) x := by
  unfold cmxHLS_RP cmxHLS_I
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  refine lintegral_congr fun y => ?_
  rw [enorm_mul, Real.enorm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  rfl


lemma cmxHLS_RP_Lq (hd : 1 ≤ d) {σ p q : ℝ} (hσ : 0 < σ) (hp : 1 < p) (hpq : p < q)
    (hrel : 1 / q = 1 / p - σ / d) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : Euc d → ℝ, Measurable w →
      ∫⁻ x, ‖cmxHLS_RP σ w x‖ₑ ^ q ≤ ENNReal.ofReal C * (∫⁻ y, ‖w y‖ₑ ^ p) ^ (q / p) := by
  obtain ⟨C, hC, hK⟩ := cmxHLS_kernel hd hσ hp hpq hrel
  refine ⟨C, hC, fun w hw => ?_⟩
  have hq0 : 0 < q := by linarith
  have hf : Measurable (fun y => ‖w y‖₊) := hw.nnnorm
  refine le_trans ?_ (hK (fun y => ‖w y‖₊) hf)
  exact lintegral_mono fun x => ENNReal.rpow_le_rpow (cmxHLS_RP_enorm_le σ w x) hq0.le

lemma cmxHLS_enorm_ofReal (r : ℝ) : ‖((r : ℝ) : ℂ)‖ₑ = ‖r‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]

lemma cmxHLS_integrable_pair (hd : 1 ≤ d) {σ p q : ℝ} (hσ : 0 < σ) (hp : 1 < p) (hpq : p < q)
    (hrel : 1 / q = 1 / p - σ / d) {w : Euc d → ℝ} (hw : Measurable w)
    (hwp : ∫⁻ y, ‖w y‖ₑ ^ p ≠ ⊤) (R : SchwartzMap (Euc d) ℂ) :
    Integrable (fun z : Euc d × Euc d =>
      ((w z.1 : ℝ) : ℂ) * (((‖z.1 - z.2‖ ^ (σ - (d : ℝ)) : ℝ)) : ℂ) * R z.2) := by
  obtain ⟨-, hq1, hqp, hrel'⟩ := cmxHLS_exps hd hσ hp hpq hrel
  have hHp := Real.HolderConjugate.conjExponent hp
  have hp'0 : 0 < p.conjExponent := by have := hHp.symm.lt; linarith
  obtain ⟨C, hC, hK⟩ := cmxHLS_kernel hd hσ hq1 hqp hrel'
  have hmeas : Measurable fun z : Euc d × Euc d =>
      ((w z.1 : ℝ) : ℂ) * (((‖z.1 - z.2‖ ^ (σ - (d : ℝ)) : ℝ)) : ℂ) * R z.2 := by
    refine Measurable.mul (Measurable.mul ?_ ?_) ?_
    · exact Complex.measurable_ofReal.comp (hw.comp measurable_fst)
    · exact Complex.measurable_ofReal.comp
        ((measurable_norm.comp (measurable_fst.sub measurable_snd)).pow_const _)
    · exact R.continuous.measurable.comp measurable_snd
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have hg : Measurable (fun y : Euc d => ((‖R y‖₊ : ℝ≥0) : ℝ≥0∞)) :=
    R.continuous.nnnorm.measurable.coe_nnreal_ennreal
  have hgq : ∫⁻ y, (‖R y‖₊ : ℝ≥0∞) ^ q.conjExponent ≠ ⊤ := by
    have hq'0 : 0 < q.conjExponent := by linarith
    have h1 : eLpNorm (⇑R) (ENNReal.ofReal q.conjExponent) volume < ⊤ :=
      (R.memLp (ENNReal.ofReal q.conjExponent) volume).eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hq'0) ENNReal.ofReal_ne_top
      R.continuous.aestronglyMeasurable, ENNReal.toReal_ofReal hq'0.le] at h1
    have h2 : (∫⁻ y, ‖R y‖ₑ ^ q.conjExponent) ≠ ⊤ := by
      intro h
      rw [h, ENNReal.top_rpow_of_pos (by positivity)] at h1
      exact lt_irrefl _ h1
    exact h2
  have hIg : ∫⁻ x, cmxHLS_I σ (fun y => ((‖R y‖₊ : ℝ≥0) : ℝ≥0∞)) x ^ p.conjExponent ≠ ⊤ := by
    have := hK (fun y => ‖R y‖₊) R.continuous.nnnorm.measurable
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hgq)) this
  have hIgm := cmxHLS_I_measurable σ hg
  rw [Measure.volume_eq_prod, lintegral_prod _ (by
    refine Measurable.aemeasurable ?_
    exact (hmeas.enorm))]
  have hrw : ∀ x : Euc d, ∫⁻ y : Euc d, ‖((w x : ℝ) : ℂ) * (((‖x - y‖ ^ (σ - (d : ℝ)) : ℝ)) : ℂ) * R y‖ₑ =
      ‖w x‖ₑ * cmxHLS_I σ (fun y => ((‖R y‖₊ : ℝ≥0) : ℝ≥0∞)) x := by
    intro x
    unfold cmxHLS_I cmxHLS_k
    rw [← lintegral_const_mul _ (by
      exact ((measurable_const.sub measurable_id).norm.pow_const _).ennreal_ofReal.mul hg)]
    refine lintegral_congr fun y => ?_
    rw [enorm_mul, enorm_mul, cmxHLS_enorm_ofReal, cmxHLS_enorm_ofReal,
      Real.enorm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), mul_assoc]
    rfl
  simp_rw [hrw]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hHp (f := fun x : Euc d => ‖w x‖ₑ)
    (g := fun x => cmxHLS_I σ (fun y => ((‖R y‖₊ : ℝ≥0) : ℝ≥0∞)) x) hw.enorm.aemeasurable
    hIgm.aemeasurable
  simp only [Pi.mul_apply] at hH
  refine lt_of_le_of_lt hH ?_
  refine ENNReal.mul_lt_top ?_ ?_
  · exact ENNReal.rpow_lt_top_of_nonneg (by have := hHp.pos; positivity) hwp
  · exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hIg


/-- The constant of the Riesz representation. -/
def cmxHLS_c1 (d : ℕ) (σ : ℝ) : ℝ :=
  Real.Gamma (((d : ℝ) - σ) / 2) /
    (π ^ (((d : ℝ) - σ) - (d : ℝ) / 2) * Real.Gamma (σ / 2) * (2 * π) ^ σ)

lemma cmxHLS_c1_pos (d : ℕ) {σ : ℝ} (hσ : 0 < σ) (hσd : σ < d) : 0 < cmxHLS_c1 d σ := by
  unfold cmxHLS_c1
  have h1 := Real.Gamma_pos_of_pos (by linarith : 0 < ((d : ℝ) - σ) / 2)
  have h2 := Real.Gamma_pos_of_pos (by linarith : 0 < σ / 2)
  positivity

theorem cmxHLS_pairing (hd : 1 ≤ d) {σ p q : ℝ} (hσ : 0 < σ) (hσd : σ < d) (hp : 1 < p)
    (hpq : p < q) (hrel : 1 / q = 1 / p - σ / d) {w : Euc d → ℝ} (hw : Measurable w)
    (hwp : ∫⁻ y, ‖w y‖ₑ ^ p ≠ ⊤) (F : SchwartzMap (Euc d) ℂ) (j : ℤ) :
    ∫ x : Euc d, ((w x : ℝ) : ℂ) * cmxHLS_piece (-σ) (⇑F) j x =
      ∫ y : Euc d, ((cmxHLS_c1 d σ * cmxHLS_RP σ w y : ℝ) : ℂ) * cmxHLS_piece 0 (⇑F) j y := by
  set R : SchwartzMap (Euc d) ℂ := cmxHLS_pieceS 0 F j with hR
  have hRc : (⇑R : Euc d → ℂ) = cmxHLS_piece 0 (⇑F) j := cmxHLS_pieceS_coe 0 F j
  have hΓ : 0 < Real.Gamma (((d : ℝ) - σ) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hc0 : 0 < π ^ (((d : ℝ) - σ) - (d : ℝ) / 2) * Real.Gamma (σ / 2) * (2 * π) ^ σ := by
    have := Real.Gamma_pos_of_pos (by linarith : 0 < σ / 2); positivity
  have hQ : ∀ x : Euc d, cmxHLS_piece (-σ) (⇑F) j x =
      ((cmxHLS_c1 d σ : ℝ) : ℂ) * ∫ y : Euc d, (((‖x - y‖ ^ (σ - (d : ℝ)) : ℝ)) : ℂ) * R y := by
    intro x
    have h1 := cmxHLS_repr_piece hd hσ hσd F j x
    have h2 : ∫ z : Euc d, ((‖z‖ ^ (σ - (d : ℝ)) : ℝ) : ℂ) * cmxHLS_piece 0 (⇑F) j (x - z) =
        ∫ y : Euc d, (((‖x - y‖ ^ (σ - (d : ℝ)) : ℝ)) : ℂ) * R y := by
      rw [← integral_sub_left_eq_self (fun y : Euc d => (((‖x - y‖ ^ (σ - (d : ℝ)) : ℝ)) : ℂ) * R y)
        volume x]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [sub_sub_cancel, hRc]
    rw [h2] at h1
    have hne : (((π ^ (((d : ℝ) - σ) - (d : ℝ) / 2) * Real.Gamma (σ / 2) * (2 * π) ^ σ : ℝ)) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 hc0.ne'
    unfold cmxHLS_c1
    rw [Complex.ofReal_div, div_mul_eq_mul_div, eq_div_iff hne]
    rw [mul_comm, ← h1]
  have hint := cmxHLS_integrable_pair hd hσ hp hpq hrel hw hwp R
  have hswap := integral_integral_swap (μ := (volume : Measure (Euc d))) (ν := (volume : Measure (Euc d)))
    (f := fun x y : Euc d => ((w x : ℝ) : ℂ) * (((‖x - y‖ ^ (σ - (d : ℝ)) : ℝ)) : ℂ) * R y) hint
  calc ∫ x : Euc d, ((w x : ℝ) : ℂ) * cmxHLS_piece (-σ) (⇑F) j x
      = ∫ x : Euc d, ((cmxHLS_c1 d σ : ℝ) : ℂ) *
          ∫ y : Euc d, ((w x : ℝ) : ℂ) * (((‖x - y‖ ^ (σ - (d : ℝ)) : ℝ)) : ℂ) * R y := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        dsimp only
        have e2 : ∫ y : Euc d, ((w x : ℝ) : ℂ) * (((‖x - y‖ ^ (σ - (d : ℝ)) : ℝ)) : ℂ) * R y =
            ((w x : ℝ) : ℂ) * ∫ y : Euc d, (((‖x - y‖ ^ (σ - (d : ℝ)) : ℝ)) : ℂ) * R y := by
          rw [← integral_const_mul]
          exact integral_congr_ae (Eventually.of_forall fun y => by ring)
        rw [hQ x, e2]; ring
    _ = ((cmxHLS_c1 d σ : ℝ) : ℂ) * ∫ x : Euc d, ∫ y : Euc d,
          ((w x : ℝ) : ℂ) * (((‖x - y‖ ^ (σ - (d : ℝ)) : ℝ)) : ℂ) * R y := by
        rw [integral_const_mul]
    _ = ((cmxHLS_c1 d σ : ℝ) : ℂ) * ∫ y : Euc d, ∫ x : Euc d,
          ((w x : ℝ) : ℂ) * (((‖x - y‖ ^ (σ - (d : ℝ)) : ℝ)) : ℂ) * R y := by rw [hswap]
    _ = ∫ y : Euc d, ((cmxHLS_c1 d σ * cmxHLS_RP σ w y : ℝ) : ℂ) * cmxHLS_piece 0 (⇑F) j y := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        dsimp only
        have : ∫ x : Euc d, ((w x : ℝ) : ℂ) * (((‖x - y‖ ^ (σ - (d : ℝ)) : ℝ)) : ℂ) * R y =
            ((cmxHLS_RP σ w y : ℝ) : ℂ) * R y := by
          unfold cmxHLS_RP
          rw [integral_mul_const, ← integral_complex_ofReal]
          congr 1
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          dsimp only
          rw [norm_sub_rev]
          push_cast
          ring
        rw [this, hRc]
        push_cast
        ring

end HRS.Commutator.Whole
