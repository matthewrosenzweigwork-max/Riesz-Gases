import HRS.Commutator.Torus.TSAMPAux4

/-!
# T-SAMP helpers, part 5: convolution calculus on the torus, reduction of the transport data
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

/-- `K ⋆ f`. -/
def tsampConv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (K : Torus d → ℝ)
    (f : Torus d → E) (x : Torus d) : E := ∫ y, K (x - y) • f y

lemma tsamp_PleqT_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (η : ℝ) (f : Torus d → E) :
    PleqT η f = tsampConv (perio (Whole.psiL (d := d) η⁻¹)) f := rfl

lemma tsamp_conv_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (hd : 1 ≤ d)
    {K : Torus d → ℝ} (hKm : Measurable K) {M : ℝ} (hKb : ∀ x : Torus d, x ≠ 0 → |K x| ≤ M)
    {f : Torus d → E} (hf : Integrable f) (x : Torus d) :
    Integrable (fun y => K (x - y) • f y) := by
  have hm : AEStronglyMeasurable (fun y => K (x - y) • f y) volume :=
    ((hKm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable).smul hf.aestronglyMeasurable
  refine (hf.norm.const_mul M).mono' hm ?_
  filter_upwards [text_ae_ne hd x] with y hy
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hKb _ (sub_ne_zero.2 (Ne.symm hy))) (norm_nonneg _)

lemma tsamp_conv_apply {K : Torus d → ℝ} {f : Torus d → Euc d} {x : Torus d}
    (hint : Integrable (fun y => K (x - y) • f y)) (j : Fin d) :
    (tsampConv K f x) j = ∫ y, K (x - y) * f y j := by
  unfold tsampConv
  have := (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).integral_comp_comm hint
  simpa using this.symm

lemma tsamp_aesm_conv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {K : Torus d → ℝ} {f : Torus d → E} (hK : Measurable K) (hf : Measurable f) :
    AEStronglyMeasurable (tsampConv K f) volume := by
  have h : StronglyMeasurable (fun q : Torus d × Torus d => K (q.1 - q.2) • f q.2) :=
    ((hK.comp (measurable_fst.sub measurable_snd)).smul (hf.comp measurable_snd)).stronglyMeasurable
  exact (h.integral_prod_right' (ν := volume)).aestronglyMeasurable

lemma tsamp_conv_eLpNorm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {K : Torus d → ℝ} {f : Torus d → E} (hK : Integrable K) (hKm : Measurable K)
    (hf : Measurable f) {p : ℝ} (hp : 1 < p) :
    eLpNorm (tsampConv K f) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (∫ y, ‖K y‖) * eLpNorm f (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := by linarith
  have hP0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hPt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPt (tsamp_aesm_conv hKm hf),
    eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPt hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le]
  have hκ : ∫⁻ y, ‖K y‖ₑ ≠ ⊤ := hK.2.ne
  have hpt : ∀ x, ‖tsampConv K f x‖ₑ ≤ ∫⁻ y, ‖K (x - y)‖ₑ * ‖f y‖ₑ := by
    intro x
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    simp_rw [enorm_smul]
  have h1 : ∫⁻ x, ‖tsampConv K f x‖ₑ ^ p ≤ ∫⁻ x, (∫⁻ y, ‖K (x - y)‖ₑ * ‖f y‖ₑ) ^ p :=
    lintegral_mono fun x => ENNReal.rpow_le_rpow (hpt x) hp0.le
  have h2 := tsamp_young_enn (k := fun y => ‖K y‖ₑ) (f := fun y => ‖f y‖ₑ) hKm.enorm hf.enorm hp hκ
  have e : ∫⁻ y, ‖K y‖ₑ = ENNReal.ofReal (∫ y, ‖K y‖) := by
    rw [ofReal_integral_norm_eq_lintegral_enorm hK]
  calc (∫⁻ x, ‖tsampConv K f x‖ₑ ^ p) ^ (1 / p)
      ≤ ((∫⁻ y, ‖K y‖ₑ) ^ p * ∫⁻ x, ‖f x‖ₑ ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (h1.trans h2) (by positivity)
    _ = ENNReal.ofReal (∫ y, ‖K y‖) * (∫⁻ x, ‖f x‖ₑ ^ p) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hp0.ne', ENNReal.rpow_one, e]

/-! ### Reduction of the transport data to a measurable representative -/

lemma tsamp_not_aesm_fcoef {g : Torus d → ℝ} (hg : ¬ AEStronglyMeasurable g volume) (k : Lattice d) :
    Torus.fcoef g k = 0 := by
  unfold Torus.fcoef
  apply integral_undef
  intro hint
  apply hg
  have h1 : AEStronglyMeasurable (fun x : Torus d => Torus.mode k x *
      (Torus.mode (-k) x * ((g x : ℝ) : ℂ))) volume :=
    (Torus.continuous_mode k).aestronglyMeasurable.mul hint.1
  have h2 : AEStronglyMeasurable (fun x : Torus d => (Torus.mode k x *
      (Torus.mode (-k) x * ((g x : ℝ) : ℂ))).re) volume :=
    Complex.continuous_re.comp_aestronglyMeasurable h1
  refine h2.congr (Eventually.of_forall fun x => ?_)
  beta_reduce
  have := Torus.mode_neg_lattice k x
  rw [← mul_assoc, mul_comm (Torus.mode k x), this, one_mul]
  simp

lemma tsamp_reduce_w {a : ℝ} (ha : 0 < a) {v w : Torus d → Euc d} (h : IsFracDeriv a v w) :
    ∃ w' : Torus d → Euc d, Measurable w' ∧ (∀ᵐ x ∂(volume : Measure (Torus d)), ‖w' x‖ ≤ ‖w x‖) ∧
      IsFracDeriv a v w' := by
  classical
  set c : Fin d → Torus d → ℝ := fun j =>
    if hj : AEStronglyMeasurable (fun x => w x j) volume then hj.mk _ else fun _ => 0 with hc
  have hcm : ∀ j, Measurable (c j) := by
    intro j
    simp only [hc]
    split_ifs with hj
    · exact hj.stronglyMeasurable_mk.measurable
    · exact measurable_const
  refine ⟨fun x => WithLp.toLp 2 (fun j => c j x), ?_, ?_, ?_⟩
  · exact (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp (measurable_pi_iff.2 hcm)
  · have hae : ∀ᵐ x ∂(volume : Measure (Torus d)), ∀ j, |c j x| ≤ |w x j| := by
      rw [ae_all_iff]
      intro j
      by_cases hj : AEStronglyMeasurable (fun x => w x j) volume
      · filter_upwards [hj.ae_eq_mk] with x hx
        simp only [hc, hj, dif_pos]
        rw [hx]
      · refine Eventually.of_forall fun x => ?_
        simp only [hc, hj, dif_neg, not_false_eq_true, abs_zero]
        exact abs_nonneg _
    filter_upwards [hae] with x hx
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => ?_)
    simp only [Real.norm_eq_abs, sq_abs]
    exact sq_le_sq.2 (hx j)
  · intro j k
    by_cases hj : AEStronglyMeasurable (fun x => w x j) volume
    · have hcj : c j = hj.mk _ := by simp only [hc, hj, dif_pos]
      have : Torus.fcoef (fun x => (WithLp.toLp 2 (fun j => c j x) : Euc d) j) k =
          Torus.fcoef (fun x => w x j) k := by
        unfold Torus.fcoef
        refine integral_congr_ae ?_
        filter_upwards [hj.ae_eq_mk] with x hx
        show Torus.mode (-k) x * ((c j x : ℝ) : ℂ) = Torus.mode (-k) x * ((w x j : ℝ) : ℂ)
        rw [hcj, hx]
      rw [this]
      exact h j k
    · have hcj : c j = fun _ => 0 := by simp only [hc, hj, dif_neg, not_false_eq_true]
      have h0 := h j k
      rw [tsamp_not_aesm_fcoef hj k] at h0
      have : Torus.fcoef (fun x => (WithLp.toLp 2 (fun j => c j x) : Euc d) j) k = 0 := by
        unfold Torus.fcoef
        show ∫ x, Torus.mode (-k) x * ((c j x : ℝ) : ℂ) = 0
        rw [hcj]; simp
      rw [this]
      exact h0

end HRS.Commutator.TorusNote
