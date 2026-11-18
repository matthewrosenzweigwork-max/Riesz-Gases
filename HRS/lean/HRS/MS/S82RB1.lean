import HRS.MS.S82P2Sum3
import HRS.MS.WlEnsAux2

/-!
# S8.2 R01B (S82R), part 1: the weak potential of a `CalibratedReferenceData`
Row bounds for `q`, the `EWeakKernel`, the one-body field, and the identification of `referenceLaw`
with the pinned weak ensemble `pinnedLaw` (Wu's resampling framework).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82R
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ} {a beta C0 : ℝ} {rho q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}

lemma s82r_isProb (hρ : HRS.Whole.IsProbDensity rho) :
    IsProbabilityMeasure (HRS.Whole.withDensityReal rho) :=
  HRS.Whole.Q34.isProbabilityMeasure_nu hρ

/-- Row integrability and mass bound for `q`. -/
lemma s82r_row_int (hd : 2 ≤ d) (hq : ShortRangePole d q) {G c : ℝ} (hG : 0 < G)
    (hρ : HRS.Whole.IsProbDensity rho) (hρG : HRS.Whole.HasR2GaussianUpper G c rho) (x : Euc d) :
    Integrable (fun y => q (x - y)) (HRS.Whole.withDensityReal rho) := by
  have := HRS.MS.S82P2.s82p2_q_integrable hd hq G c hG hρG.1 rho hρ hρG x
  refine this.congr (ae_of_all _ fun y => ?_)
  show q (y - x) = q (x - y)
  rw [← hq.even (x - y), neg_sub]

lemma s82r_row_le (hbeta : 0 < beta) (hD : CalibratedReferenceData d a beta rho q h C0) (x : Euc d) :
    HRS.Whole.convMeasure q (HRS.Whole.withDensityReal rho) x ≤ 1 / (1000 * beta) := by
  have h1 := hD.small_row x
  rw [le_div_iff₀ (by positivity)]
  nlinarith

lemma s82r_conv_nonneg (hq : ShortRangePole d q) (μ : Measure (Euc d)) (x : Euc d) :
    0 ≤ HRS.Whole.convMeasure q μ x :=
  integral_nonneg fun y => hq.nonneg _

/-- The weak kernel `(x, y) ↦ q (x - y)`. -/
lemma s82r_weakKernel (hd : 2 ≤ d) (hbeta : 0 < beta) (hD : CalibratedReferenceData d a beta rho q h C0)
    {G c : ℝ} (hG : 0 < G) (hρ : HRS.Whole.IsProbDensity rho)
    (hρG : HRS.Whole.HasR2GaussianUpper G c rho) :
    HRS.MS.Wr.EWeakKernel (HRS.Whole.withDensityReal rho) (1 / (1000 * beta))
      (fun x y : Euc d => q (x - y)) := by
  have hq := hD.short
  refine ⟨?_, fun x y => ?_, fun x y => hq.nonneg _, fun x => ?_⟩
  · exact hq.measurable.comp (measurable_fst.sub measurable_snd)
  · rw [← hq.even (x - y), neg_sub]
  · have hi := s82r_row_int hd hq hG hρ hρG x
    have e := ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun y => hq.nonneg _)
    rw [← e]
    exact ENNReal.ofReal_le_ofReal (s82r_row_le hbeta hD x)

/-- The one-body field `u_N = beta q*mu + h_N`. -/
def s82r_phi (q : Euc d → ℝ) (h : ℕ → Euc d → ℝ) (mu : Measure (Euc d)) (beta : ℝ) (N : ℕ)
    (x : Euc d) : ℝ :=
  beta * HRS.Whole.convMeasure q mu x + h N x

lemma s82r_isField (hd : 2 ≤ d) (hbeta : 0 < beta) (hD : CalibratedReferenceData d a beta rho q h C0)
    {G c : ℝ} (hG : 0 < G) (hρ : HRS.Whole.IsProbDensity rho)
    (hρG : HRS.Whole.HasR2GaussianUpper G c rho) {N : ℕ} (hN : 2 ≤ N) :
    haveI := s82r_isProb hρ
    HRS.External.IsField (HRS.Whole.withDensityReal rho)
      (s82r_phi q h (HRS.Whole.withDensityReal rho) beta N) (1 + 1 / 1000) 1 := by
  haveI := s82r_isProb hρ
  have hK := s82r_weakKernel hd hbeta hD hG hρ hρG
  have hconvm : Measurable (HRS.Whole.convMeasure q (HRS.Whole.withDensityReal rho)) :=
    hK.wr1_measurable_rowInt
  have hm : Measurable (s82r_phi q h (HRS.Whole.withDensityReal rho) beta N) :=
    (hconvm.const_mul beta).add (hD.hmeas N)
  have hb1 : ∀ x, |h N x| ≤ 1 := hD.hsmall N hN
  have hr : ∀ x, 0 ≤ beta * HRS.Whole.convMeasure q (HRS.Whole.withDensityReal rho) x :=
    fun x => mul_nonneg hbeta.le (s82r_conv_nonneg hD.short _ x)
  have hr1 := hD.small_row
  have hbd : ∀ x, |s82r_phi q h (HRS.Whole.withDensityReal rho) beta N x| ≤ 1 + 1 / 1000 := by
    intro x
    unfold s82r_phi
    have h1 := abs_le.1 (hb1 x)
    rw [abs_le]
    have := hr x
    have := hr1 x
    constructor <;> linarith [h1.1, h1.2]
  have hint : Integrable (s82r_phi q h (HRS.Whole.withDensityReal rho) beta N)
      (HRS.Whole.withDensityReal rho) :=
    Integrable.of_bound hm.aestronglyMeasurable (1 + 1 / 1000)
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hbd x)
  refine ⟨hm, fun x => ?_, hint, ?_⟩
  · have := (abs_le.1 (hbd x)).2
    linarith
  · have hlow : ∀ x, -1 ≤ s82r_phi q h (HRS.Whole.withDensityReal rho) beta N x := by
      intro x
      unfold s82r_phi
      have := hr x
      have := (abs_le.1 (hb1 x)).1
      linarith
    have : ∫ x, (-1 : ℝ) ∂(HRS.Whole.withDensityReal rho) ≤
        ∫ x, s82r_phi q h (HRS.Whole.withDensityReal rho) beta N x ∂(HRS.Whole.withDensityReal rho) :=
      integral_mono (integrable_const _) hint hlow
    simpa using this


/-- The weak potential of the calibrated reference. -/
def s82r_pot (hd : 2 ≤ d) (hbeta : 0 < beta) (hD : CalibratedReferenceData d a beta rho q h C0)
    {G c : ℝ} (hG : 0 < G) (hρ : HRS.Whole.IsProbDensity rho)
    (hρG : HRS.Whole.HasR2GaussianUpper G c rho) {N : ℕ} (hN : 2 ≤ N) :
    haveI := s82r_isProb hρ
    HRS.External.WeakPotential (HRS.Whole.withDensityReal rho) :=
  haveI := s82r_isProb hρ
  HRS.MS.Wl.wlPot (s82r_weakKernel hd hbeta hD hG hρ hρG) (by positivity)
    (s82r_isField hd hbeta hD hG hρ hρG hN)

open HRS.External in
/-- `referenceLaw` is the pinned weak ensemble. -/
lemma s82r_referenceLaw_eq (hd : 2 ≤ d) (hbeta : 0 < beta)
    (hD : CalibratedReferenceData d a beta rho q h C0)
    {G c : ℝ} (hG : 0 < G) (hρ : HRS.Whole.IsProbDensity rho)
    (hρG : HRS.Whole.HasR2GaussianUpper G c rho) {N : ℕ} (hN : 2 ≤ N) {p n : ℕ}
    (pins : Fin p → Euc d) :
    haveI := s82r_isProb hρ
    referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins =
      pinnedLaw (s82r_pot hd hbeta hD hG hρ hρG hN) (beta / N) n pins := by
  haveI := s82r_isProb hρ
  set μ := HRS.Whole.withDensityReal rho with hμ
  set V := s82r_pot hd hbeta hD hG hρ hρG hN with hV
  have hlam : 0 ≤ beta / (N : ℝ) := div_nonneg hbeta.le (Nat.cast_nonneg N)
  have hψ := isField_pinField V hlam pins
  have hVφ : V.φ = s82r_phi q h μ beta N := rfl
  have hVq : ∀ x y, V.q x y = q (x - y) := fun x y => rfl
  set P : Measure (EucConfig d n) := Measure.pi fun _ : Fin n => μ with hP
  -- the weights agree
  have hE : ∀ y : EucConfig d n, referenceExponent q h μ beta N pins y =
      ∑ i, pinField V (beta / N) pins (y i) - (beta / N) * HRS.External.pairEnergy V y := by
    intro y
    unfold referenceExponent pinField HRS.External.pairEnergy HRS.MS.Phase2S82.pairSum
    simp only [hVφ, hVq, s82r_phi]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hW : ∀ y : EucConfig d n, fieldWeight V (pinField V (beta / N) pins) (beta / N) y =
      ENNReal.ofReal (Real.exp (referenceExponent q h μ beta N pins y)) := by
    intro y
    unfold fieldWeight
    rw [hE y]
  have hEm : Measurable (referenceExponent q h μ beta N pins (n := n)) := by
    have : referenceExponent q h μ beta N pins (n := n) = fun y =>
        ∑ i, pinField V (beta / N) pins (y i) - (beta / N) * HRS.External.pairEnergy V y := funext hE
    rw [this]
    exact (Finset.measurable_sum _ fun i _ => hψ.measurable.comp (measurable_pi_apply i)).sub
      ((HRS.External.measurable_pairEnergy V).const_mul _)
  have hZfin := fieldNorm_lt_top (V := V) hψ hlam n
  have hint : Integrable (fun y => Real.exp (referenceExponent q h μ beta N pins y)) P := by
    refine ⟨(Real.measurable_exp.comp hEm).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => (Real.exp_pos _).le)]
    have : ∫⁻ y, ENNReal.ofReal (Real.exp (referenceExponent q h μ beta N pins y)) ∂P =
        fieldNorm V (pinField V (beta / N) pins) (beta / N) n := by
      unfold fieldNorm
      exact lintegral_congr fun y => (hW y).symm
    rw [this]; exact hZfin
  have hZ : ENNReal.ofReal (∫ y, Real.exp (referenceExponent q h μ beta N pins y) ∂P) =
      fieldNorm V (pinField V (beta / N) pins) (beta / N) n := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y => (Real.exp_pos _).le)]
    unfold fieldNorm
    exact lintegral_congr fun y => (hW y).symm
  unfold referenceLaw exponentialTilt
  rw [hZ]
  unfold pinnedLaw fieldLaw fieldDensity
  have hfm : Measurable (fun y => ENNReal.ofReal (Real.exp (referenceExponent q h μ beta N pins y))) :=
    (Real.measurable_exp.comp hEm).ennreal_ofReal
  have hfw : (fun y : EucConfig d n => fieldWeight V (pinField V (beta / N) pins) (beta / N) y *
      (fieldNorm V (pinField V (beta / N) pins) (beta / N) n)⁻¹) =
      (fieldNorm V (pinField V (beta / N) pins) (beta / N) n)⁻¹ •
        fun y : EucConfig d n => ENNReal.ofReal (Real.exp (referenceExponent q h μ beta N pins y)) := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, hW y]
    ring
  rw [hfw, withDensity_smul _ hfm]

end HRS.MS.S82R

end
