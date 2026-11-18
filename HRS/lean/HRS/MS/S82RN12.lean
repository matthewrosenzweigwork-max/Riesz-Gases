import HRS.MS.S82RB1
import HRS.MS.S82RN11

/-!
# S8.2 R02 (S82R), N12: the weak potential of a `WeakReferenceSetup` field (no `hsmall`)
A general identification of `referenceLaw` with `pinnedLaw` for any weak potential with the right field and kernel,
and the construction of such a potential with explicit field bounds `(1/1000 + t, t)` for `|h N| <= t`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82R
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ} {beta : ℝ} {rho q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}

open HRS.External in
/-- `referenceLaw` is the pinned weak ensemble of any weak potential with the reference field and kernel. -/
lemma s82r_referenceLaw_eq_gen (hρ : HRS.Whole.IsProbDensity rho) (hbeta : 0 < beta) {N : ℕ} {p n : ℕ}
    (pins : Fin p → Euc d)
    (V : WeakPotential (HRS.Whole.withDensityReal rho))
    (hVφ : V.φ = s82r_phi q h (HRS.Whole.withDensityReal rho) beta N)
    (hVq : ∀ x y, V.q x y = q (x - y)) :
    referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins =
      pinnedLaw V (beta / N) n pins := by
  haveI := s82r_isProb hρ
  have hlam : 0 ≤ beta / (N : ℝ) := div_nonneg hbeta.le (Nat.cast_nonneg N)
  have hψ := isField_pinField V hlam pins
  set P : Measure (EucConfig d n) := Measure.pi fun _ : Fin n => (HRS.Whole.withDensityReal rho) with hP
  -- the weights agree
  have hE : ∀ y : EucConfig d n, referenceExponent q h (HRS.Whole.withDensityReal rho) beta N pins y =
      ∑ i, pinField V (beta / N) pins (y i) - (beta / N) * HRS.External.pairEnergy V y := by
    intro y
    unfold referenceExponent pinField HRS.External.pairEnergy HRS.MS.Phase2S82.pairSum
    simp only [hVφ, hVq, s82r_phi]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hW : ∀ y : EucConfig d n, fieldWeight V (pinField V (beta / N) pins) (beta / N) y =
      ENNReal.ofReal (Real.exp (referenceExponent q h (HRS.Whole.withDensityReal rho) beta N pins y)) := by
    intro y
    unfold fieldWeight
    rw [hE y]
  have hEm : Measurable (referenceExponent q h (HRS.Whole.withDensityReal rho) beta N pins (n := n)) := by
    have : referenceExponent q h (HRS.Whole.withDensityReal rho) beta N pins (n := n) = fun y =>
        ∑ i, pinField V (beta / N) pins (y i) - (beta / N) * HRS.External.pairEnergy V y := funext hE
    rw [this]
    exact (Finset.measurable_sum _ fun i _ => hψ.measurable.comp (measurable_pi_apply i)).sub
      ((HRS.External.measurable_pairEnergy V).const_mul _)
  have hZfin := fieldNorm_lt_top (V := V) hψ hlam n
  have hint : Integrable (fun y => Real.exp (referenceExponent q h (HRS.Whole.withDensityReal rho) beta N pins y)) P := by
    refine ⟨(Real.measurable_exp.comp hEm).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => (Real.exp_pos _).le)]
    have : ∫⁻ y, ENNReal.ofReal (Real.exp (referenceExponent q h (HRS.Whole.withDensityReal rho) beta N pins y)) ∂P =
        fieldNorm V (pinField V (beta / N) pins) (beta / N) n := by
      unfold fieldNorm
      exact lintegral_congr fun y => (hW y).symm
    rw [this]; exact hZfin
  have hZ : ENNReal.ofReal (∫ y, Real.exp (referenceExponent q h (HRS.Whole.withDensityReal rho) beta N pins y) ∂P) =
      fieldNorm V (pinField V (beta / N) pins) (beta / N) n := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y => (Real.exp_pos _).le)]
    unfold fieldNorm
    exact lintegral_congr fun y => (hW y).symm
  unfold referenceLaw exponentialTilt
  rw [hZ]
  unfold pinnedLaw fieldLaw fieldDensity
  have hfm : Measurable (fun y => ENNReal.ofReal (Real.exp (referenceExponent q h (HRS.Whole.withDensityReal rho) beta N pins y))) :=
    (Real.measurable_exp.comp hEm).ennreal_ofReal
  have hfw : (fun y : EucConfig d n => fieldWeight V (pinField V (beta / N) pins) (beta / N) y *
      (fieldNorm V (pinField V (beta / N) pins) (beta / N) n)⁻¹) =
      (fieldNorm V (pinField V (beta / N) pins) (beta / N) n)⁻¹ •
        fun y : EucConfig d n => ENNReal.ofReal (Real.exp (referenceExponent q h (HRS.Whole.withDensityReal rho) beta N pins y)) := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, hW y]
    ring
  rw [hfw, withDensity_smul _ hfm]


/-- The weak kernel `(x, y) ↦ q (x - y)` from a `ShortRangePole` with small row. -/
lemma s82r_weakKernelW (hd : 2 ≤ d) (hbeta : 0 < beta) (hq : ShortRangePole d q)
    (hsr : ∀ x, beta * HRS.Whole.convMeasure q (HRS.Whole.withDensityReal rho) x ≤ 1 / 1000)
    {G c : ℝ} (hG : 0 < G) (hρ : HRS.Whole.IsProbDensity rho)
    (hρG : HRS.Whole.HasR2GaussianUpper G c rho) :
    HRS.MS.Wr.EWeakKernel (HRS.Whole.withDensityReal rho) (1 / (1000 * beta))
      (fun x y : Euc d => q (x - y)) := by
  refine ⟨?_, fun x y => ?_, fun x y => hq.nonneg _, fun x => ?_⟩
  · exact hq.measurable.comp (measurable_fst.sub measurable_snd)
  · rw [← hq.even (x - y), neg_sub]
  · have hi := s82r_row_int hd hq hG hρ hρG x
    have e := ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun y => hq.nonneg _)
    rw [← e]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : beta * ∫ y, q (x - y) ∂(HRS.Whole.withDensityReal rho) ≤ 1 / 1000 := hsr x
    rw [le_div_iff₀ (by positivity)]
    nlinarith

/-- The reference field `beta q*mu + h N` has bounds `(1/1000 + t, t)` when `|h N| <= t`. -/
lemma s82r_isFieldW (hd : 2 ≤ d) (hbeta : 0 < beta) (hq : ShortRangePole d q)
    (hsr : ∀ x, beta * HRS.Whole.convMeasure q (HRS.Whole.withDensityReal rho) x ≤ 1 / 1000)
    {G c : ℝ} (hG : 0 < G) (hρ : HRS.Whole.IsProbDensity rho)
    (hρG : HRS.Whole.HasR2GaussianUpper G c rho) {N : ℕ} {t : ℝ}
    (hhm : Measurable (h N)) (hh : ∀ x, |h N x| ≤ t) :
    haveI := s82r_isProb hρ
    HRS.External.IsField (HRS.Whole.withDensityReal rho)
      (s82r_phi q h (HRS.Whole.withDensityReal rho) beta N) (1 / 1000 + t) t := by
  haveI := s82r_isProb hρ
  have hK := s82r_weakKernelW hd hbeta hq hsr hG hρ hρG
  have hconvm : Measurable (HRS.Whole.convMeasure q (HRS.Whole.withDensityReal rho)) :=
    hK.wr1_measurable_rowInt
  have hm : Measurable (s82r_phi q h (HRS.Whole.withDensityReal rho) beta N) :=
    (hconvm.const_mul beta).add hhm
  have hr : ∀ x, 0 ≤ beta * HRS.Whole.convMeasure q (HRS.Whole.withDensityReal rho) x :=
    fun x => mul_nonneg hbeta.le (s82r_conv_nonneg hq _ x)
  have hup : ∀ x, s82r_phi q h (HRS.Whole.withDensityReal rho) beta N x ≤ 1 / 1000 + t := by
    intro x
    unfold s82r_phi
    have := hsr x
    have := (abs_le.1 (hh x)).2
    linarith
  have hlow : ∀ x, -t ≤ s82r_phi q h (HRS.Whole.withDensityReal rho) beta N x := by
    intro x
    unfold s82r_phi
    have := hr x
    have := (abs_le.1 (hh x)).1
    linarith
  have ht0 : 0 ≤ t := (abs_nonneg _).trans (hh (0 : Euc d))
  have hbd : ∀ x, |s82r_phi q h (HRS.Whole.withDensityReal rho) beta N x| ≤ 1 / 1000 + t := by
    intro x
    rw [abs_le]
    constructor
    · have := hlow x; linarith
    · exact hup x
  have hint : Integrable (s82r_phi q h (HRS.Whole.withDensityReal rho) beta N)
      (HRS.Whole.withDensityReal rho) :=
    Integrable.of_bound hm.aestronglyMeasurable (1 / 1000 + t)
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hbd x)
  refine ⟨hm, hup, hint, ?_⟩
  have : ∫ x, (-t : ℝ) ∂(HRS.Whole.withDensityReal rho) ≤
      ∫ x, s82r_phi q h (HRS.Whole.withDensityReal rho) beta N x ∂(HRS.Whole.withDensityReal rho) :=
    integral_mono (integrable_const _) hint hlow
  simpa using this

/-- The weak potential of the reference field `beta q*mu + h N`. -/
def s82r_potW (hd : 2 ≤ d) (hbeta : 0 < beta) (hq : ShortRangePole d q)
    (hsr : ∀ x, beta * HRS.Whole.convMeasure q (HRS.Whole.withDensityReal rho) x ≤ 1 / 1000)
    {G c : ℝ} (hG : 0 < G) (hρ : HRS.Whole.IsProbDensity rho)
    (hρG : HRS.Whole.HasR2GaussianUpper G c rho) {N : ℕ} {t : ℝ}
    (hhm : Measurable (h N)) (hh : ∀ x, |h N x| ≤ t) :
    HRS.External.WeakPotential (HRS.Whole.withDensityReal rho) :=
  haveI := s82r_isProb hρ
  HRS.MS.Wl.wlPot (s82r_weakKernelW hd hbeta hq hsr hG hρ hρG) (by positivity)
    (s82r_isFieldW hd hbeta hq hsr hG hρ hρG hhm hh)

end HRS.MS.S82R

end
