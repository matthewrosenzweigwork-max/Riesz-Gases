import HRS.MS.S82RQ1
import HRS.MS.S82RB4
import HRS.MS.WrQuadAux3
import HRS.MS.WrRefMargAux3

/-!
# S8.2 R01A (S82R), part 1: general helpers
`referenceLaw` as a weak ensemble for an arbitrary weak potential, bounded tilts, density bounds.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82R
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

open HRS.External in
/-- `referenceLaw` is the pinned weak ensemble of any weak potential with the right kernel and field. -/
lemma s82r_referenceLaw_eq_pot {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {q : Euc d → ℝ}
    {h : ℕ → Euc d → ℝ} {beta : ℝ} {N : ℕ} (V : WeakPotential μ)
    (hVφ : V.φ = s82r_phi q h μ beta N) (hVq : ∀ x y, V.q x y = q (x - y))
    (hbeta : 0 ≤ beta) {p n : ℕ} (pins : Fin p → Euc d) :
    referenceLaw q h μ beta N n pins = pinnedLaw V (beta / N) n pins := by
  have hlam : 0 ≤ beta / (N : ℝ) := div_nonneg hbeta (Nat.cast_nonneg N)
  have hψ := isField_pinField V hlam pins
  set P : Measure (EucConfig d n) := Measure.pi fun _ : Fin n => μ with hP
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

open HRS.External in
/-- Unpinned case: `pinnedLaw` with no pins is `fieldLaw V V.φ`. -/
lemma s82r_pinnedLaw_zero {μ : Measure (Euc d)} (V : WeakPotential μ) (lam : ℝ) (n : ℕ) :
    pinnedLaw V lam n (fun i : Fin 0 => i.elim0) = fieldLaw V V.φ lam n := by
  unfold pinnedLaw
  congr 1
  funext z
  simp [pinField]

/-- A bounded tilt: `P.tilted f ≤ e^{2B} P` if `|f| ≤ B`. -/
lemma s82r_tilted_le {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
    (f : α → ℝ) (hfm : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    P.tilted f ≤ ENNReal.ofReal (Real.exp (2 * B)) • P := by
  have hfi : Integrable (fun x => Real.exp (f x)) P := by
    refine Integrable.of_bound (Real.measurable_exp.comp hfm).aestronglyMeasurable (Real.exp B)
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 ((le_abs_self _).trans (hB x))
  have hZ : Real.exp (-B) ≤ ∫ x, Real.exp (f x) ∂P := by
    have := integral_mono (μ := P) (integrable_const (Real.exp (-B))) hfi
      (fun x => Real.exp_le_exp.2 (by linarith [(abs_le.1 (hB x)).1]))
    simpa using this
  have hZpos : 0 < ∫ x, Real.exp (f x) ∂P := (Real.exp_pos _).trans_le hZ
  refine Measure.le_iff.2 fun A hA => ?_
  unfold Measure.tilted
  rw [withDensity_apply _ hA, Measure.smul_apply, smul_eq_mul]
  calc ∫⁻ x in A, ENNReal.ofReal (Real.exp (f x) / ∫ x', Real.exp (f x') ∂P) ∂P
      ≤ ∫⁻ x in A, ENNReal.ofReal (Real.exp (2 * B)) ∂P := by
        refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
        rw [div_le_iff₀ hZpos]
        calc Real.exp (f x) ≤ Real.exp B := Real.exp_le_exp.2 ((le_abs_self _).trans (hB x))
          _ = Real.exp (2 * B) * Real.exp (-B) := by rw [← Real.exp_add]; ring_nf
          _ ≤ _ := mul_le_mul_of_nonneg_left hZ (Real.exp_pos _).le
    _ = _ := by rw [setLIntegral_const]

/-- `ν ≤ c μ` gives `dν/dμ ≤ c` a.e. -/
lemma s82r_rnDeriv_le {μ ν : Measure (Euc d)} [IsProbabilityMeasure μ] [IsFiniteMeasure ν] {c : ℝ}
    (hc : 0 ≤ c) (hle : ν ≤ ENNReal.ofReal c • μ) : ∀ᵐ x ∂μ, (ν.rnDeriv μ x).toReal ≤ c := by
  have hac : ν ≪ μ := by
    refine Measure.AbsolutelyContinuous.mk fun s hs hμs => ?_
    have := hle s
    rw [Measure.smul_apply, hμs, smul_zero] at this
    exact le_antisymm this bot_le
  haveI : ν.HaveLebesgueDecomposition μ := Measure.haveLebesgueDecomposition_of_sigmaFinite ν μ
  have hae : ∀ᵐ x ∂μ, ν.rnDeriv μ x ≤ ENNReal.ofReal c := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv ν μ) fun s hs _ => ?_
    rw [Measure.setLIntegral_rnDeriv hac, setLIntegral_const]
    have := hle s
    rw [Measure.smul_apply, smul_eq_mul] at this
    exact this
  filter_upwards [hae, Measure.rnDeriv_lt_top ν μ] with x h1 h2
  exact ((ENNReal.toReal_le_toReal h2.ne ENNReal.ofReal_ne_top).2 h1).trans (ENNReal.toReal_ofReal hc).le

end HRS.MS.S82R

end
