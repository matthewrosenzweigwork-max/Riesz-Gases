import HRS.MS.S113X2C9

/-!
# S11.3 X2 wiring (worker S11W), C10: helper lemmas for the final assembly

* `s113c_movQ_measurable`: `X ↦ movQDensity ρ X` is measurable.
* `s113c_qmax`: the moving reference is bounded above on a compact set.
* `s113c_initial_bound`: the weighted initial law is dominated by a multiple of Lebesgue measure on `D`.
* `s113c_rnDeriv_ae`: the Radon-Nikodym derivative of a density family against the moving Gibbs law.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory intervalIntegral
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2C

open HRS HRS.Whole HRS.MS.S113X2 HRS.MS.S113X2B
open HRS.MC.CepP3 (Jc Jc_single fderiv2_comp_clm)

variable {d N : ℕ}

theorem s113c_movQ_measurable (s β : ℝ) {ρ : Euc d → ℝ} (hρ : Measurable ρ) :
    Measurable (movQDensity d s β N ρ) := by
  unfold movQDensity rieszModulatedEnergy HRS.Whole.modulatedEnergy
  have hg : Measurable (rieszKernel d s) := HRS.MP.RdRem.mrr_measurable_rieszKernel s
  have h1 : Measurable (fun X : EucConfig d N => ∑ i, ∑ j ∈ Finset.univ.erase i, rieszKernel d s (X i - X j)) :=
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      hg.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))
  haveI : SFinite (HRS.Whole.withDensityReal ρ) := by unfold HRS.Whole.withDensityReal; infer_instance
  have hconv : Measurable (HRS.Whole.convMeasure (rieszKernel d s) (HRS.Whole.withDensityReal ρ)) := by
    unfold HRS.Whole.convMeasure
    have : StronglyMeasurable (Function.uncurry fun x y : Euc d => rieszKernel d s (x - y)) :=
      (hg.comp (measurable_fst.sub measurable_snd)).stronglyMeasurable
    exact (this.integral_prod_right' (ν := HRS.Whole.withDensityReal ρ)).measurable
  have h2 : Measurable (fun X : EucConfig d N => ∑ i, HRS.Whole.convMeasure (rieszKernel d s)
      (HRS.Whole.withDensityReal ρ) (X i)) :=
    Finset.measurable_sum _ fun i _ => hconv.comp (measurable_pi_apply i)
  have h3 : Measurable (fun X : EucConfig d N => ∏ i, ρ (X i)) :=
    Finset.measurable_prod _ fun i _ => hρ.comp (measurable_pi_apply i)
  exact (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul
    (((measurable_const.mul h1).sub (measurable_const.mul h2)).add measurable_const)))).mul h3

theorem s113c_qmax {s β : ℝ} {ρ : ℝ → Euc d → ℝ} {T : ℝ} {K : Set (EucConfig d N)} (hK : IsCompact K)
    {qt : ℝ → s113b_E (N * d) → ℝ} {G' : Set (s113b_E (N * d))} (hQ : s113c_QReg d N s β ρ T K qt G') :
    ∃ Cq : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ K, movQDensity d s β N (ρ t) x ≤ Cq := by
  have hKE : IsCompact (Jc d N ⁻¹' K) := ((Jc d N).toHomeomorph.isCompact_preimage).2 hK
  obtain ⟨Cq, hCq⟩ := (isCompact_Icc.prod hKE).exists_bound_of_continuousOn
    (f := fun z : ℝ × s113b_E (N * d) => qt z.1 z.2) hQ.smooth.continuous.continuousOn
  refine ⟨Cq, fun t ht x hx => ?_⟩
  set z := (Jc d N).symm x with hz
  have hzK : z ∈ Jc d N ⁻¹' K := by simpa [hz] using hx
  have h1 := hCq (t, z) ⟨ht, hzK⟩
  have h2 := hQ.match_ t ⟨ht.1, by linarith [ht.2]⟩ z (hQ.subset z (by simpa [hz] using hx))
  have h3 : Jc d N z = x := (Jc d N).apply_symm_apply x
  rw [h3] at h2
  rw [← h2]
  exact (le_abs_self _).trans h1

theorem s113c_initial_bound (μ0 : Measure (EucConfig d N)) (q0 : EucConfig d N → ℝ)
    (Q0 : Measure (EucConfig d N)) [IsFiniteMeasure Q0]
    (hQ0 : Q0 = volume.withDensity (fun x => ENNReal.ofReal (q0 x))) (hac : μ0 ≪ Q0)
    (chi : EucConfig d N → ℝ) (hchim : Measurable chi) {n : ℕ}
    (hchin : ∀ᵐ x ∂Q0, ENNReal.ofReal (chi x) * μ0.rnDeriv Q0 x ≤ ENNReal.ofReal n)
    (D : Set (EucConfig d N)) (hDm : MeasurableSet D) {Cq : ℝ} (hCq : ∀ x ∈ D, q0 x ≤ Cq) [SigmaFinite μ0] :
    μ0.withDensity (D.indicator fun x => ENNReal.ofReal (chi x)) ≤ ENNReal.ofReal (n * Cq) • volume := by
  refine Measure.le_iff.2 fun A hA => ?_
  have hg : Measurable (D.indicator fun x => ENNReal.ofReal (chi x)) :=
    (ENNReal.measurable_ofReal.comp hchim).indicator hDm
  rw [withDensity_apply _ hA, Measure.smul_apply, smul_eq_mul]
  have hS : MeasurableSet (A ∩ D) := hA.inter hDm
  have e1 : ∫⁻ x in A, D.indicator (fun x => ENNReal.ofReal (chi x)) x ∂μ0 =
      ∫⁻ x in A ∩ D, ENNReal.ofReal (chi x) ∂μ0 := by
    rw [lintegral_indicator hDm, Measure.restrict_restrict hDm, Set.inter_comm]
  rw [e1]
  nth_rewrite 1 [← Measure.withDensity_rnDeriv_eq _ _ hac]
  have hrm := Measure.measurable_rnDeriv μ0 Q0
  rw [setLIntegral_withDensity_eq_setLIntegral_mul _ hrm (g := fun x => ENNReal.ofReal (chi x))
    (ENNReal.measurable_ofReal.comp hchim) hS]
  have h1 : ∫⁻ x in A ∩ D, (μ0.rnDeriv Q0 * fun x => ENNReal.ofReal (chi x)) x ∂Q0 ≤
      ∫⁻ x in A ∩ D, ENNReal.ofReal n ∂Q0 := by
    refine lintegral_mono_ae (ae_restrict_of_ae ?_)
    filter_upwards [hchin] with x hx
    simpa [mul_comm] using hx
  refine h1.trans ?_
  rw [setLIntegral_const, hQ0, withDensity_apply _ hS]
  have h2 : ∫⁻ x in A ∩ D, ENNReal.ofReal (q0 x) ∂volume ≤ ∫⁻ x in A ∩ D, ENNReal.ofReal Cq ∂volume := by
    refine setLIntegral_mono' hS fun x hx => ENNReal.ofReal_le_ofReal (hCq x hx.2)
  rw [setLIntegral_const] at h2
  calc ENNReal.ofReal n * ∫⁻ x in A ∩ D, ENNReal.ofReal (q0 x) ∂volume
      ≤ ENNReal.ofReal n * (ENNReal.ofReal Cq * volume (A ∩ D)) := by gcongr
    _ ≤ ENNReal.ofReal n * (ENNReal.ofReal Cq * volume A) := by gcongr; exact Set.inter_subset_left
    _ = ENNReal.ofReal (n * Cq) * volume A := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]

open Classical in
/-- The killed law at time `0` is the initial law weighted by `1_D χ`. -/
theorem s113c_killedLaw_zero {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {s q β : ℝ} {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : MovParticleSetup P d s q β N X₀ W X) (D : Set (EucConfig d N)) (hD : IsOpen D)
    (chi : EucConfig d N → ℝ) (hchim : Measurable chi) :
    s113a_killedLaw P D X₀ X chi 0 = (P.map X₀).withDensity (D.indicator fun x => ENNReal.ofReal (chi x)) := by
  have hsol := hX.sol 0
  have hX0 : Measurable (X 0) := hsol.adapted 0
  have hg : Measurable (D.indicator fun x => ENNReal.ofReal (chi x)) :=
    (ENNReal.measurable_ofReal.comp hchim).indicator hD.measurableSet
  ext A hA
  have h1 : P.map X₀ = P.map (X 0) := (Measure.map_congr hsol.init).symm
  rw [h1, withDensity_apply _ hA]
  unfold s113a_killedLaw
  rw [Measure.map_apply hX0 hA]
  set w : Ω → ℝ≥0∞ := fun ζ => if ζ ∈ s113a_survives D X 0 then ENNReal.ofReal (chi (X₀ ζ)) else 0 with hw
  have hwae : w =ᵐ[P] fun ζ => (D.indicator fun x => ENNReal.ofReal (chi x)) (X 0 ζ) := by
    filter_upwards [hsol.init] with ζ hζ
    simp only [hw]
    by_cases hD0 : X 0 ζ ∈ D
    · have : ζ ∈ s113a_survives D X 0 := fun r hr => by
        have : r = 0 := le_antisymm hr (zero_le)
        rw [this]; exact hD0
      rw [if_pos this, Set.indicator_of_mem hD0, hζ]
    · have : ζ ∉ s113a_survives D X 0 := fun h => hD0 (h 0 le_rfl)
      rw [if_neg this, Set.indicator_of_notMem hD0]
  rw [withDensity_apply _ (hX0 hA), lintegral_congr_ae (ae_restrict_of_ae hwae)]
  exact (setLIntegral_map hA hg hX0).symm

theorem s113c_rnDeriv_ae {q u : EucConfig d N → ℝ} (hqm : Measurable q) (hq : ∀ x, 0 < q x)
    (hum : Measurable u) (hu0 : ∀ x, 0 ≤ u x) (ν : Measure (EucConfig d N))
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal (u x)))
    [SigmaFinite (volume.withDensity (fun x => ENNReal.ofReal (q x)))] :
    (fun x => (ν.rnDeriv (volume.withDensity (fun x => ENNReal.ofReal (q x))) x).toReal) =ᵐ[
      volume.withDensity (fun x => ENNReal.ofReal (q x))] fun x => u x / q x := by
  have hqm' : Measurable (fun x => ENNReal.ofReal (q x)) := ENNReal.measurable_ofReal.comp hqm
  have hgm : Measurable (fun x => ENNReal.ofReal (u x / q x)) :=
    ENNReal.measurable_ofReal.comp (hum.div hqm)
  have hν' : ν = (volume.withDensity (fun x => ENNReal.ofReal (q x))).withDensity
      (fun x => ENNReal.ofReal (u x / q x)) := by
    rw [hν, ← withDensity_mul _ hqm' hgm]
    congr 1
    funext x
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (hq x).le, mul_div_cancel₀ _ (hq x).ne']
  rw [hν']
  filter_upwards [Measure.rnDeriv_withDensity₀ (volume.withDensity (fun x => ENNReal.ofReal (q x)))
    hgm.aemeasurable] with x hx
  rw [hx, ENNReal.toReal_ofReal (div_nonneg (hu0 x) (hq x).le)]

end HRS.MS.S113X2C

end
