import HRS.MS.R2WinErrAux15
import HRS.MS.GenPathAux11

/-!
# S10.4 packet E4a: measurability of the corrected energy in the configuration (input of `S104ClassInput`)

`s104_energy_meas`: for a probability density `ρ₀` (measurable), `Z ↦ F_N(Z, ρ₀ dx) + o_N` is measurable on `EucConfig d N`
(the proof of `s56_energy_meas` for a time-independent density).  Also `s104_energy_joint_meas`: joint measurability in `(r, Z)` when
`(r, y) ↦ ρ r y` is jointly measurable, and the transfer to `P ⊗ dr` along a progressive process (`s56_aemeas_of_clamp` pattern).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinErr

open HRS.Whole HRS.Whole.AppendixA HRS.MP.RdRem

variable {d : ℕ}

/-- Joint measurability of the corrected energy in `(r, Z)` for a jointly measurable family of probability densities. -/
theorem s104_energy_joint_meas (N : ℕ) (s C₀ : ℝ) (ρ : ℝ → Euc d → ℝ)
    (hprob : ∀ r, HRS.Whole.IsProbDensity (ρ r)) (hjm : Measurable fun p : ℝ × Euc d => ρ p.1 p.2) :
    Measurable fun p : ℝ × EucConfig d N =>
      rieszModulatedEnergy d s p.2 (HRS.Whole.withDensityReal (ρ p.1)) + HRS.oN d s C₀ N := by
  have hgm : Measurable (rieszKernel d s) := mrr_measurable_rieszKernel s
  have hint : ∀ (q : ℝ) (f : Euc d → ℝ),
      ∫ y, f y ∂(HRS.Whole.withDensityReal (ρ q)) = ∫ y, ρ q y * f y :=
    fun q f => mrr_integral_withDensityReal (ρ q) (hprob q).measurable (hprob q).nonneg f
  unfold rieszModulatedEnergy HRS.Whole.modulatedEnergy
  refine Measurable.add (Measurable.add (Measurable.sub ?_ ?_) ?_) measurable_const
  · refine measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_)
    exact hgm.comp (((measurable_pi_apply i).comp measurable_snd).sub
      ((measurable_pi_apply j).comp measurable_snd))
  · refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
    have e' : (fun p : ℝ × EucConfig d N => HRS.Whole.convMeasure (rieszKernel d s)
          (HRS.Whole.withDensityReal (ρ p.1)) (p.2 i)) =
        fun p => ∫ y, ρ p.1 y * rieszKernel d s (p.2 i - y) := funext fun p => hint p.1 _
    rw [e']
    have : StronglyMeasurable (fun q : (ℝ × EucConfig d N) × Euc d =>
        ρ q.1.1 q.2 * rieszKernel d s (q.1.2 i - q.2)) := by
      refine Measurable.stronglyMeasurable ?_
      refine Measurable.mul ?_ ?_
      · exact hjm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
      · exact hgm.comp (((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)).sub
          measurable_snd)
    exact (this.integral_prod_right' (ν := volume)).measurable
  · have e : (fun p : ℝ × EucConfig d N => HRS.Whole.energyPairing (rieszKernel d s)
          (HRS.Whole.withDensityReal (ρ p.1)) (HRS.Whole.withDensityReal (ρ p.1))) =
        fun p => ∫ x, ρ p.1 x * ∫ y, ρ p.1 y * rieszKernel d s (x - y) := by
      funext p
      unfold HRS.Whole.energyPairing
      rw [hint p.1]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only
      rw [hint p.1]
    refine Measurable.const_mul ?_ _
    rw [e]
    have h1 : StronglyMeasurable (fun q : (ℝ × Euc d) × Euc d =>
        ρ q.1.1 q.2 * rieszKernel d s (q.1.2 - q.2)) := by
      refine Measurable.stronglyMeasurable (Measurable.mul ?_ ?_)
      · exact hjm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
      · exact hgm.comp ((measurable_snd.comp measurable_fst).sub measurable_snd)
    have h2 := h1.integral_prod_right' (ν := volume)
    have h3 : StronglyMeasurable (fun q : ℝ × Euc d =>
        ρ q.1 q.2 * ∫ y, ρ q.1 y * rieszKernel d s (q.2 - y)) :=
      (hjm.stronglyMeasurable).mul h2
    have h4 := h3.integral_prod_right' (ν := volume)
    exact h4.measurable.comp measurable_fst

/-- Measurability of the corrected energy in the configuration for one probability density. -/
theorem s104_energy_meas (N : ℕ) (s C₀ : ℝ) (ρ₀ : Euc d → ℝ) (hprob : HRS.Whole.IsProbDensity ρ₀) :
    Measurable fun Z : EucConfig d N =>
      rieszModulatedEnergy d s Z (HRS.Whole.withDensityReal ρ₀) + HRS.oN d s C₀ N := by
  have hjm : Measurable fun p : ℝ × Euc d => (fun _ : ℝ => ρ₀) p.1 p.2 := by
    exact hprob.measurable.comp measurable_snd
  have h := s104_energy_joint_meas N s C₀ (fun _ : ℝ => ρ₀) (fun _ => hprob) hjm
  have hm : Measurable (fun Z : EucConfig d N => ((0 : ℝ), Z)) := measurable_prodMk_left
  have hc := h.comp hm
  simpa only [Function.comp_def] using hc

open HRS.MS.GenPath in
/-- `P ⊗ dr`-a.e. measurability of the corrected energy along a progressive process, for a family of probability densities whose clamped
version is jointly measurable (`s56_energy_aemeas` for an arbitrary jointly measurable family). -/
theorem s104_energy_aemeas {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) {N : ℕ} (X : ℝ≥0 → Ω → EucConfig d N)
    (hprog : IsProgressive ℱ (ofNNRealTime X)) (s C₀ : ℝ) (ρ : ℝ → Euc d → ℝ) {T' : ℝ} (hT' : 0 ≤ T')
    (hprob : ∀ r ∈ Set.Icc (0 : ℝ) T', HRS.Whole.IsProbDensity (ρ r))
    (hjm : Measurable fun p : ℝ × Euc d => ρ (mrrClamp T' p.1) p.2) :
    AEMeasurable (fun p : Ω × ℝ => rieszModulatedEnergy d s (X p.2.toNNReal p.1)
        (HRS.Whole.withDensityReal (ρ p.2)) + HRS.oN d s C₀ N)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T'))) := by
  have hF := s104_energy_joint_meas N s C₀ (fun q => ρ (mrrClamp T' q))
    (fun q => hprob _ (mrrClamp_mem hT' q)) hjm
  have h := s56_aemeas_of_clamp P ℱ X hprog hT' _ hF
  refine h.congr ?_
  have hq : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T'))), p.2 ∈ Set.Icc (0 : ℝ) T' :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Icc)
  filter_upwards [hq] with p hp
  simp only [mrrClamp_of_mem hp]

end HRS.MS.R2WinErr
