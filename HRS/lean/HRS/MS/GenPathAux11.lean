import HRS.MS.GenPathAux10
import HRS.MP.RdRemainder

/-!
# S5.6 packet P4: joint measurability of the corrected energy and of the empirical second moment in `(ζ, r)`

For `S : WholeSetup b`: `(r, X) ↦ F_N(X, ρ_N^{clamp r}) + o_N` is jointly measurable (`s56_energy_meas`, the proof of
`mrr_energy_meas` of `HRS/MP/RdRemainder.lean` transported to the hypotheses of `WholeSetup`: continuity of `ρ_N^t(y)` in
`t` is `s55m_rho_data`), and composed with the progressive particle process it is `P ⊗ dr`-a.e.-measurable on `[0,T]`
(`s56_energy_aemeas`, `s56_mm_aemeas`): exactly the measurability hypotheses of `s56_trace_moment` (`GenPathAux4`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS.Whole HRS.Whole.AppendixA HRS.MP.RdRem

variable {d : ℕ}

theorem s56_rho_meas (b : WholeBounds d) (hb : b.Valid) (S : WholeSetup b) (N : ℕ) :
    Measurable fun p : ℝ × Euc d => S.ρ N (mrrClamp b.T p.1) p.2 := by
  have hT : 0 ≤ b.T := hb.hT.le
  obtain ⟨A, -, -, hcont⟩ := HRS.MS.Go.s55m_rho_data b hb S N
  have hρc : ∀ q, Continuous (S.ρ N (mrrClamp b.T q)) := fun q =>
    ((S.dens N _ (mrrClamp_mem hT q)).1).continuous
  have hpt : ∀ x, Continuous fun q => S.ρ N (mrrClamp b.T q) x := fun x =>
    (hcont x).comp_continuous (continuous_mrrClamp b.T) (fun q => mrrClamp_mem hT q)
  exact measurable_uncurry_of_continuous_of_measurable (u := fun (q : ℝ) (x : Euc d) =>
    S.ρ N (mrrClamp b.T q) x) (fun x => hpt x) (fun q => (hρc q).measurable)

theorem s56_energy_meas (b : WholeBounds d) (hb : b.Valid) (S : WholeSetup b) (N : ℕ) :
    Measurable fun p : ℝ × EucConfig d N =>
      rieszModulatedEnergy d b.s p.2 (HRS.Whole.withDensityReal (S.ρ N (mrrClamp b.T p.1))) +
        HRS.oN d b.s b.C₀ N := by
  have hT : 0 ≤ b.T := hb.hT.le
  have hgm : Measurable (rieszKernel d b.s) := mrr_measurable_rieszKernel b.s
  have hjm := s56_rho_meas b hb S N
  set ρt : ℝ → Euc d → ℝ := fun q => S.ρ N (mrrClamp b.T q) with hρt
  have hprob : ∀ q, HRS.Whole.IsProbDensity (ρt q) := fun q =>
    (S.mf N).density _ (mrrClamp_mem hT q)
  have hint : ∀ (q : ℝ) (f : Euc d → ℝ),
      ∫ y, f y ∂(HRS.Whole.withDensityReal (ρt q)) = ∫ y, ρt q y * f y :=
    fun q f => mrr_integral_withDensityReal (ρt q) (hprob q).measurable (hprob q).nonneg f
  have hjm' : Measurable fun p : ℝ × Euc d => ρt p.1 p.2 := hjm
  unfold rieszModulatedEnergy HRS.Whole.modulatedEnergy
  refine Measurable.add (Measurable.add (Measurable.sub ?_ ?_) ?_) measurable_const
  · refine measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_)
    exact hgm.comp (((measurable_pi_apply i).comp measurable_snd).sub
      ((measurable_pi_apply j).comp measurable_snd))
  · refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
    have e' : (fun p : ℝ × EucConfig d N => HRS.Whole.convMeasure (rieszKernel d b.s)
          (HRS.Whole.withDensityReal (ρt p.1)) (p.2 i)) =
        fun p => ∫ y, ρt p.1 y * rieszKernel d b.s (p.2 i - y) := funext fun p => hint p.1 _
    rw [e']
    have : StronglyMeasurable (fun q : (ℝ × EucConfig d N) × Euc d =>
        ρt q.1.1 q.2 * rieszKernel d b.s (q.1.2 i - q.2)) := by
      refine Measurable.stronglyMeasurable ?_
      refine Measurable.mul ?_ ?_
      · exact hjm'.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
      · exact hgm.comp (((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)).sub
          measurable_snd)
    exact (this.integral_prod_right' (ν := volume)).measurable
  · have e : (fun p : ℝ × EucConfig d N => HRS.Whole.energyPairing (rieszKernel d b.s)
          (HRS.Whole.withDensityReal (ρt p.1)) (HRS.Whole.withDensityReal (ρt p.1))) =
        fun p => ∫ x, ρt p.1 x * ∫ y, ρt p.1 y * rieszKernel d b.s (x - y) := by
      funext p
      unfold HRS.Whole.energyPairing
      rw [hint p.1]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only
      rw [hint p.1]
    refine Measurable.const_mul ?_ _
    rw [e]
    have h1 : StronglyMeasurable (fun q : (ℝ × Euc d) × Euc d =>
        ρt q.1.1 q.2 * rieszKernel d b.s (q.1.2 - q.2)) := by
      refine Measurable.stronglyMeasurable (Measurable.mul ?_ ?_)
      · exact hjm'.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
      · exact hgm.comp ((measurable_snd.comp measurable_fst).sub measurable_snd)
    have h2 := h1.integral_prod_right' (ν := volume)
    have h3 : StronglyMeasurable (fun q : ℝ × Euc d =>
        ρt q.1 q.2 * ∫ y, ρt q.1 y * rieszKernel d b.s (q.2 - y)) :=
      (hjm'.stronglyMeasurable).mul h2
    have h4 := h3.integral_prod_right' (ν := volume)
    exact h4.measurable.comp measurable_fst

/-- Transfer of a clamped jointly measurable function of `(r, X_r)` to an a.e.-measurable function on
`P ⊗ (dr|_{[0,T]})`. -/
theorem s56_aemeas_of_clamp {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) {N : ℕ} (X : ℝ≥0 → Ω → EucConfig d N)
    (hprog : IsProgressive ℱ (ofNNRealTime X)) {T : ℝ} (hT : 0 ≤ T)
    (F : ℝ × EucConfig d N → ℝ) (hF : Measurable F) :
    AEMeasurable (fun p : Ω × ℝ => F (p.2, X (Real.toNNReal p.2) p.1))
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
  have hX := mrr_prog_meas ℱ X hprog hT
  have hm : Measurable fun p : Ω × ℝ => F (mrrClamp T p.2, X (Real.toNNReal (mrrClamp T p.2)) p.1) := by
    refine hF.comp (((continuous_mrrClamp T).measurable.comp measurable_snd).prodMk ?_)
    exact hX.comp (measurable_snd.prodMk measurable_fst)
  refine hm.aemeasurable.congr ?_
  have hq : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))), p.2 ∈ Set.Icc (0 : ℝ) T :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Icc)
  filter_upwards [hq] with p hp
  rw [mrrClamp_of_mem hp]

theorem s56_energy_aemeas (b : WholeBounds d) (hb : b.Valid) (S : WholeSetup b) (N : ℕ)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (X : ℝ≥0 → Ω → EucConfig d N) (hprog : IsProgressive ℱ (ofNNRealTime X)) :
    AEMeasurable (fun p : Ω × ℝ => rieszModulatedEnergy d b.s (X (Real.toNNReal p.2) p.1)
        (HRS.Whole.withDensityReal (S.ρ N p.2)) + HRS.oN d b.s b.C₀ N)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) b.T))) := by
  have h := s56_aemeas_of_clamp P ℱ X hprog hb.hT.le _ (s56_energy_meas b hb S N)
  refine h.congr ?_
  have hq : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) b.T))), p.2 ∈ Set.Icc (0 : ℝ) b.T :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Icc)
  filter_upwards [hq] with p hp
  simp only [mrrClamp_of_mem hp]

theorem s56_mm_aemeas {N : ℕ} (hN : 0 < N) {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (X : ℝ≥0 → Ω → EucConfig d N)
    (hprog : IsProgressive ℱ (ofNNRealTime X)) {T : ℝ} (hT : 0 ≤ T) :
    AEMeasurable (fun p : Ω × ℝ => secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal p.2) p.1)))
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
  have hF : Measurable fun p : ℝ × EucConfig d N => secondMomentOf (HRS.Whole.empirical p.2) := by
    have e : (fun p : ℝ × EucConfig d N => secondMomentOf (HRS.Whole.empirical p.2)) =
        fun p => (N : ℝ)⁻¹ * ∑ i, ‖p.2 i‖ ^ 2 := by
      funext p
      unfold secondMomentOf
      exact HRS.Whole.pair_empirical hN p.2 _
    rw [e]
    exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      (measurable_norm.comp ((measurable_pi_apply i).comp measurable_snd)).pow_const 2)
  exact s56_aemeas_of_clamp P ℱ X hprog hT _ hF

end HRS.MS.GenPath
