import HRS.MD.EQBurnBurnBase
import HRS.MD.EQMild4
import HRS.MD.EQInterpWin
import HRS.Main.T25PAux17

/-!
# EQ-BURN P4, part 4: the remainder package

For the process `Xp t = ζ^t = zetaE m (P₁.map (Y t)) (Y t)`, the linear flow `Vev t 0 ζ^0` and a continuous convolution `Zm`, the remainder
`Rr := Xp - Vev(·,0) ζ^0 - Zm` has the Fourier coefficients `statF` (the mild identity of EQ-MILD); this yields the measurability, the a.s.
continuity of `Rr` on `[0,S]`, the measurable majorant `Bm = sup_{t ∈ ratTimes a T} (coordEnergy statF)^{1/2}` and the domination
`‖Rr t‖ₑ ≤ Bm` on `[a,a+T]`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQBurnBurn

open HRS HRS.LZ HRS.MD.EQMild HRS.MD.EQ29

variable {d : ℕ}

theorem eqb_fourierCoeff_sub {M : ℝ} (x y : NegSobolev d M) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (x - y) k = NegSobolev.fourierCoeff x k - NegSobolev.fourierCoeff y k := by
  rw [← eqmild_fc_apply, ← eqmild_fc_apply, ← eqmild_fc_apply, map_sub]

theorem eqb_rem_package {m : ℝ} (hm : (d : ℝ) < 2 * m) {N : ℕ} (hN : 1 ≤ N) {a T : ℝ} (ha : 0 ≤ a) (hT : 0 < T)
    {Ω₁ : Type*} [MeasurableSpace Ω₁] (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (Y : ℝ≥0 → Ω₁ → Config d N) (G : Measure (Config d N)) [IsProbabilityMeasure G]
    (hYm : ∀ t, Measurable (Y t))
    (hstat : ∀ t : ℝ≥0, (t : ℝ) ≤ a + T → P₁.map (Y t) = G)
    (hYc : ∀ᵐ ω ∂P₁, ∀ i, Continuous fun t : ℝ≥0 => Y t ω i)
    (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (hVc : ∀ x : NegSobolev d m, ContinuousOn (fun t : ℝ => Vev t 0 x) (Set.Icc 0 (a + T)))
    (Zm : ℝ → Ω₁ → NegSobolev d m) (hZmm : ∀ t, Measurable (Zm t))
    (hZmc : ∀ᵐ ω ∂P₁, ContinuousOn (fun t => Zm t ω) (Set.Icc 0 (a + T)))
    (statF : NonzeroLattice d → ℝ → Ω₁ → ℝ)
    (hmild : ∀ᵐ ω ∂P₁, ∀ t ∈ Set.Icc (0 : ℝ) (a + T), ∀ k : NonzeroLattice d,
      NegSobolev.fourierCoeff (zetaE m (P₁.map (Y t.toNNReal)) (Y t.toNNReal ω)) k =
        NegSobolev.fourierCoeff (Vev t 0 (zetaE m (P₁.map (Y 0)) (Y 0 ω))) k +
          NegSobolev.fourierCoeff (Zm t ω) k + statF k t ω) :
    (∀ t, Measurable (fun ω => zetaE m (P₁.map (Y t.toNNReal)) (Y t.toNNReal ω) -
        Vev t 0 (zetaE m (P₁.map (Y 0)) (Y 0 ω)) - Zm t ω)) ∧
    (∀ᵐ ω ∂P₁, ContinuousOn (fun t => zetaE m (P₁.map (Y t.toNNReal)) (Y t.toNNReal ω) -
        Vev t 0 (zetaE m (P₁.map (Y 0)) (Y 0 ω)) - Zm t ω) (Set.Icc 0 (a + T))) ∧
    AEMeasurable (fun ω => ⨆ t ∈ ratTimes a T, (coordEnergy m (fun k => statF k t ω)) ^ (1 / 2 : ℝ)) P₁ ∧
    (∀ᵐ ω ∂P₁, ∀ t ∈ Set.Icc a (a + T),
      ‖zetaE m (P₁.map (Y t.toNNReal)) (Y t.toNNReal ω) -
        Vev t 0 (zetaE m (P₁.map (Y 0)) (Y 0 ω)) - Zm t ω‖ₑ ≤
        ⨆ t ∈ ratTimes a T, (coordEnergy m (fun k => statF k t ω)) ^ (1 / 2 : ℝ)) := by
  have hS0 : 0 ≤ a + T := by linarith
  have hPm : ∀ t : ℝ≥0, IsProbabilityMeasure (P₁.map (Y t)) := fun t =>
    ((Measure.isProbabilityMeasure_map_iff (hYm t).aemeasurable).2 inferInstance)
  have hzc : ∀ t : ℝ≥0, Continuous (zetaE m (P₁.map (Y t))) := fun t =>
    EQLawPath.eqlaw_continuous_zetaE hm hN _
  have hzm : ∀ t : ℝ, Measurable (fun ω => zetaE m (P₁.map (Y t.toNNReal)) (Y t.toNNReal ω)) :=
    fun t => (hzc t.toNNReal).measurable.comp (hYm _)
  have hz0m : Measurable (fun ω => zetaE m (P₁.map (Y 0)) (Y 0 ω)) := (hzc 0).measurable.comp (hYm 0)
  have hmapS : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), P₁.map (Y t.toNNReal) = G := fun t ht =>
    hstat _ (by rw [Real.coe_toNNReal _ ht.1]; exact ht.2)
  have hmap0 : P₁.map (Y 0) = G := hstat 0 (by simpa using hS0)
  have hcont : ∀ ω, (∀ i, Continuous fun t : ℝ≥0 => Y t ω i) →
      ContinuousOn (fun t : ℝ => Zm t ω) (Set.Icc 0 (a + T)) →
      ContinuousOn (fun t => zetaE m (P₁.map (Y t.toNNReal)) (Y t.toNNReal ω) -
        Vev t 0 (zetaE m (P₁.map (Y 0)) (Y 0 ω)) - Zm t ω) (Set.Icc 0 (a + T)) := by
    intro ω hω hZ
    have hX : ContinuousOn (fun t : ℝ => zetaE m (P₁.map (Y t.toNNReal)) (Y t.toNNReal ω))
        (Set.Icc 0 (a + T)) := by
      have hc : Continuous fun t : ℝ => zetaE m G (Y t.toNNReal ω) :=
        (EQLawPath.eqlaw_continuous_zetaE hm hN G).comp
          (continuous_pi fun i => (hω i).comp continuous_real_toNNReal)
      refine hc.continuousOn.congr fun t ht => ?_
      simp only [hmapS t ht]
    exact (hX.sub (hVc _)).sub hZ
  have hae : ∀ᵐ ω ∂P₁, ∀ t ∈ ratTimes a T,
      (coordEnergy m (fun k => statF k t ω)) ^ (1 / 2 : ℝ) =
        ‖zetaE m (P₁.map (Y t.toNNReal)) (Y t.toNNReal ω) -
          Vev t 0 (zetaE m (P₁.map (Y 0)) (Y 0 ω)) - Zm t ω‖ₑ := by
    filter_upwards [hmild] with ω hω t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) (a + T) := ⟨ha.trans ht.1.1, ht.1.2⟩
    rw [HRS.T25P.t25p_enorm_eq_tsum]
    unfold coordEnergy
    congr 3
    funext k
    rw [eqb_fourierCoeff_sub, eqb_fourierCoeff_sub, hω t ht' k]
    ring_nf
  refine ⟨fun t => ?_, ?_, ?_, ?_⟩
  · exact ((hzm t).sub ((Vev t 0).continuous.measurable.comp hz0m)).sub (hZmm t)
  · filter_upwards [hYc, hZmc] with ω hω hZ
    exact hcont ω hω hZ
  · -- measurability of the majorant
    have hmeas : Measurable (fun ω => ⨆ t ∈ ratTimes a T,
        ‖zetaE m (P₁.map (Y t.toNNReal)) (Y t.toNNReal ω) -
          Vev t 0 (zetaE m (P₁.map (Y 0)) (Y 0 ω)) - Zm t ω‖ₑ) := by
      have : Countable (ratTimes a T) := (eqb_ratTimes_countable a T).to_subtype
      have : (fun ω => ⨆ t ∈ ratTimes a T,
          ‖zetaE m (P₁.map (Y t.toNNReal)) (Y t.toNNReal ω) -
            Vev t 0 (zetaE m (P₁.map (Y 0)) (Y 0 ω)) - Zm t ω‖ₑ) =
          fun ω => ⨆ t : ratTimes a T, ‖zetaE m (P₁.map (Y (t : ℝ).toNNReal)) (Y (t : ℝ).toNNReal ω) -
            Vev t 0 (zetaE m (P₁.map (Y 0)) (Y 0 ω)) - Zm t ω‖ₑ := by
        funext ω
        rw [iSup_subtype']
      rw [this]
      refine Measurable.iSup fun t => ?_
      exact (((hzm t).sub ((Vev t 0).continuous.measurable.comp hz0m)).sub (hZmm t)).enorm
    refine hmeas.aemeasurable.congr ?_
    filter_upwards [hae] with ω hω
    exact iSup_congr fun t => iSup_congr fun ht => (hω t ht).symm
  · filter_upwards [hae, hYc, hZmc] with ω hω hY hZ t ht
    have hRc := hcont ω hY hZ
    have hsub : Set.Icc a (a + T) ⊆ Set.Icc 0 (a + T) := Set.Icc_subset_Icc ha le_rfl
    have h1 := eqb_le_iSup_rat hT (fun t => ‖zetaE m (P₁.map (Y t.toNNReal)) (Y t.toNNReal ω) -
        Vev t 0 (zetaE m (P₁.map (Y 0)) (Y 0 ω)) - Zm t ω‖ₑ) (hRc.enorm.mono hsub) ht
    refine h1.trans (le_of_eq ?_)
    exact iSup_congr fun t => iSup_congr fun hq => (hω t hq).symm

end HRS.MD.EQBurnBurn

end
