import HRS.MS.R26T8AB07b2

/-!
# S8.2 observed-time layer, packet T8A.B07b3: dominated-convergence core and continuity of the pole envelope

(i) For a continuous path `x` through an open-ish region `U`, a family `Ψ v y` measurable in `y`, continuous in `v ≥ 0`
and dominated by `B * env y` with `env` continuous on `U`, the maps `t ↦ ∫_{lo}^{hi t} Ψ(a0+t-r)(x r) dr` are continuous
on `[0,T]` (moving upper endpoint included).
(ii) The configuration pole envelope is continuous off collisions.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_b07b3_core {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (x : ℝ → E) (hx : Continuous x) (U : Set E) (hU : MeasurableSet U) (H : ℝ)
    (hxU : ∀ r ∈ Set.Icc (0 : ℝ) H, x r ∈ U)
    (env : E → ℝ) (henv : ContinuousOn env U) (hnn : ∀ y ∈ U, 0 ≤ env y)
    (Ψ : ℝ → E → ℝ) (hmeas : ∀ v, Measurable (Ψ v))
    (hcont : ∀ y ∈ U, ∀ v0 : ℝ, 0 ≤ v0 → ContinuousWithinAt (fun v => Ψ v y) (Set.Ici 0) v0)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ v ∈ Set.Icc (0 : ℝ) H, ∀ y ∈ U, |Ψ v y| ≤ B * env y)
    (T a0 lo : ℝ) (hT : 0 ≤ T) (ha0 : 0 ≤ a0) (hH : H = a0 + T) (hlo : 0 ≤ lo) (hi : ℝ → ℝ)
    (hhi : Continuous hi) (hhiH : ∀ t ∈ Set.Icc (0 : ℝ) T, hi t ≤ a0 + t) :
    ContinuousOn (fun t => ∫ r in Set.Icc lo (hi t), Ψ (a0 + t - r) (x r)) (Set.Icc 0 T) := by
  classical
  have hHnn : 0 ≤ H := by rw [hH]; linarith
  -- bound along the path
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := H)).bddAbove_image
    (henv.comp hx.continuousOn hxU)
  have hMb : ∀ r ∈ Set.Icc (0 : ℝ) H, env (x r) ≤ M := fun r hr => hM ⟨r, hr, rfl⟩
  have hM0 : 0 ≤ M := (hnn _ (hxU 0 ⟨le_rfl, hHnn⟩)).trans (hMb 0 ⟨le_rfl, hHnn⟩)
  -- the Carathéodory regularisation
  set u : ℝ → E → ℝ := fun v y => if y ∈ U then Ψ (max v 0) y else 0 with hu
  have hucont : ∀ y, Continuous fun v => u v y := fun y => by
    by_cases hy : y ∈ U
    · have : (fun v => u v y) = fun v => Ψ (max v 0) y := by
        funext v; simp [hu, hy]
      rw [this, continuous_iff_continuousAt]
      intro v1
      exact (hcont y hy (max v1 0) (le_max_right _ _)).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨((continuous_id.max continuous_const).tendsto v1),
          Eventually.of_forall fun v => le_max_right v 0⟩)
    · have : (fun v => u v y) = fun _ => 0 := by funext v; simp [hu, hy]
      rw [this]; exact continuous_const
  have humeas : ∀ v, Measurable (u v) := fun v => Measurable.ite hU (hmeas _) measurable_const
  have huj : Measurable (Function.uncurry u) := measurable_uncurry_of_continuous_of_measurable hucont humeas
  have hgm : ∀ t : ℝ, Measurable fun r => u (a0 + t - r) (x r) := fun t =>
    huj.comp ((measurable_const.sub measurable_id).prodMk hx.measurable)
  set μ : Measure ℝ := volume.restrict (Set.Icc 0 H) with hμ
  set F : ℝ → ℝ → ℝ := fun t r => (Set.Icc lo (hi t)).indicator (fun r => u (a0 + t - r) (x r)) r with hF
  have heq : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ r in Set.Icc lo (hi t), Ψ (a0 + t - r) (x r) =
      ∫ r, F t r ∂μ := by
    intro t ht
    have hsub : Set.Icc lo (hi t) ⊆ Set.Icc 0 H := fun r hr =>
      ⟨hlo.trans hr.1, by linarith [hr.2, hhiH t ht, ht.2]⟩
    have h1 : ∫ r in Set.Icc lo (hi t), Ψ (a0 + t - r) (x r) =
        ∫ r in Set.Icc lo (hi t), u (a0 + t - r) (x r) := by
      refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
      have hrU := hxU r (hsub hr)
      have hv : 0 ≤ a0 + t - r := by linarith [hr.2, hhiH t ht]
      simp [hu, hrU, max_eq_left hv]
    rw [h1, hF, integral_indicator measurableSet_Icc, hμ, Measure.restrict_restrict measurableSet_Icc,
      Set.inter_eq_left.2 hsub]
  have hcw : ∀ t0 ∈ Set.Icc (0 : ℝ) T,
      ContinuousWithinAt (fun t => ∫ r, F t r ∂μ) (Set.Icc 0 T) t0 := by
    intro t0 ht0
    refine continuousWithinAt_of_dominated (bound := fun _ => B * M) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun t =>
        ((hgm t).indicator measurableSet_Icc).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with t ht
      refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => ?_)
      by_cases hrs : r ∈ Set.Icc lo (hi t)
      · have hv0 : 0 ≤ a0 + t - r := by linarith [hrs.2, hhiH t ht]
        have hvH : a0 + t - r ≤ H := by linarith [hrs.1, ht.2]
        have hrU := hxU r ⟨hlo.trans hrs.1, by linarith [hrs.2, hhiH t ht, ht.2]⟩
        simp only [hF, Set.indicator_of_mem hrs, hu, if_pos hrU, max_eq_left hv0, Real.norm_eq_abs]
        exact (hB _ ⟨hv0, hvH⟩ _ hrU).trans (mul_le_mul_of_nonneg_left (hMb r hr) hB0)
      · simp only [hF, Set.indicator_of_notMem hrs, norm_zero]
        exact mul_nonneg hB0 hM0
    · exact integrable_const _
    · have hne : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ hi t0 := by rw [ae_iff]; simp
      filter_upwards [ae_restrict_of_ae hne] with r hr
      by_cases h1 : r < lo
      · have : (fun t => F t r) = fun _ => 0 := by
          funext t
          simp only [hF]
          exact Set.indicator_of_notMem (fun h => absurd h.1 (not_le.2 h1)) _
        rw [this]; exact continuousWithinAt_const
      · by_cases h2 : hi t0 < r
        · have hev : ∀ᶠ t in 𝓝 t0, hi t < r := (hhi.continuousAt (x := t0)).eventually (gt_mem_nhds h2)
          refine (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq ?_ ?_
          · filter_upwards [nhdsWithin_le_nhds hev] with t ht
            simp only [hF]
            exact Set.indicator_of_notMem (fun h => absurd h.2 (not_le.2 ht)) _
          · simp only [hF]
            exact Set.indicator_of_notMem (fun h => absurd h.2 (not_le.2 h2)) _
        · have h3 : r < hi t0 := lt_of_le_of_ne (not_lt.1 h2) hr
          have hev : ∀ᶠ t in 𝓝 t0, r < hi t := (hhi.continuousAt (x := t0)).eventually (lt_mem_nhds h3)
          have hc : Continuous fun t : ℝ => u (a0 + t - r) (x r) :=
            (hucont (x r)).comp ((continuous_const.add continuous_id).sub continuous_const)
          refine hc.continuousWithinAt.congr_of_eventuallyEq ?_ ?_
          · filter_upwards [nhdsWithin_le_nhds hev] with t ht
            simp only [hF]
            exact Set.indicator_of_mem (show r ∈ Set.Icc lo (hi t) from ⟨not_lt.1 h1, ht.le⟩) _
          · simp only [hF]
            exact Set.indicator_of_mem (show r ∈ Set.Icc lo (hi t0) from ⟨not_lt.1 h1, h3.le⟩) _
  intro t0 ht0
  exact (hcw t0 ht0).congr (fun t ht => heq t ht) (heq t0 ht0)

theorem r26t8a_b07b3_env_cont (d N : ℕ) (s : ℝ) :
    ContinuousOn (r26t8a_configPoleEnvelope (d := d) (N := N) s) (eucCollisionSet d N)ᶜ := by
  show ContinuousOn (fun X : EucConfig d N => (1 + ‖X‖) ^ s *
    ∏ i, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-s))) _
  refine ContinuousOn.mul ?_ (continuousOn_finsetProd _ fun i _ =>
    continuousOn_finsetProd _ fun j hj => ?_)
  · exact ((continuous_const.add continuous_norm).continuousOn).rpow_const
      (fun Y _ => Or.inl (by show (1 : ℝ) + ‖Y‖ ≠ 0; positivity))
  · have hji : j ≠ i := (Finset.mem_erase.1 hj).1
    refine continuousOn_const.add (((continuous_apply i |>.sub (continuous_apply j)).norm
      |>.continuousOn).rpow_const fun Y hY => Or.inl ?_)
    exact norm_ne_zero_iff.2 (sub_ne_zero.2 fun h => hY ⟨i, j, hji.symm, h⟩)

end HRS.MS.R26T8A
