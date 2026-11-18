import HRS.MS.MfeConfAux109

/-!
# S.B.1, packet F9 (part 13): Vitali's convergence theorem in the form used for the signed commutator limit

`sb1_vitali`: if `f_M → f` a.e. on a probability space and the family is uniformly integrable in the sense
`∀ ε ∃ L ∀ M, ∫_{|f_M| ≥ L} |f_M| ≤ ε`, then `f` is integrable and `∫ f_M → ∫ f`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MfeConf

theorem sb1_vitali {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ} (hf : ∀ n, Measurable (f n))
    (hui : ∀ ε : ℝ, 0 < ε → ∃ L : ℝ≥0, ∀ n,
      ∫⁻ ω, ({x | L ≤ ‖f n x‖₊}.indicator (fun x => ‖f n x‖ₑ)) ω ∂P ≤ ENNReal.ofReal ε)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) :
    Integrable g P ∧ Tendsto (fun n => ∫ ω, f n ω ∂P) atTop (𝓝 (∫ ω, g ω ∂P)) := by
  have hLp : ∀ n (L : ℝ≥0), eLpNorm ({x | L ≤ ‖f n x‖₊}.indicator (f n)) 1 P =
      ∫⁻ ω, ({x | L ≤ ‖f n x‖₊}.indicator (fun x => ‖f n x‖ₑ)) ω ∂P := by
    intro n L
    rw [eLpNorm_one_eq_lintegral_enorm (((hf n).indicator (measurableSet_le measurable_const (hf n).nnnorm)).aestronglyMeasurable)]
    refine lintegral_congr fun ω => ?_
    by_cases h : ω ∈ {x | L ≤ ‖f n x‖₊}
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  have hUI : UnifIntegrable f 1 P := by
    refine unifIntegrable_of le_rfl ENNReal.one_ne_top (fun n => (hf n).aestronglyMeasurable) fun ε hε => ?_
    by_cases htop : ε = ⊤
    · exact ⟨0, fun n => by rw [htop]; exact le_top⟩
    · obtain ⟨L, hL⟩ := hui ε.toReal (ENNReal.toReal_pos hε.ne' htop)
      refine ⟨L, fun n => ?_⟩
      rw [hLp]
      exact (hL n).trans (by rw [ENNReal.ofReal_toReal htop])
  -- the limit is integrable (Fatou)
  obtain ⟨L1, hL1⟩ := hui 1 one_pos
  have hbd : ∀ n, ∫⁻ ω, ‖f n ω‖ₑ ∂P ≤ (L1 : ℝ≥0∞) + 1 := by
    intro n
    calc ∫⁻ ω, ‖f n ω‖ₑ ∂P ≤ ∫⁻ ω, ((L1 : ℝ≥0∞) + ({x | L1 ≤ ‖f n x‖₊}.indicator (fun x => ‖f n x‖ₑ)) ω) ∂P := by
          refine lintegral_mono fun ω => ?_
          by_cases h : L1 ≤ ‖f n ω‖₊
          · rw [Set.indicator_of_mem (show ω ∈ {x | L1 ≤ ‖f n x‖₊} from h)]
            exact le_add_self
          · rw [Set.indicator_of_notMem (show ω ∉ {x | L1 ≤ ‖f n x‖₊} from h), add_zero]
            push Not at h
            exact (le_of_lt (by simpa using h))
      _ = (L1 : ℝ≥0∞) + ∫⁻ ω, ({x | L1 ≤ ‖f n x‖₊}.indicator (fun x => ‖f n x‖ₑ)) ω ∂P := by
          rw [lintegral_add_left measurable_const]
          simp
      _ ≤ (L1 : ℝ≥0∞) + 1 := by
          gcongr
          exact (hL1 n).trans (by simp)
  have hg1 : ∫⁻ ω, ‖g ω‖ₑ ∂P ≤ liminf (fun n => ∫⁻ ω, ‖f n ω‖ₑ ∂P) atTop := by
    calc ∫⁻ ω, ‖g ω‖ₑ ∂P = ∫⁻ ω, liminf (fun n => ‖f n ω‖ₑ) atTop ∂P :=
          lintegral_congr_ae (by filter_upwards [hae] with x hx using hx.enorm.liminf_eq.symm)
      _ ≤ _ := lintegral_liminf_le fun n => (hf n).enorm
  have hgm : AEStronglyMeasurable g P := aestronglyMeasurable_of_tendsto_ae _ (fun n => (hf n).aestronglyMeasurable) hae
  have hgI : Integrable g P := by
    have hlim : liminf (fun n => ∫⁻ ω, ‖f n ω‖ₑ ∂P) atTop ≤ (L1 : ℝ≥0∞) + 1 :=
      liminf_le_of_le (by isBoundedDefault) fun b hb => by
        obtain ⟨n, hn⟩ := hb.exists
        exact hn.trans (hbd n)
    exact ⟨hgm, lt_of_le_of_lt (hg1.trans hlim) (ENNReal.add_lt_top.2 ⟨ENNReal.coe_lt_top, ENNReal.one_lt_top⟩)⟩
  refine ⟨hgI, ?_⟩
  have hlp := tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top (fun n => (hf n).aestronglyMeasurable)
    (memLp_one_iff_integrable.2 hgI) hUI hae
  have hfI : ∀ n, Integrable (f n) P := by
    intro n
    refine ⟨(hf n).aestronglyMeasurable, lt_of_le_of_lt (hbd n) (ENNReal.add_lt_top.2 ⟨ENNReal.coe_lt_top, ENNReal.one_lt_top⟩)⟩
  refine tendsto_integral_of_L1 g hgI.aestronglyMeasurable (Eventually.of_forall hfI) ?_
  have hlp' : Tendsto (fun n => ∫⁻ ω, ‖f n ω - g ω‖ₑ ∂P) atTop (𝓝 0) := by
    refine hlp.congr fun n => ?_
    exact eLpNorm_one_eq_lintegral_enorm ((hf n).aestronglyMeasurable.sub hgm)
  exact hlp'

end HRS.MS.MfeConf
