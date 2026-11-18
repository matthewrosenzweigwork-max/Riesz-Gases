import HRS.MS.SA12V3R

/-!
# S.A.12 C2 (SA12V3 worker), part S: regularity of the periodic initial datum

`φ` with `ulocNormE m χ φ < ⊤` is locally integrable; `mollify η ε φ` is smooth; `perL L g` is smooth for smooth `g`
supported in `‖y‖ < L/3`; a smooth `L`-periodic function has bounded jets.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Pointwise

namespace HRS.MH.AdjointRd.Phase2SA12V3

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12v3_locInt_of_uloc {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) {m : ℕ} {φ : Euc d → ℝ}
    (hφ : ulocNormE m χ φ < ⊤) : LocallyIntegrable φ volume := by
  intro x
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, ?_⟩
  have h1 : sobolevNormE (m : ℝ) (fun y => χ (y - x) * φ y) < ⊤ :=
    lt_of_le_of_lt (le_iSup (fun z : Euc d => sobolevNormE (m : ℝ) fun y => χ (y - z) * φ y) x) hφ
  have hmem : HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) (fun y => χ (y - x) * φ y) := by
    by_contra h
    simp [sobolevNormE, h] at h1
  haveI : IsFiniteMeasure ((volume : Measure (Euc d)).restrict (Metric.ball x 1)) :=
    ⟨by simpa using measure_ball_lt_top (x := x) (r := 1)⟩
  have h2 : Integrable (fun y => χ (y - x) * φ y) ((volume : Measure (Euc d)).restrict (Metric.ball x 1)) :=
    (hmem.1.restrict (Metric.ball x 1)).integrable (by norm_num)
  refine h2.congr ?_
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with y hy
  have : χ (y - x) = 1 := by
    apply hχ.2.2.2.2
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [Metric.mem_ball, dist_eq_norm] at hy
    exact hy.le
  simp [this]

theorem sa12v3_mollify_eq_H (η : Euc d → ℝ) (ε : ℝ) (φ : Euc d → ℝ) :
    mollify η ε φ = sa12vH φ (sa12v3_G η ε) := by
  funext x
  unfold mollify sa12vH sa12v3_G
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  ring

theorem sa12v3_mollify_smooth {η : Euc d → ℝ} (hη : IsMollifier η) {ε : ℝ} (hε : 0 < ε) {φ : Euc d → ℝ}
    (hφ : LocallyIntegrable φ volume) : ContDiff ℝ ∞ (mollify η ε φ) := by
  rw [sa12v3_mollify_eq_H]
  refine sa12v_H_smooth hφ ?_ ?_
  · exact contDiff_const.mul (hη.1.comp (contDiff_const_smul _))
  · exact (hη.2.1.comp_smul (inv_ne_zero hε.ne')).mul_left

theorem sa12v3_perL_smooth {L : ℝ} (hL : 0 < L) {g : Euc d → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgs : ∀ y : Euc d, L / 3 ≤ ‖y‖ → g y = 0) : ContDiff ℝ ∞ (perL L g) := by
  obtain ⟨χ, hχ⟩ := HRS.MS.Ul.ul0_exists_ulocCutoff d
  rw [contDiff_iff_contDiffAt]
  intro x₀
  obtain ⟨B, hB, -⟩ := sa12v3_box_card L hL x₀ (2 + L / 3) (by positivity)
  classical
  set K : Finset (Fin d → ℤ) := B with hKdef
  have hK : ∀ z : Fin d → ℤ, ‖L • latticePt z - x₀‖ < 2 + L / 3 → z ∈ K := by
    intro z hz'
    refine hB z fun i => ?_
    have h1 := PiLp.norm_apply_le (L • latticePt z - x₀) i
    have e : (L • latticePt z - x₀) i = L * (z i : ℝ) - x₀ i := by simp [latticePt]
    rw [e, Real.norm_eq_abs] at h1
    exact h1.trans hz'.le
  have hfun := sa12v3_perL_cell_fun hχ hL hgs x₀ K hK
  have hev : perL L g =ᶠ[𝓝 x₀] fun x => ∑ z ∈ K, g (x - L • latticePt z) := by
    have : {x : Euc d | ‖x - x₀‖ < 1} ∈ 𝓝 x₀ := by
      have := Metric.ball_mem_nhds x₀ one_pos
      simpa [Metric.ball, dist_eq_norm] using this
    filter_upwards [this] with x hx
    have h1 := congrFun hfun x
    have : χ (x - x₀) = 1 := by
      apply hχ.2.2.2.2
      rw [Metric.mem_closedBall, dist_zero_right]; exact (show ‖x - x₀‖ < 1 from hx).le
    simp only [this, one_mul] at h1
    exact h1
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  exact (ContDiff.sum fun z _ => hg.comp (contDiff_id.sub contDiff_const)).contDiffAt

theorem sa12v3_bddJets_of_periodic {L : ℝ} (hL : 0 < L) {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f)
    (hper : ∀ (x : Euc d) (k : Fin d → ℤ), f (x + L • latticePt k) = f x) (m : ℕ) : BddJets m f := by
  refine ⟨hf, fun j _ idx => ?_⟩
  set F : Euc d → ℝ := partialDeriv idx f with hF
  have hFc : Continuous F := by
    have := (hf.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top))
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ
      (fun l => EuclideanSpace.single (idx l) (1 : ℝ))).continuous.comp this
  have hFp : ∀ (x : Euc d) (k : Fin d → ℤ), F (x + L • latticePt k) = F x := by
    intro x k
    have h1 : (fun y => f (y + L • latticePt k)) = f := funext fun y => hper y k
    have h2 := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := f) j (L • latticePt k) (x := x)
    rw [h1] at h2
    simp only [hF, partialDeriv]
    rw [← h2]
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Euc d) (Real.sqrt (d * (L / 2) ^ 2))).exists_bound_of_continuousOn
    hFc.continuousOn
  refine ⟨C, fun x => ?_⟩
  obtain ⟨k, hk⟩ := sa12v3_reduce hL x
  have hmem : x - L • latticePt k ∈ Metric.closedBall (0 : Euc d) (Real.sqrt (d * (L / 2) ^ 2)) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact sa12v3_norm_le_of_coord hk
  have := hC _ hmem
  have e : F x = F (x - L • latticePt k) := by
    have := hFp (x - L • latticePt k) k
    rw [sub_add_cancel] at this
    exact this
  rw [e]
  simpa [Real.norm_eq_abs] using this

end HRS.MH.AdjointRd.Phase2SA12V3
