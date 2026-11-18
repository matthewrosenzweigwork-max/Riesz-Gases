import HRS.MS.UniqM2Loc

/-!
# M2 of `UniqPlan.md`, part 3: the weak gradient of `u` with `ulocNormE 1 χ u ≤ B`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqM2

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqM1

variable {d : ℕ}

/-- The weak gradient of the cut-off function `χ(·-c) u`, tested against functions supported
in `closedBall c 1` (where the cutoff is `1`). -/
theorem local_weakGrad {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) {u : Euc d → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hu : ulocNormE 1 χ u ≤ ENNReal.ofReal B) (c : Euc d) :
    ∃ V : Fin d → Euc d → ℝ, (∀ j, Measurable (V j)) ∧ (∀ j, MemLp (V j) 2 volume) ∧
      ∑ j, ∫ x, V j x ^ 2 ≤ B ^ 2 ∧
      ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ closedBall c 1 →
        ∀ j : Fin d, ∫ x, u x * fderiv ℝ ψ x (EuclideanSpace.single j 1) = - ∫ x, V j x * ψ x := by
  have h1 : sobolevNormE (1 : ℝ) (fun x => χ (x - c) * u x) ≤ ENNReal.ofReal B := by
    have := (le_iSup (fun z : Euc d => sobolevNormE ((1 : ℕ) : ℝ) fun x => χ (x - z) * u x) c).trans hu
    simpa using this
  obtain ⟨hmem, hsq⟩ := memSobolev_of_sobolevNormE_le hB h1
  obtain ⟨V, hVm, hVl, hVb, hVid⟩ := weakGrad_of_memSobolev hmem
  refine ⟨V, hVm, hVl, hVb.trans hsq, fun ψ hψ hc hs j => ?_⟩
  rw [← hVid ψ hψ hc j]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  beta_reduce
  by_cases hx : x ∈ closedBall c 1
  · rw [hχ.2.2.2.2 (x - c) (by simpa [dist_eq_norm] using hx), one_mul]
  · have : x ∉ tsupport ψ := fun h => hx (hs h)
    simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) this]


theorem LocMass.of_norm_le {B : ℝ} {f g : Euc d → ℝ} (hg : LocMass B g)
    (hf : AEStronglyMeasurable f volume) (h : ∀ x, ‖f x‖ ≤ ‖g x‖) : LocMass B f := by
  refine ⟨hf, fun c => le_trans (lintegral_mono fun y => ?_) (hg.2 c)⟩
  have : ‖f y‖ₑ ≤ ‖g y‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (h y)
  gcongr

/-- **Weak gradient of `u` with `ulocNormE 1 χ u ≤ B`.**  There is a measurable `v : ℝ^d → ℝ^d` with
`∫ u ∂_jψ = -∫ v_j ψ` for every `C_c^∞` function `ψ` and every direction `j`, and with
`∫_{ball c 1} ‖v‖² ≤ B²` for every centre `c`. -/
theorem exists_weakGrad {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) {u : Euc d → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hu : ulocNormE 1 χ u ≤ ENNReal.ofReal B) :
    ∃ v : Euc d → Euc d, Measurable v ∧
      (∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∀ j : Fin d,
        ∫ x, u x * fderiv ℝ ψ x (EuclideanSpace.single j 1) = - ∫ x, v x j * ψ x) ∧
      LocMass B (fun x => ‖v x‖) := by
  have hLu : LocMass B u := locMass_of_ulocNormE (m := 1) hχ hB hu
  choose V hVm hVl hVb hVid using local_weakGrad hχ hB hu
  classical
  set cn : ℕ → Euc d := TopologicalSpace.denseSeq (Euc d) with hcn
  have hex : ∀ x : Euc d, ∃ n, x ∈ ball (cn n) 1 := fun x => by
    obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq (Euc d)).exists_dist_lt x one_pos
    exact ⟨n, by rw [mem_ball]; exact hn⟩
  have hVli : ∀ c j, LocallyIntegrable (V c j) volume := fun c j =>
    (hVl c j).locallyIntegrable (by norm_num)
  set vj : Fin d → Euc d → ℝ := fun j x => V (cn (Nat.find (hex x))) j x with hvj
  have hvj_meas : ∀ j, Measurable (vj j) := fun j =>
    Measurable.find (f := fun n x => V (cn n) j x) (p := fun n x => x ∈ ball (cn n) 1)
      (fun n => hVm _ j) (fun n => measurableSet_ball) hex
  -- agreement with the local gradients
  have hG1 : ∀ c : Euc d, ∀ᵐ x, x ∈ ball c 1 → ∀ j, vj j x = V c j x := by
    intro c
    have key : ∀ n j, ∀ᵐ x, x ∈ ball (cn n) 1 ∩ ball c 1 → V (cn n) j x = V c j x := fun n j =>
      ae_eq_of_local (u := u) (EuclideanSpace.single j 1) (hVli _ j) (hVli _ j)
        (fun ψ hψ hc hs => hVid (cn n) ψ hψ hc hs j) (fun ψ hψ hc hs => hVid c ψ hψ hc hs j)
    have := ae_all_iff.2 fun n => ae_all_iff.2 fun j => key n j
    filter_upwards [this] with x hx hxc j
    exact hx (Nat.find (hex x)) j ⟨Nat.find_spec (hex x), hxc⟩
  set v : Euc d → Euc d := fun x => WithLp.toLp 2 (fun j => vj j x) with hv
  have hv_meas : Measurable v :=
    (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp (measurable_pi_iff.2 hvj_meas)
  have hnorm : ∀ x, ‖v x‖ ^ 2 = ∑ j, vj j x ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_sq_eq]
    simp [hv]
  have hLM : LocMass B (fun x => ‖v x‖) := by
    refine ⟨hv_meas.norm.aestronglyMeasurable, fun c => ?_⟩
    have hint : Integrable (fun y => ∑ j, V c j y ^ 2) volume :=
      integrable_finsetSum _ fun j _ => (hVl c j).integrable_sq
    calc ∫⁻ y in ball c 1, ‖(‖v y‖)‖ₑ ^ 2 = ∫⁻ y in ball c 1, ENNReal.ofReal (∑ j, V c j y ^ 2) := by
          refine setLIntegral_congr_fun_ae measurableSet_ball ?_
          filter_upwards [hG1 c] with y hy hyb
          rw [enorm_sq_eq, hnorm]
          congr 1
          exact Finset.sum_congr rfl fun j _ => by rw [hy hyb j]
      _ ≤ ∫⁻ y, ENNReal.ofReal (∑ j, V c j y ^ 2) := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (∫ y, ∑ j, V c j y ^ 2) :=
          (ofReal_integral_eq_lintegral_ofReal hint
            (Eventually.of_forall fun y => Finset.sum_nonneg fun j _ => sq_nonneg _)).symm
      _ ≤ ENNReal.ofReal (B ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          rw [integral_finsetSum _ fun j _ => (hVl c j).integrable_sq]
          exact hVb c
  refine ⟨v, hv_meas, ?_, hLM⟩
  intro ψ hψ hc j
  have hvjl : LocallyIntegrable (vj j) volume :=
    (LocMass.of_norm_le hLM (hvj_meas j).aestronglyMeasurable (fun x => by
      simpa [hv] using PiLp.norm_apply_le (v x) j)).locallyIntegrable
  refine glue_identity (v := vj j) hLu.locallyIntegrable hvjl (EuclideanSpace.single j 1) ?_ hψ hc
  intro c ψ hψ hc hs
  rw [hVid c ψ hψ hc (hs.trans ball_subset_closedBall) j]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hG1 c] with x hx
  by_cases hxb : x ∈ ball c 1
  · rw [hx hxb j]
  · have : ψ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hxb (hs h)
    simp [this]

end HRS.MS.UniqM2
