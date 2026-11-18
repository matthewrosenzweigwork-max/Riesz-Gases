import HRS.MS.SA12DensCc

/-!
# S.A.12 L2: density of `C_c^∞` in the `ℓ¹(L²)` cell norm
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd

variable {d : ℕ}

/-- The local `L²` norm on the fine-lattice unit ball at `z`. -/
def sa12x_cn (g : Euc d → ℝ) (z : Fin d → ℤ) : ℝ≥0∞ :=
  eLpNorm g 2 (volume.restrict (Metric.ball (cellPt d z) 1))

theorem sa12x_cn_eq {g : Euc d → ℝ} (hg : AEStronglyMeasurable g volume) (z : Fin d → ℤ) :
    (∫⁻ x in Metric.ball (cellPt d z) 1, ENNReal.ofReal (g x ^ 2)) ^ (1 / 2 : ℝ) = sa12x_cn g z := by
  unfold sa12x_cn
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp) hg.restrict]
  simp only [ENNReal.toReal_ofNat]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]

theorem sa12x_cellL2Sum_eq {g : Euc d → ℝ} (hg : AEStronglyMeasurable g volume) : cellL2Sum g = ∑' z, sa12x_cn g z := by
  unfold cellL2Sum
  exact tsum_congr fun z => sa12x_cn_eq hg z

theorem sa12x_cn_add_le (g h : Euc d → ℝ) (z : Fin d → ℤ) :
    sa12x_cn (g + h) z ≤ sa12x_cn g z + sa12x_cn h z :=
  eLpNorm_add_le (by norm_num)

theorem sa12x_cn_zero_of {h : Euc d → ℝ} (z : Fin d → ℤ)
    (hz : ∀ x ∈ Metric.ball (cellPt d z) 1, h x = 0) : sa12x_cn h z = 0 := by
  unfold sa12x_cn
  have : h =ᵐ[volume.restrict (Metric.ball (cellPt d z) 1)] 0 :=
    (ae_restrict_iff' Metric.isOpen_ball.measurableSet).2 (Filter.Eventually.of_forall hz)
  rw [eLpNorm_congr_ae this]; simp

theorem sa12x_cn_le_global (h : Euc d → ℝ) (z : Fin d → ℤ) :
    sa12x_cn h z ≤ eLpNorm h 2 volume :=
  eLpNorm_restrict_le h 2 volume _

theorem sa12x_cn_mono {g h : Euc d → ℝ} (hg : AEStronglyMeasurable g volume) (z : Fin d → ℤ)
    (hz : ∀ x ∈ Metric.ball (cellPt d z) 1, ‖g x‖ ≤ ‖h x‖) : sa12x_cn g z ≤ sa12x_cn h z := by
  unfold sa12x_cn
  refine eLpNorm_mono_ae hg.restrict ?_
  exact (ae_restrict_iff' Metric.isOpen_ball.measurableSet).2 (Filter.Eventually.of_forall hz)

-- BEGIN SA12.L2
theorem cell_test_density (hd : 1 ≤ d) (g : Euc d → ℝ)
    (hg : AEStronglyMeasurable g volume) (hgf : cellL2Sum g < ⊤) :
    ∀ ε : ℝ, 0 < ε → ∃ ψ : Euc d → ℝ, IsCcInfty ψ ∧
      cellL2Sum (fun x => g x - ψ x) ≤ ENNReal.ofReal ε := by
  intro ε hε
  have hsum : ∑' z, sa12x_cn g z ≠ ⊤ := by
    rw [← sa12x_cellL2Sum_eq hg]; exact hgf.ne
  have hcnfin : ∀ z, sa12x_cn g z < ⊤ := fun z =>
    (ENNReal.le_tsum z).trans_lt (lt_top_iff_ne_top.2 hsum)
  have hε2 : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.2 (half_pos hε)
  obtain ⟨S, hS⟩ := ((ENNReal.tendsto_tsum_compl_atTop_zero hsum).eventually
    (gt_mem_nhds hε2)).exists
  set U : Set (Euc d) := ⋃ z : S, Metric.ball (cellPt d (z : Fin d → ℤ)) 1 with hU
  have hUm : MeasurableSet U := MeasurableSet.iUnion fun _ => Metric.isOpen_ball.measurableSet
  set f : Euc d → ℝ := U.indicator g with hf
  have hUfin : ∫⁻ x in U, ‖g x‖ₑ ^ (2 : ℝ) < ⊤ := by
    refine (lintegral_iUnion_le _ _).trans_lt ?_
    rw [tsum_fintype]
    refine ENNReal.sum_lt_top.2 fun z _ => ?_
    have := hcnfin (z : Fin d → ℤ)
    unfold sa12x_cn at this
    have h2 := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := 2) (by norm_num) (by simp)
      (μ := volume.restrict (Metric.ball (cellPt d (z : Fin d → ℤ)) 1)) (f := g) hg.restrict).1 this
    simpa using h2
  have hfL : MemLp f 2 volume := by
    rw [memLp_iff, hf, eLpNorm_indicator_eq_eLpNorm_restrict hUm,
      eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by simp) hg.restrict]
    simpa using hUfin
  set R0 : ℝ := 1 + ∑ z ∈ S, (‖cellPt d z‖ + 1) with hR0
  have hR0pos : 0 < R0 := by
    have : 0 ≤ ∑ z ∈ S, (‖cellPt d z‖ + 1) :=
      Finset.sum_nonneg fun z _ => by positivity
    linarith
  have hBsub : ∀ z ∈ S, ∀ x ∈ Metric.ball (cellPt d z) 1, ‖x‖ < R0 := by
    intro z hz x hx
    have h1 : ‖x‖ < ‖cellPt d z‖ + 1 := by
      have := norm_le_norm_add_norm_sub' x (cellPt d z)
      rw [Metric.mem_ball, dist_eq_norm] at hx
      have h3 : ‖x‖ ≤ ‖cellPt d z‖ + ‖x - cellPt d z‖ := by
        calc ‖x‖ = ‖cellPt d z + (x - cellPt d z)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      linarith
    have h2 : ‖cellPt d z‖ + 1 ≤ ∑ z ∈ S, (‖cellPt d z‖ + 1) :=
      Finset.single_le_sum (f := fun z => ‖cellPt d z‖ + 1) (fun z _ => by positivity) hz
    linarith
  have hf0 : ∀ x, R0 < ‖x‖ → f x = 0 := by
    intro x hx
    rw [hf]
    refine Set.indicator_of_notMem ?_ _
    intro hxU
    obtain ⟨z, hz⟩ := Set.mem_iUnion.1 hxU
    have := hBsub z z.2 x hz
    linarith
  have hfn : Set.Finite {z : Fin d → ℤ | ‖cellPt d z‖ ≤ R0 + 3} :=
    HRS.MH.AdjointRd.Phase2SA12Construction.sa12c12_finite_cells hd _
  set N : Finset (Fin d → ℤ) := hfn.toFinset with hN
  set δ : ℝ := ε / (2 * ((N.card : ℝ) + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨ψ, hψ1, hψ2, hψ3, hψ4⟩ := sa12x_cc_approx hfL R0 hR0pos hf0 hδpos
  refine ⟨ψ, ⟨hψ1, hψ2⟩, ?_⟩
  have hψm : AEStronglyMeasurable ψ volume := hψ1.continuous.aestronglyMeasurable
  have hfm : AEStronglyMeasurable f volume := hfL.aestronglyMeasurable
  have hsplit : (fun x => g x - ψ x) = (fun x => g x - f x) + (fun x => f x - ψ x) := by
    funext x; simp
  have hA0 : ∀ z ∈ S, sa12x_cn (fun x => g x - f x) z = 0 := by
    intro z hz
    refine sa12x_cn_zero_of z fun x hx => ?_
    have hxU : x ∈ U := Set.mem_iUnion.2 ⟨⟨z, hz⟩, hx⟩
    simp [hf, Set.indicator_of_mem hxU]
  have hAle : ∀ z, sa12x_cn (fun x => g x - f x) z ≤ sa12x_cn g z := by
    intro z
    refine sa12x_cn_mono (hg.sub hfm) z fun x _ => ?_
    by_cases hxU : x ∈ U
    · simp [hf, Set.indicator_of_mem hxU]
    · simp [hf, Set.indicator_of_notMem hxU]
  have hB0 : ∀ z ∉ N, sa12x_cn (fun x => f x - ψ x) z = 0 := by
    intro z hz
    have hz' : R0 + 3 < ‖cellPt d z‖ := by
      by_contra h
      exact hz (hfn.mem_toFinset.2 (not_lt.1 h))
    refine sa12x_cn_zero_of z fun x hx => ?_
    have hxn : R0 + 2 < ‖x‖ := by
      rw [Metric.mem_ball, dist_eq_norm] at hx
      have : ‖cellPt d z‖ ≤ ‖x‖ + ‖cellPt d z - x‖ := by
        calc ‖cellPt d z‖ = ‖x + (cellPt d z - x)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      rw [norm_sub_rev] at this
      linarith
    have h1 : f x = 0 := hf0 x (by linarith)
    have h2 : ψ x = 0 := by
      by_contra h
      have := hψ3 (subset_tsupport _ (Function.mem_support.2 h))
      rw [mem_closedBall_zero_iff] at this
      linarith
    simp [h1, h2]
  have hBle : ∀ z, sa12x_cn (fun x => f x - ψ x) z ≤ ENNReal.ofReal δ := fun z =>
    (sa12x_cn_le_global _ z).trans (by exact hψ4)
  have hgψ : AEStronglyMeasurable (fun x => g x - ψ x) volume := hg.sub hψm
  rw [sa12x_cellL2Sum_eq hgψ, hsplit]
  calc ∑' z, sa12x_cn ((fun x => g x - f x) + (fun x => f x - ψ x)) z
      ≤ ∑' z, (sa12x_cn (fun x => g x - f x) z + sa12x_cn (fun x => f x - ψ x) z) :=
        ENNReal.tsum_le_tsum fun z => sa12x_cn_add_le _ _ z
    _ = ∑' z, sa12x_cn (fun x => g x - f x) z + ∑' z, sa12x_cn (fun x => f x - ψ x) z :=
        ENNReal.tsum_add
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
        gcongr
        · have hsupp : Function.support (fun z => sa12x_cn (fun x => g x - f x) z) ⊆
              {z : Fin d → ℤ | z ∉ S} := fun z hz hzS => hz (hA0 z hzS)
          rw [← tsum_subtype_eq_of_support_subset hsupp]
          exact le_trans (ENNReal.tsum_le_tsum fun z => hAle z) hS.le
        · rw [tsum_eq_sum (s := N) fun z hz => hB0 z hz]
          calc ∑ z ∈ N, sa12x_cn (fun x => f x - ψ x) z ≤ ∑ z ∈ N, ENNReal.ofReal δ :=
                Finset.sum_le_sum fun z _ => hBle z
            _ = ENNReal.ofReal (N.card * δ) := by
                rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity)]
                simp
            _ ≤ ENNReal.ofReal (ε / 2) := by
                refine ENNReal.ofReal_le_ofReal ?_
                rw [hδ, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
                nlinarith [hε, (Nat.cast_nonneg N.card : (0 : ℝ) ≤ N.card)]
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
-- END SA12.L2

end HRS.MH.AdjointRd.Phase2SA12Limit
