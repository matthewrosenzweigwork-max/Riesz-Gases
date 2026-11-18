import HRS.MS.R26T8AD00
import HRS.MS.S82WK6

/-!
# S8.2 observed-time layer, packet T8A.G0 (adapter for T8A G00, G01)

* `r26t8a_gibbs_pole_moments_adapter` (T8A G00): the polynomial-pole envelope `configPoleEnvelope M = u4Env M M` is in `L²(canonicalP)`
  and the collision set is null (merged `u4_env_L2`, `u4_P_coll`).
* `r26t8a_graph_cutoffs_C2` (T8A G01, **C² instead of C^∞**: the merged cut-off `wTheta` is `C²` only, which is all the local
  time-dependent Itô formula needs): spatial and collision cut-offs, compactly supported off collisions, `0 ≤ θ ≤ 1`, equal to `1`
  near every collision-free configuration for large `n`, with first two derivatives bounded by `C · configPoleEnvelope M` uniformly in `n`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_gibbs_pole_moments_adapter (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N)
    (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (M : ℝ) (hM : 0 ≤ M) :
    MemLp (r26t8a_configPoleEnvelope (d := d) (N := N) M) 2 (canonicalP d N a beta) ∧
    (canonicalP d N a beta) (eucCollisionSet d N) = 0 := by
  haveI := HRS.MS.S82U.u4_prob (N := N) hd ha hbeta
  refine ⟨?_, HRS.MS.S82U.u4_P_coll hd N a beta⟩
  have hmeas : Measurable (fun X : EucConfig d N => HRS.MS.S82U.u4Env M M X) := by
    unfold HRS.MS.S82U.u4Env
    fun_prop
  exact (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2
    (HRS.MS.S82U.u4_env_L2 hd (by omega) ha hbeta hM hM)

theorem r26t8a_graph_cutoffs_C2 (d N : ℕ) :
    ∃ theta : ℕ → EucConfig d N → ℝ,
      (∀ n, ContDiff ℝ 2 (theta n) ∧ HasCompactSupport (theta n) ∧
        tsupport (theta n) ⊆ (eucCollisionSet d N)ᶜ) ∧
      (∀ n X, 0 ≤ theta n X ∧ theta n X ≤ 1) ∧
      (∀ X, X ∉ eucCollisionSet d N → ∀ᶠ n in atTop,
        theta n =ᶠ[𝓝 X] (fun _ => 1)) ∧
      ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ n X, X ∉ eucCollisionSet d N →
        ‖fderiv ℝ (theta n) X‖ + ‖iteratedFDeriv ℝ 2 (theta n) X‖ ≤
          C * r26t8a_configPoleEnvelope M X := by
  refine ⟨fun n => HRS.MS.S82W.wTheta d N ((n : ℝ) + 1), ?_, ?_, ?_, ?_⟩
  · intro n
    have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact ⟨HRS.MS.S82W.wTheta_contDiff _, HRS.MS.S82W.wTheta_hasCompactSupport hm,
      HRS.MS.S82W.wTheta_tsupport.trans HRS.MS.S82W.wS_subset_compl⟩
  · intro n X; exact HRS.MS.S82W.wTheta_01 _ X
  · intro X hX
    filter_upwards [HRS.MS.S82W.wTheta_eventually_one hX] with n hn
    filter_upwards [hn] with Y hY using hY
  · obtain ⟨C1, p1, q1, hC1, hp1, hq1, h1⟩ := (HRS.MS.S82W.wT1_tame (d := d) (N := N))
    obtain ⟨C2, p2, q2, hC2, hp2, hq2, h2⟩ := (HRS.MS.S82W.wT2_tame (d := d) (N := N))
    set M : ℝ := max (max p1 p2) (max q1 q2) with hMdef
    have hM0 : 0 ≤ M := le_max_of_le_left (le_max_of_le_left hp1)
    set K : ℝ := ∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, (2 : ℝ) with hK
    have hK0 : 0 ≤ K := Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => by norm_num
    refine ⟨(C1 + C2) * K, M, by positivity, hM0, ?_⟩
    intro n X hX
    have hm : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    obtain ⟨j1, j2⟩ := HRS.MS.S82W.wTheta_jets (d := d) (N := N) hm hX
    have hn : ‖iteratedFDeriv ℝ 2 (HRS.MS.S82W.wTheta d N ((n : ℝ) + 1)) X‖ =
        ‖fderiv ℝ (fderiv ℝ (HRS.MS.S82W.wTheta d N ((n : ℝ) + 1))) X‖ := by
      have e := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := HRS.MS.S82W.wTheta d N ((n : ℝ) + 1))
        (x := X) (n := 1)
      rw [norm_iteratedFDeriv_one] at e
      exact e.symm
    have a1 : HRS.MS.S82W.wT1 X ≤ C1 * (K * HRS.MS.S82U.u4Env M M X) := by
      refine (le_abs_self _).trans ((h1 X hX).trans ?_)
      refine mul_le_mul_of_nonneg_left ?_ hC1
      exact HRS.MS.S82U.u4Env_mono hp1 (le_trans (le_max_left _ _) (le_max_left _ _)) hq1
        (le_trans (le_max_left _ _) (le_max_right _ _)) X hX
    have a2 : HRS.MS.S82W.wT2 X ≤ C2 * (K * HRS.MS.S82U.u4Env M M X) := by
      refine (le_abs_self _).trans ((h2 X hX).trans ?_)
      refine mul_le_mul_of_nonneg_left ?_ hC2
      exact HRS.MS.S82U.u4Env_mono hp2 (le_trans (le_max_right _ _) (le_max_left _ _)) hq2
        (le_trans (le_max_right _ _) (le_max_right _ _)) X hX
    rw [hn]
    show _ ≤ (C1 + C2) * K * HRS.MS.S82U.u4Env M M X
    nlinarith [j1, j2, a1, a2]

end HRS.MS.R26T8A

end
