import HRS.MS.SA16E1Liou2

/-!
# S.A.16 E1: Liouville preliminaries (integrability, Lipschitz continuity of the columns)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Evolution

section Liou

variable {d : ℕ} {T L : ℝ} {A M : ℝ → Euc d →L[ℝ] Euc d}

theorem e1_A_sum (s : ℝ) (w : Euc d) :
    A s w = ∑ k, w k • A s (EuclideanSpace.single k (1 : ℝ)) := by
  conv_lhs => rw [e1_vec_sum w]
  rw [map_sum]
  simp only [map_smul]

theorem e1_F_meas (hAm : ∀ v : Euc d, AEStronglyMeasurable (fun s => A s v)
      (volume.restrict (Icc (0:ℝ) T)))
    (hMc : ∀ v : Euc d, ContinuousOn (fun s => M s v) (Icc (0:ℝ) T)) (v : Euc d) :
    AEStronglyMeasurable (fun s => A s (M s v)) (volume.restrict (Icc (0:ℝ) T)) := by
  have e : (fun s => A s (M s v)) = fun s => ∑ k, (M s v) k • A s (EuclideanSpace.single k (1:ℝ)) := by
    funext s; exact e1_A_sum s (M s v)
  rw [e]
  refine Finset.aestronglyMeasurable_fun_sum _ fun k _ => ?_
  refine AEStronglyMeasurable.smul (f := fun s => (M s v) k) ?_ (hAm _)
  have : ContinuousOn (fun s => (M s v) k) (Icc (0:ℝ) T) :=
    ((EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).continuous.comp_continuousOn (hMc v))
  exact this.aestronglyMeasurable measurableSet_Icc

theorem e1_M_bound (hMc : ∀ v : Euc d, ContinuousOn (fun s => M s v) (Icc (0:ℝ) T)) (v : Euc d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc (0:ℝ) T, ‖M s v‖ ≤ K := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (hMc v)
  exact ⟨max K 0, le_max_right _ _, fun s hs => (hK s hs).trans (le_max_left _ _)⟩

theorem e1_F_int (hT : 0 ≤ T) (hA : ∀ s ∈ Icc (0:ℝ) T, ‖A s‖ ≤ L)
    (hAm : ∀ v : Euc d, AEStronglyMeasurable (fun s => A s v) (volume.restrict (Icc (0:ℝ) T)))
    (hMc : ∀ v : Euc d, ContinuousOn (fun s => M s v) (Icc (0:ℝ) T)) (v : Euc d) :
    IntervalIntegrable (fun s => A s (M s v)) volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
  obtain ⟨K, hK0, hK⟩ := e1_M_bound hMc v
  refine Integrable.mono' (g := fun _ => L * K) (integrable_const _) (e1_F_meas hAm hMc v) ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs => ?_)
  exact ((A s).le_opNorm _).trans (mul_le_mul (hA s hs) (hK s hs) (norm_nonneg _)
    ((norm_nonneg _).trans (hA s hs)))

theorem e1_c_int (hT : 0 ≤ T) (hA : ∀ s ∈ Icc (0:ℝ) T, ‖A s‖ ≤ L)
    (hAm : ∀ v : Euc d, AEStronglyMeasurable (fun s => A s v) (volume.restrict (Icc (0:ℝ) T))) :
    IntervalIntegrable (fun s => ∑ i, A s (EuclideanSpace.single i (1:ℝ)) i) volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
  refine Integrable.mono' (g := fun _ => (d:ℝ) * L) (integrable_const _) ?_ ?_
  · refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
    exact (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable
      (hAm (EuclideanSpace.single i (1:ℝ)))
  · refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs => ?_)
    refine (norm_sum_le _ _).trans ?_
    have : ∀ i : Fin d, ‖A s (EuclideanSpace.single i (1:ℝ)) i‖ ≤ L := fun i => by
      refine (PiLp.norm_apply_le _ i).trans ?_
      refine ((A s).le_opNorm _).trans ?_
      simpa using mul_le_mul_of_nonneg_right (hA s hs) (norm_nonneg (EuclideanSpace.single i (1:ℝ)))
    calc ∑ i, ‖A s (EuclideanSpace.single i (1:ℝ)) i‖ ≤ ∑ _i : Fin d, L :=
          Finset.sum_le_sum fun i _ => this i
      _ = d * L := by simp

theorem e1_M_lip (hT : 0 ≤ T) (hA : ∀ s ∈ Icc (0:ℝ) T, ‖A s‖ ≤ L)
    (hAm : ∀ v : Euc d, AEStronglyMeasurable (fun s => A s v) (volume.restrict (Icc (0:ℝ) T)))
    (hMc : ∀ v : Euc d, ContinuousOn (fun s => M s v) (Icc (0:ℝ) T))
    (hM : ∀ τ ∈ Icc (0:ℝ) T, ∀ v : Euc d, M τ v = v - ∫ s in (0:ℝ)..τ, A s (M s v))
    (v : Euc d) :
    ∃ K : ℝ≥0, LipschitzOnWith K (fun s => M s v) (uIcc 0 T) := by
  obtain ⟨K, hK0, hK⟩ := e1_M_bound hMc v
  have hint := e1_F_int hT hA hAm hMc v
  refine ⟨(L * K).toNNReal, LipschitzOnWith.of_dist_le_mul fun σ hσ τ hτ => ?_⟩
  rw [uIcc_of_le hT] at hσ hτ
  have h1 : IntervalIntegrable (fun s => A s (M s v)) volume 0 τ :=
    hint.mono_set (by rw [uIcc_of_le hT]; exact Set.uIcc_subset_Icc (left_mem_Icc.2 hT) hτ)
  have h2 : IntervalIntegrable (fun s => A s (M s v)) volume 0 σ :=
    hint.mono_set (by rw [uIcc_of_le hT]; exact Set.uIcc_subset_Icc (left_mem_Icc.2 hT) hσ)
  have h3 := intervalIntegral.integral_interval_sub_left h1 h2
  have hsub : M σ v - M τ v = ∫ s in σ..τ, A s (M s v) := by
    rw [hM τ hτ, hM σ hσ, ← h3]
    abel
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (mul_nonneg ((norm_nonneg _).trans
    (hA 0 ⟨le_rfl, hT⟩)) hK0), hsub]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := σ) (b := τ) (C := L * K)
    (f := fun s => A s (M s v)) (fun s hs => by
      have hs' : s ∈ Icc (0:ℝ) T := Set.uIcc_subset_Icc hσ hτ (Set.uIoc_subset_uIcc hs)
      exact ((A s).le_opNorm _).trans (mul_le_mul (hA s hs') (hK s hs') (norm_nonneg _)
        ((norm_nonneg _).trans (hA s hs'))))
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact this

end Liou

end HRS.Whole.AppendixA.Phase2SA16Evolution
