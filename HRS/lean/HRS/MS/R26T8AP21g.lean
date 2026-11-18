import HRS.MS.R26T8AP21f
import HRS.MS.R26T8AP03c

/-!
# S8.2 local Newton layer, packet T8A.P21 (part g): differentiation under a `t`-integral on `[0,1]`
`r26t8a_stageT` (compactly supported in `x`, uniformly in `t`) and `r26t8a_nest_integral`:
`nest p q (Y,w |-> int_0^1 Theta t (Y,w) dt) = int_0^1 nest p q (Theta t) dt`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_slice_jet_inr' {E1 E2 V : Type} [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2]
    [NormedSpace ℝ E2] [NormedAddCommGroup V] [NormedSpace ℝ V] {Θ : E1 × E2 → V} {i : ℕ}
    (hΘ : ContDiff ℝ (i : WithTop ℕ∞) Θ) (a : E1) (w : E2) :
    iteratedFDeriv ℝ i (fun w' => Θ (a, w')) w =
      (iteratedFDeriv ℝ i Θ (a, w)).compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ E1 E2) := by
  have h1 : (fun w' : E2 => Θ (a, w')) = (fun v : E1 × E2 => Θ (v + (a, 0))) ∘
      (ContinuousLinearMap.inr ℝ E1 E2) := by
    funext w'; simp [Prod.mk_add_mk]
  have hf' : ContDiff ℝ (i : WithTop ℕ∞) (fun v : E1 × E2 => Θ (v + (a, 0))) :=
    hΘ.comp (contDiff_id.add contDiff_const)
  rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_right (ContinuousLinearMap.inr ℝ E1 E2) hf' w le_rfl]
  rw [iteratedFDeriv_comp_add_right]
  simp

section T

variable {d : ℕ}

theorem r26t8a_stageT {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] {n : ℕ}
    (Θ : ℝ → Euc d → V) (hΘ : ContDiff ℝ (n : WithTop ℕ∞) (fun tx : ℝ × Euc d => Θ tx.1 tx.2))
    {K : Set (Euc d)} (hK : IsCompact K) (hsupp : ∀ t x, x ∉ K → Θ t x = 0) (x0 : Euc d) :
    iteratedFDeriv ℝ n (fun x => ∫ t in (0 : ℝ)..1, Θ t x) x0 = ∫ t in (0 : ℝ)..1, iteratedFDeriv ℝ n (Θ t) x0 := by
  set G : ℝ → Euc d → V := fun t x => (Set.Ioc (0 : ℝ) 1).indicator (fun t => Θ t x) t with hG
  have hslice : ∀ t, ContDiff ℝ (n : WithTop ℕ∞) (Θ t) := fun t =>
    hΘ.comp (contDiff_const.prodMk contDiff_id)
  have hGd : ∀ t, ContDiff ℝ (n : WithTop ℕ∞) (G t) := fun t => by
    by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
    · have : G t = Θ t := by funext x; simp [hG, ht]
      rw [this]; exact hslice t
    · have : G t = fun _ => 0 := by funext x; simp [hG, ht]
      rw [this]; exact contDiff_const
  have hGjet : ∀ i t x, iteratedFDeriv ℝ i (G t) x = (Set.Ioc (0 : ℝ) 1).indicator
      (fun t => iteratedFDeriv ℝ i (Θ t) x) t := fun i t x => by
    by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
    · have : G t = Θ t := by funext x; simp [hG, ht]
      rw [this]; simp [ht]
    · have : G t = fun _ => 0 := by funext x; simp [hG, ht]
      rw [this]; simp [ht]
  -- jet continuity and bounds
  have hcont : ∀ i ≤ n, Continuous (fun tx : ℝ × Euc d => iteratedFDeriv ℝ i (Θ tx.1) tx.2) := fun i hi => by
    have hΘ' : ContDiff ℝ (i : WithTop ℕ∞) (fun tx : ℝ × Euc d => Θ tx.1 tx.2) := hΘ.of_le (by exact_mod_cast hi)
    have e : (fun tx : ℝ × Euc d => iteratedFDeriv ℝ i (Θ tx.1) tx.2) = fun tx =>
        (iteratedFDeriv ℝ i (fun tx : ℝ × Euc d => Θ tx.1 tx.2) tx).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inr ℝ ℝ (Euc d)) := by
      funext tx
      have := r26t8a_slice_jet_inr' hΘ' tx.1 tx.2
      simpa using this
    rw [e]
    exact (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin i => ContinuousLinearMap.inr ℝ ℝ (Euc d))).continuous.comp
      (hΘ'.continuous_iteratedFDeriv le_rfl)
  have hzero : ∀ i t x, x ∉ K → iteratedFDeriv ℝ i (Θ t) x = 0 := fun i t x hx => by
    have : Θ t =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy using hsupp t y hy
    rw [(this.iteratedFDeriv ℝ i).eq_of_nhds]; simp
  have hB : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, i ≤ n → ‖iteratedFDeriv ℝ i (Θ t) x‖ ≤ C := by
    intro i
    by_cases hi : i ≤ n
    · obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn (hcont i hi).continuousOn
      refine ⟨max C 0, le_max_right _ _, fun t ht x _ => ?_⟩
      by_cases hx : x ∈ K
      · exact (hC (t, x) ⟨ht, hx⟩).trans (le_max_left _ _)
      · rw [hzero i t x hx, norm_zero]; exact le_max_right _ _
    · exact ⟨0, le_rfl, fun t _ x h => absurd h hi⟩
  choose C hC0 hC using hB
  set B : ℝ := ∑ i ∈ Finset.range (n + 1), C i with hBdef
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => hC0 i
  have hBb : ∀ i ≤ n, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖iteratedFDeriv ℝ i (Θ t) x‖ ≤ B := fun i hi t ht x =>
    (hC i t ht x hi).trans (Finset.single_le_sum (f := C) (fun j _ => hC0 j) (Finset.mem_range.2 (by omega)))
  have hint : Integrable ((Set.Ioc (0 : ℝ) 1).indicator fun _ => B) :=
    (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const (by simp))
  have key := HRS.MS.Lc.lc4_iteratedFDeriv_integral (μ := (volume : Measure ℝ)) G n hGd
    (Φ := (Set.Ioc (0 : ℝ) 1).indicator fun _ => B) hint
    (fun i hi t x => by
      rw [hGjet]
      by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
        exact hBb i hi t ⟨ht.1.le, ht.2⟩ x
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, norm_zero])
    (fun i hi x => by
      have e : (fun t => iteratedFDeriv ℝ i (G t) x) = (Set.Ioc (0 : ℝ) 1).indicator
          (fun t => iteratedFDeriv ℝ i (Θ t) x) := funext fun t => hGjet i t x
      rw [e]
      exact ((hcont i hi).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable.indicator
        measurableSet_Ioc)
  have hL : (fun x => ∫ t, G t x) = fun x => ∫ t in (0 : ℝ)..1, Θ t x := by
    funext x
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_indicator measurableSet_Ioc]
  have hR : ∫ t, iteratedFDeriv ℝ n (G t) x0 = ∫ t in (0 : ℝ)..1, iteratedFDeriv ℝ n (Θ t) x0 := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_indicator measurableSet_Ioc]
    exact integral_congr_ae (Eventually.of_forall fun t => hGjet n t x0)
  have := key.2 n le_rfl x0
  rw [hL] at this
  rw [this, hR]

end T

end HRS.MS.R26T8A
