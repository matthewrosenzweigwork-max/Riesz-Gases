import HRS.MS.S82P2Mom

/-!
# S8.2 local Newton layer, packet T8A.R05 (part a): the product of `withDensityReal` measures on `EucConfig d N`
`r26t8a_r05_pi_wd`: `Measure.pi (fun _ => withDensityReal ρ) = volume.withDensity (X ↦ ∏ ofReal (ρ (X i)))` (Euclidean port of `pi_withDensityReal_eq`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

namespace HRS.MS.R26T8A

variable {d N : ℕ}

theorem r26t8a_r05_sigmaFinite (ρ : Euc d → ℝ) : SigmaFinite (HRS.Whole.withDensityReal ρ) := by
  unfold HRS.Whole.withDensityReal; infer_instance

theorem r26t8a_r05_pi_wd (ρ : Euc d → ℝ) (hρ : HRS.Whole.IsProbDensity ρ) :
    Measure.pi (fun _ : Fin N => HRS.Whole.withDensityReal ρ) =
      (volume : Measure (HRS.Whole.EucConfig d N)).withDensity (fun X => ∏ i, ENNReal.ofReal (ρ (X i))) := by
  have := r26t8a_r05_sigmaFinite ρ
  refine (Measure.pi_eq (μ := fun _ : Fin N => HRS.Whole.withDensityReal ρ) fun s hs => ?_)
  have hms : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hms, ← lintegral_indicator hms]
  have h1 : (Set.univ.pi s).indicator (fun X : HRS.Whole.EucConfig d N => ∏ i, ENNReal.ofReal (ρ (X i))) =
      fun X => ∏ i, (s i).indicator (fun y => ENNReal.ofReal (ρ y)) (X i) := by
    funext X
    by_cases h : ∀ i, X i ∈ s i
    · rw [Set.indicator_of_mem (by simpa using h)]
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (h i) (fun y => ENNReal.ofReal (ρ y))).symm
    · push Not at h
      obtain ⟨i, hi⟩ := h
      rw [Set.indicator_of_notMem (by simpa using ⟨i, hi⟩)]
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [h1]
  have hρi : Integrable ρ := by
    by_contra h
    have := hρ.integral_one
    rw [integral_undef h] at this; norm_num at this
  set g : Fin N → Euc d → ℝ := fun i => (s i).indicator ρ with hg
  have hg0 : ∀ i y, 0 ≤ g i y := fun i y => Set.indicator_nonneg (fun y _ => hρ.nonneg y) y
  have hgi : ∀ i, Integrable (g i) := fun i => hρi.indicator (hs i)
  have h2 : ∀ (i : Fin N) (y : Euc d), (s i).indicator (fun y => ENNReal.ofReal (ρ y)) y = ENNReal.ofReal (g i y) := by
    intro i y
    simp only [hg, Set.indicator]
    split_ifs <;> simp
  simp_rw [h2]
  have hint : Integrable (fun x : HRS.Whole.EucConfig d N => ∏ i, g i (x i)) volume := by
    rw [volume_pi]
    exact Integrable.fintype_prod (fun i => hgi i)
  have e1 : ∀ x : HRS.Whole.EucConfig d N, ∏ i, ENNReal.ofReal (g i (x i)) = ENNReal.ofReal (∏ i, g i (x i)) :=
    fun x => (ENNReal.ofReal_prod_of_nonneg (fun i _ => hg0 i (x i))).symm
  simp_rw [e1]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x =>
    Finset.prod_nonneg fun i _ => hg0 i (x i))]
  rw [volume_pi, integral_fintype_prod_eq_prod (fun i y => g i y)]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hg0 i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ofReal_integral_eq_lintegral_ofReal (hgi i) (Filter.Eventually.of_forall (hg0 i))]
  have : ∫⁻ y, ENNReal.ofReal (g i y) = ∫⁻ y, (s i).indicator (fun y => ENNReal.ofReal (ρ y)) y := by
    refine lintegral_congr fun y => (h2 i y).symm
  rw [this, lintegral_indicator (hs i)]
  unfold HRS.Whole.withDensityReal
  rw [withDensity_apply _ (hs i)]

end HRS.MS.R26T8A
