import HRS.MS.R26T6CI09Finite

/-! S11.1 I09: finite coordinate projections satisfy the sharp L3 square-sum estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole HRS.MS.CovMeas
variable {d : ℕ}

theorem r26t6c_finite_ellVec_L3 {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (m : ℝ) (s : Finset (MultiIndex d))
    (f : MultiIndex d → Omega → ℝ) (b : MultiIndex d → ℝ)
    (hb0 : ∀ i, 0 ≤ b i)
    (hf : ∀ i, MemLp (f i) 3 P)
    (hfb : ∀ i, eLpNorm (f i) 3 P ≤ ENNReal.ofReal (b i)) :
    MemLp (fun w => ellVec (d := d) m (fun i => if i ∈ s then f i w else 0)) 3 P ∧
    eLpNorm (fun w => ellVec (d := d) m (fun i => if i ∈ s then f i w else 0))
      3 P ≤ ENNReal.ofReal (Real.sqrt (∑ i ∈ s, b i ^ 2)) := by
  classical
  let U : Omega → OscDual d m :=
    fun w => ellVec (d := d) m (fun i => if i ∈ s then f i w else 0)
  let F : Omega → ℝ := fun w => Real.sqrt (∑ i ∈ s, |f i w| ^ 2)
  have hUm : AEStronglyMeasurable U P := by
    refine r26t6c_ellVec_aesm P m
      (fun i w => if i ∈ s then f i w else 0) ?_ ?_
    · intro i
      by_cases hi : i ∈ s
      · simpa [hi] using (hf i).aestronglyMeasurable
      · simpa [hi] using (aestronglyMeasurable_const :
          AEStronglyMeasurable (fun _ : Omega => (0 : ℝ)) P)
    · apply ae_of_all
      intro w
      have hsumm : Summable (fun i => (if i ∈ s then f i w else 0) ^ 2) := by
        rw [← memℓp_two_iff]
        have hc : Memℓp (fun i => if i ∈ s then f i w else 0) 2 := by
          rw [memℓp_two_iff]
          exact summable_of_finite_support (by
            have hsup : Function.support
              (fun i => (if i ∈ s then f i w else 0) ^ 2) ⊆
              (s : Set (MultiIndex d)) := by
              intro i hi
              by_cases his : i ∈ s
              · exact his
              · have hz : (if i ∈ s then f i w else 0) ^ 2 = 0 := by simp [his]
                exact False.elim (hi hz)
            exact (Finset.finite_toSet s).subset hsup)
        exact hc
      exact hsumm
  have hn : ∀ w, ‖U w‖ = F w := by
    intro w
    have hs := r26t6c_finite_ellVec_norm_sq m s (fun i => f i w)
    have he := congrArg Real.sqrt hs
    rw [Real.sqrt_sq (norm_nonneg _)] at he
    simpa only [U, F, sq_abs] using he
  have hF := r26t6c_finite_square_L3 P s f b (fun i _ => hb0 i)
    (fun i _ => hf i) (fun i _ => hfb i)
  have hnorm : eLpNorm U 3 P = eLpNorm F 3 P := by
    apply eLpNorm_congr_enorm_ae hUm hF.1.aestronglyMeasurable
    exact ae_of_all _ fun w => by
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, hn]
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  refine ⟨?_, ?_⟩
  · change MemLp U 3 P
    rw [memLp_iff, hnorm]
    exact hF.1
  · change eLpNorm U 3 P ≤ _
    rw [hnorm]
    exact hF.2

end HRS.MS.R26T6C
