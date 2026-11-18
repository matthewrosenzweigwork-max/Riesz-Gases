import HRS.MS.R26T6CI09FiniteSeries

/-! I09: sharp finite-partial-sum L3 control in the oscillator coefficient Hilbert space. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole HRS.MS.CovMeas
variable {d : ℕ}

theorem r26t6c_finite_series_L3
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (m : ℝ) (s : Finset (MultiIndex d))
    (f : MultiIndex d → Omega → ℝ) (b : MultiIndex d → ℝ)
    (hb0 : ∀ i, 0 ≤ b i) (hf : ∀ i, MemLp (f i) 3 P)
    (hfb : ∀ i, eLpNorm (f i) 3 P ≤ ENNReal.ofReal (b i)) :
    MemLp (fun w => ∑ i ∈ s,
      (lp.single 2 i (f i w) : OscDual d m)) 3 P ∧
    eLpNorm (fun w => ∑ i ∈ s,
      (lp.single 2 i (f i w) : OscDual d m)) 3 P ≤
      ENNReal.ofReal (Real.sqrt (∑ i ∈ s, b i ^ 2)) := by
  classical
  let V : Omega → OscDual d m := fun w =>
    ∑ i ∈ s, (lp.single 2 i (f i w) : OscDual d m)
  let F : Omega → ℝ := fun w =>
    Real.sqrt (∑ i ∈ s, |f i w| ^ 2)
  have hVm : AEStronglyMeasurable V P := by
    dsimp [V]
    exact Finset.aestronglyMeasurable_fun_sum s fun i _ =>
      (lp.singleContinuousLinearMap (𝕜 := ℝ)
        (E := fun _ : MultiIndex d => ℝ) 2 i).continuous.comp_aestronglyMeasurable
          (hf i).aestronglyMeasurable
  have hVn : ∀ w, ‖V w‖ = F w := by
    intro w
    have hsq := r26t6c_finite_single_norm_sq m s (fun i => f i w)
    have he := congrArg Real.sqrt hsq
    rw [Real.sqrt_sq (norm_nonneg _)] at he
    calc
      ‖V w‖ = Real.sqrt (∑ i ∈ s, f i w ^ 2) := he
      _ = F w := by
        dsimp [F]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        exact (sq_abs _).symm
  have hF := r26t6c_finite_square_L3 P s f b (fun i _ => hb0 i)
    (fun i _ => hf i) (fun i _ => hfb i)
  have hnorm : eLpNorm V 3 P = eLpNorm F 3 P := by
    apply eLpNorm_congr_enorm_ae hVm hF.1.aestronglyMeasurable
    exact ae_of_all _ fun w => by
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, hVn]
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  refine ⟨?_, ?_⟩
  · change MemLp V 3 P
    rw [memLp_iff, hnorm]
    exact hF.1
  · change eLpNorm V 3 P ≤ _
    rw [hnorm]
    exact hF.2

end HRS.MS.R26T6C
