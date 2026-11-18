import HRS.MS.GenPathAux53

/-!
# S5.6 packet P7j: the path `t ↦ A(k)(t)` as a continuous linear map `𝒦 → 𝒴`; extension of paths beyond `[0,T]`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole HRS.MP.RdRem

variable {d : ℕ}

/-- `k ↦ (t ↦ A(k)(t))` as a bounded linear map into the path space. -/
def s56EvalPath {m T : ℝ} (hT : 0 ≤ T) : KSpace d m T →L[ℝ] OscPath d m T :=
  LinearMap.mkContinuous
    { toFun := fun k => (⟨fun t : Set.Icc (0 : ℝ) T => k.evalA t,
        continuousOn_iff_continuous_restrict.1 (HRS.MS.U9.u9_continuousOn_evalA hT k)⟩ :
          C(Set.Icc (0 : ℝ) T, OscDual d m))
      map_add' := fun x y => ContinuousMap.ext fun t => s56_evalA_add x y t
      map_smul' := fun c x => ContinuousMap.ext fun t => s56_evalA_smul c x t }
    (1 + Real.sqrt T) (fun x => by
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun t => ?_
      have h1 := HRS.MS.U9.u9_evalA_norm_le hT x t
      have h2 := HRS.MS.U9.u9_norm_A₀_le x
      have h3 := HRS.MS.U9.u9_norm_A'_le x
      have : Real.sqrt T * ‖x.A'‖ ≤ Real.sqrt T * ‖x‖ :=
        mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
      show ‖x.evalA t‖ ≤ _
      nlinarith)

theorem s56EvalPath_apply {m T : ℝ} (hT : 0 ≤ T) (k : KSpace d m T) (t : Set.Icc (0 : ℝ) T) :
    (show C(Set.Icc (0 : ℝ) T, OscDual d m) from s56EvalPath hT k) t = k.evalA t := rfl

/-- Extension of a path to `ℝ` by the endpoint values. -/
def s56Ext {m T : ℝ} (hT : 0 ≤ T) (w : OscPath d m T) (t : ℝ) : OscDual d m :=
  (show C(Set.Icc (0 : ℝ) T, OscDual d m) from w) ⟨mrrClamp T t, mrrClamp_mem hT t⟩

theorem s56Ext_of_mem {m T : ℝ} (hT : 0 ≤ T) (w : OscPath d m T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    s56Ext hT w t = (show C(Set.Icc (0 : ℝ) T, OscDual d m) from w) ⟨t, ht⟩ := by
  unfold s56Ext
  congr 1
  exact Subtype.ext (mrrClamp_of_mem ht)

theorem s56Ext_cont {m T : ℝ} (hT : 0 ≤ T) (w : OscPath d m T) : Continuous (s56Ext hT w) := by
  unfold s56Ext
  exact (show C(Set.Icc (0 : ℝ) T, OscDual d m) from w).continuous.comp
    ((continuous_mrrClamp T).subtype_mk _)

theorem s56Ext_meas {m T : ℝ} (hT : 0 ≤ T) {Ω : Type*} [MeasurableSpace Ω] (c : Ω → OscPath d m T)
    (hc : Measurable c) (t : ℝ) : Measurable fun ζ => s56Ext hT (c ζ) t := by
  unfold s56Ext
  have : Continuous fun w : C(Set.Icc (0 : ℝ) T, OscDual d m) => w ⟨mrrClamp T t, mrrClamp_mem hT t⟩ :=
    continuous_eval_const _
  exact (show Continuous fun w : OscPath d m T =>
      (show C(Set.Icc (0 : ℝ) T, OscDual d m) from w) ⟨mrrClamp T t, mrrClamp_mem hT t⟩ from this).measurable.comp hc

/-- The window of `A(k) - w` is the difference of paths. -/
theorem s56_window_evalA_sub {m T : ℝ} (hT : 0 ≤ T) (k : KSpace d m T) (w : OscPath d m T) :
    windowPathOf m T 0 (fun t => k.evalA t - s56Ext hT w t) = s56EvalPath hT k - w := by
  have hc : ContinuousOn (fun t => k.evalA t - s56Ext hT w t) (Set.Icc 0 T) :=
    (HRS.MS.U9.u9_continuousOn_evalA hT k).sub (s56Ext_cont hT w).continuousOn
  refine ContinuousMap.ext fun t => ?_
  have := s56_wpo_apply (m := m) (T := T) hc t
  show (show C(Set.Icc (0 : ℝ) T, OscDual d m) from windowPathOf m T 0 _) t =
    (show C(Set.Icc (0 : ℝ) T, OscDual d m) from s56EvalPath hT k) t -
      (show C(Set.Icc (0 : ℝ) T, OscDual d m) from w) t
  rw [this, s56EvalPath_apply, s56Ext_of_mem hT w t.2]

end HRS.MS.GenPath
