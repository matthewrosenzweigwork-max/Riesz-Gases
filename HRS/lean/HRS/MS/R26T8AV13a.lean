import HRS.MS.R26T8AV12

/-!
# S8.2 observed-time layer, packet T8A.V13a: generic helpers for the closure step of V13

* the supremum of `‖f‖ₑ` over `[0,T]` equals the supremum over a dense subset when `f` is continuous on `[0,T]`;
* `L²`-convergence of squared norms gives convergence of `eLpNorm`;
* `‖∫ f‖ₑ ≤ ‖f‖₂` on a probability space and the resulting bound for centered differences.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A

theorem r26t8a_v13a_sup_dense {f : ℝ → ℝ} {T : ℝ} (hf : ContinuousOn f (Set.Icc 0 T)) {D : Set ℝ}
    (hDs : D ⊆ Set.Icc 0 T) (hDc : Set.Icc 0 T ⊆ closure D) :
    (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖f t‖ₑ) = ⨆ d ∈ D, ‖f d‖ₑ := by
  refine le_antisymm (iSup₂_le fun t ht => ?_)
    (iSup₂_le fun d hd => le_iSup₂ (f := fun t _ => ‖f t‖ₑ) d (hDs hd))
  obtain ⟨u, hu, hut⟩ := mem_closure_iff_seq_limit.1 (hDc ht)
  have hcw : ContinuousWithinAt f (Set.Icc 0 T) t := hf t ht
  have hut' : Tendsto u atTop (𝓝[Set.Icc 0 T] t) :=
    tendsto_nhdsWithin_iff.2 ⟨hut, Eventually.of_forall fun n => hDs (hu n)⟩
  have h1 : Tendsto (fun n => ‖f (u n)‖ₑ) atTop (𝓝 ‖f t‖ₑ) :=
    (continuous_enorm.tendsto _).comp (hcw.tendsto.comp hut')
  exact le_of_tendsto' h1 fun n => le_iSup₂ (f := fun d _ => ‖f d‖ₑ) (u n) (hu n)

theorem r26t8a_v13a_L2_tendsto {α : Type*} [MeasurableSpace α] {P : Measure α} {f : ℕ → α → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) P)
    (h : Tendsto (fun n => ∫⁻ x, ‖f n x‖ₑ ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) 2 P) atTop (𝓝 0) := by
  have h2 : Tendsto (fun n => eLpNorm (f n) 2 P ^ 2) atTop (𝓝 0) :=
    h.congr fun n => lintegral_enorm_sq_eq_eLpNorm_sq (hf n)
  have h3 := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp h2
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
  refine h3.congr fun n => ?_
  show (eLpNorm (f n) 2 P ^ 2) ^ (1 / 2 : ℝ) = _
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem r26t8a_v13a_enorm_integral_le {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsProbabilityMeasure P] {f : α → ℝ} (hf : AEStronglyMeasurable f P) :
    ‖∫ x, f x ∂P‖ₑ ≤ eLpNorm f 2 P := by
  calc ‖∫ x, f x ∂P‖ₑ ≤ ∫⁻ x, ‖f x‖ₑ ∂P := enorm_integral_le_lintegral_enorm f
    _ = eLpNorm f 1 P := (eLpNorm_one_eq_lintegral_enorm hf).symm
    _ ≤ eLpNorm f 2 P := eLpNorm_le_eLpNorm_of_exponent_le one_le_two

theorem r26t8a_v13a_center_bound {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsProbabilityMeasure P] {g F : α → ℝ} (hg : Integrable g P) (hF : Integrable F P) :
    eLpNorm (fun x => (g x - ∫ y, g y ∂P) - (F x - ∫ y, F y ∂P)) 2 P ≤
      2 * eLpNorm (fun x => g x - F x) 2 P := by
  have hd : AEStronglyMeasurable (fun x => g x - F x) P := (hg.sub hF).aestronglyMeasurable
  have e : (fun x => (g x - ∫ y, g y ∂P) - (F x - ∫ y, F y ∂P)) =
      fun x => (g x - F x) - (∫ y, g y ∂P - ∫ y, F y ∂P) := by
    funext x; ring
  rw [e]
  have hc : eLpNorm (fun _ : α => (∫ y, g y ∂P - ∫ y, F y ∂P)) 2 P ≤
      eLpNorm (fun x => g x - F x) 2 P := by
    have h0 := r26t8a_v13a_enorm_integral_le P hd
    rw [integral_sub hg hF] at h0
    rw [eLpNorm_const _ (by norm_num) (NeZero.ne P)]
    simpa using h0
  calc _ ≤ eLpNorm (fun x => g x - F x) 2 P +
        eLpNorm (fun _ : α => (∫ y, g y ∂P - ∫ y, F y ∂P)) 2 P :=
        eLpNorm_sub_le one_le_two
    _ ≤ _ := by rw [two_mul]; gcongr

end HRS.MS.R26T8A
