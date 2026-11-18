import HRS.MC.E213U15a
import HRS.MS.S21F_S26a

/-!
# S21F, packet R26-T3.S26b: derivative-only Gaussian contractions for the actual static Stein class

For `f ∈ SteinCl` apply the generic contractions (`u15_drift_generic`, `u15_J_generic`, hypotheses `MemCb 3`) to the cutoffs `f_n` of S26a
and pass to the limit by dominated convergence: the derivatives of order `1..3` of `f_n` converge pointwise to those of `f` and are bounded by a common
constant, the random factors `D`, `A` are integrable and the Bochner tensors are bounded functionals.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole

namespace HRS.MS.R26T3

theorem r26t3_stein_gaussian_contract {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ξ : ℕ → Ω → ℝ)
    (hξ : HRS.IsStdGaussianSeq P ξ) (G D : Ω → SeqL2) (A : Ω → projTensor SeqL2 2)
    (hG : IsCenteredGaussian (law P G)) (hGc : HRS.InFirstChaos P ξ 2 G)
    (hDc : HRS.InSecondChaos P ξ 3 D) (hAc : HRS.InFirstChaos P ξ 2 A)
    (hD1 : Integrable (fun ω => ‖D ω‖) P)
    (hDGG : Integrable (fun ω => ‖D ω‖ * ‖G ω‖ * ‖G ω‖) P)
    (hA1 : Integrable (fun ω => ‖A ω‖) P)
    (hAG : Integrable (fun ω => ‖A ω‖ * ‖G ω‖) P)
    (f : SeqL2 → ℝ) (hf : S99.SteinCl f) :
    (∫ ω, fderiv ℝ f (G ω) (D ω) ∂P) =
      (1 / 2) * ∫ ω, (HRS.MC.E213T.bochTensor3 P D G G)
        (iteratedFDeriv ℝ 3 f (G ω)) ∂P ∧
    (∫ ω, (A ω : TensorDual SeqL2 2) (iteratedFDeriv ℝ 2 f (G ω)) ∂P) =
      ∫ ω, (HRS.MC.E213T.bochTensor21 P (fun ω => (A ω : TensorDual SeqL2 2)) G)
        (iteratedFDeriv ℝ 3 f (G ω)) ∂P := by
  obtain ⟨fn, hmem, ⟨C, hC⟩, hlim⟩ := r26t3_stein_cutoff f hf
  have hGa : AEStronglyMeasurable G P := hGc.1
  have hDa : AEStronglyMeasurable D P := hDc.1
  have hAa : AEStronglyMeasurable (fun ω => (A ω : TensorDual SeqL2 2)) P :=
    continuous_subtype_val.comp_aestronglyMeasurable hAc.1
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 1 le_rfl (by norm_num) 0)
  have hcont : ∀ n j, j ≤ 3 → Continuous (iteratedFDeriv ℝ j (fn n)) := fun n j hj =>
    HRS.MC.E213U15.u15_cont_iter (hmem n) j hj
  have hc1 : ∀ n, Continuous (fderiv ℝ (fn n)) := fun n => HRS.MC.E213U15.u15_cont_fderiv (hmem n)
  have hfd : ∀ (g : SeqL2 → ℝ) (x v : SeqL2), iteratedFDeriv ℝ 1 g x (fun _ => v) = fderiv ℝ g x v :=
    fun g x v => iteratedFDeriv_one_apply (fun _ => v)
  -- the two identities for the cutoffs
  have h1 : ∀ n, ∫ ω, fderiv ℝ (fn n) (G ω) (D ω) ∂P =
      (1 / 2) * ∫ ω, (HRS.MC.E213T.bochTensor3 P D G G) (iteratedFDeriv ℝ 3 (fn n) (G ω)) ∂P := fun n =>
    HRS.MC.E213U15.u15_drift_generic P ξ hξ G D hG hGc hDc (fn n) (hmem n) hGa hDa hD1 hDGG
  have h2 : ∀ n, ∫ ω, (A ω : TensorDual SeqL2 2) (iteratedFDeriv ℝ 2 (fn n) (G ω)) ∂P =
      ∫ ω, (HRS.MC.E213T.bochTensor21 P (fun ω => (A ω : TensorDual SeqL2 2)) G)
        (iteratedFDeriv ℝ 3 (fn n) (G ω)) ∂P := fun n =>
    HRS.MC.E213U15.u15_J_generic P ξ hξ G hG hGc A 2 le_rfl hAc (fn n) (hmem n) hGa hAa hA1 hAG
  have hbd1 : ∀ n x v, ‖fderiv ℝ (fn n) x v‖ ≤ C * ‖v‖ := fun n x v => by
    calc ‖fderiv ℝ (fn n) x v‖ ≤ ‖fderiv ℝ (fn n) x‖ * ‖v‖ := (fderiv ℝ (fn n) x).le_opNorm v
      _ ≤ C * ‖v‖ := by
        gcongr
        rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]
        exact hC n 1 le_rfl (by norm_num) x
  have hevl : ∀ (j : ℕ) (hj1 : 1 ≤ j) (hj3 : j ≤ 3) (x : SeqL2) (T : TensorDual SeqL2 j),
      Tendsto (fun n => T (iteratedFDeriv ℝ j (fn n) x)) atTop (𝓝 (T (iteratedFDeriv ℝ j f x))) :=
    fun j hj1 hj3 x T => (T.continuous.tendsto _).comp (hlim x j hj1 hj3)
  constructor
  · -- first identity
    have hL : Tendsto (fun n => ∫ ω, fderiv ℝ (fn n) (G ω) (D ω) ∂P) atTop
        (𝓝 (∫ ω, fderiv ℝ f (G ω) (D ω) ∂P)) := by
      refine tendsto_integral_of_dominated_convergence (fun ω => C * ‖D ω‖) (fun n => ?_)
        (hD1.const_mul C) (fun n => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => ?_)
      · exact (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := SeqL2) (F := ℝ)).continuous.comp_aestronglyMeasurable
          (((hc1 n).comp_aestronglyMeasurable hGa).prodMk hDa)
      · exact hbd1 n (G ω) (D ω)
      · have h := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => SeqL2) ℝ
          (fun _ => D ω)).continuous.tendsto _ |>.comp (hlim (G ω) 1 le_rfl (by norm_num))
        simpa [Function.comp_def, hfd] using h
    set T := HRS.MC.E213T.bochTensor3 P D G G with hT
    have hR : Tendsto (fun n => ∫ ω, T (iteratedFDeriv ℝ 3 (fn n) (G ω)) ∂P) atTop
        (𝓝 (∫ ω, T (iteratedFDeriv ℝ 3 f (G ω)) ∂P)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => ‖T‖ * C) (fun n => ?_)
        (integrable_const _) (fun n => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => ?_)
      · exact T.continuous.comp_aestronglyMeasurable ((hcont n 3 le_rfl).comp_aestronglyMeasurable hGa)
      · calc ‖T (iteratedFDeriv ℝ 3 (fn n) (G ω))‖ ≤ ‖T‖ * ‖iteratedFDeriv ℝ 3 (fn n) (G ω)‖ := T.le_opNorm _
          _ ≤ ‖T‖ * C := by gcongr; exact hC n 3 (by norm_num) le_rfl _
      · exact hevl 3 (by norm_num) le_rfl (G ω) T
    exact tendsto_nhds_unique hL (by simpa [h1] using hR.const_mul (1 / 2 : ℝ))
  · -- second identity
    have hL : Tendsto (fun n => ∫ ω, (A ω : TensorDual SeqL2 2) (iteratedFDeriv ℝ 2 (fn n) (G ω)) ∂P) atTop
        (𝓝 (∫ ω, (A ω : TensorDual SeqL2 2) (iteratedFDeriv ℝ 2 f (G ω)) ∂P)) := by
      refine tendsto_integral_of_dominated_convergence (fun ω => ‖A ω‖ * C) (fun n => ?_)
        (hA1.mul_const C) (fun n => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => ?_)
      · exact (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := SeqL2 [×2]→L[ℝ] ℝ) (F := ℝ)).continuous.comp_aestronglyMeasurable
          (hAa.prodMk ((hcont n 2 (by norm_num)).comp_aestronglyMeasurable hGa))
      · calc ‖(A ω : TensorDual SeqL2 2) (iteratedFDeriv ℝ 2 (fn n) (G ω))‖
            ≤ ‖(A ω : TensorDual SeqL2 2)‖ * ‖iteratedFDeriv ℝ 2 (fn n) (G ω)‖ := (A ω : TensorDual SeqL2 2).le_opNorm _
          _ ≤ ‖A ω‖ * C := mul_le_mul (le_of_eq rfl) (hC n 2 (by norm_num) (by norm_num) _) (norm_nonneg _) (norm_nonneg _)
      · exact hevl 2 (by norm_num) (by norm_num) (G ω) (A ω : TensorDual SeqL2 2)
    set T := HRS.MC.E213T.bochTensor21 P (fun ω => (A ω : TensorDual SeqL2 2)) G with hT
    have hR : Tendsto (fun n => ∫ ω, T (iteratedFDeriv ℝ 3 (fn n) (G ω)) ∂P) atTop
        (𝓝 (∫ ω, T (iteratedFDeriv ℝ 3 f (G ω)) ∂P)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => ‖T‖ * C) (fun n => ?_)
        (integrable_const _) (fun n => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => ?_)
      · exact T.continuous.comp_aestronglyMeasurable ((hcont n 3 le_rfl).comp_aestronglyMeasurable hGa)
      · calc ‖T (iteratedFDeriv ℝ 3 (fn n) (G ω))‖ ≤ ‖T‖ * ‖iteratedFDeriv ℝ 3 (fn n) (G ω)‖ := T.le_opNorm _
          _ ≤ ‖T‖ * C := by gcongr; exact hC n 3 (by norm_num) le_rfl _
      · exact hevl 3 (by norm_num) le_rfl (G ω) T
    exact tendsto_nhds_unique hL (by simpa [h2] using hR)

end HRS.MS.R26T3
