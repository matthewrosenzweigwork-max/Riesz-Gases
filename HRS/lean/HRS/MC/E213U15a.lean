import HRS.MC.E213U13o
import HRS.MC.E213U11j
import HRS.MC.E213TCons

/-!
# Packet e213u15, file a: generic Gaussian contractions in `bochTensor` form

Generic (Banach space `B`, probability space `Ω`) forms of `gaussian_second_contraction` and
`gaussian_first_contraction`, with the right-hand sides rewritten through `bochTensor3_apply` and
`bochTensor21_apply` (Fubini over `P.prod P`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

namespace HRS.MC.E213U15

open HRS HRS.Contr HRS.MC.E213T

section Generic

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

theorem u15_bounds {Φ : B → ℝ} (hΦ : MemCb 3 Φ) (j : ℕ) (hj : j ≤ 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ j Φ x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hΦ.2 j hj
  refine ⟨max C 0, le_max_right _ _, fun x => (hC ⟨x, rfl⟩).trans (le_max_left _ _)⟩

theorem u15_cont_iter {Φ : B → ℝ} (hΦ : MemCb 3 Φ) (j : ℕ) (hj : j ≤ 3) :
    Continuous (iteratedFDeriv ℝ j Φ) :=
  hΦ.1.continuous_iteratedFDeriv (by exact_mod_cast hj)

theorem u15_cont_fderiv {Φ : B → ℝ} (hΦ : MemCb 3 Φ) : Continuous (fderiv ℝ Φ) :=
  hΦ.1.continuous_fderiv (by norm_num)

theorem u15_vec3_continuous : Continuous fun p : B × B × B => (![p.1, p.2.1, p.2.2] : Fin 3 → B) := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact continuous_fst
  · exact continuous_fst.comp continuous_snd
  · exact continuous_snd.comp continuous_snd

theorem u15_drift_generic (ξ : ℕ → Ω → ℝ) (hξ : IsStdGaussianSeq P ξ) (G D : Ω → B)
    (hG : IsCenteredGaussian (law P G)) (hGc : InFirstChaos P ξ 2 G) (hDc : InSecondChaos P ξ 3 D)
    (Φ : B → ℝ) (hΦ : MemCb 3 Φ)
    (hGa : AEStronglyMeasurable G P) (hDa : AEStronglyMeasurable D P)
    (hD1 : Integrable (fun ω => ‖D ω‖) P)
    (hDGG : Integrable (fun ω => ‖D ω‖ * ‖G ω‖ * ‖G ω‖) P) :
    ∫ ω, fderiv ℝ Φ (G ω) (D ω) ∂P =
      (1 / 2) * ∫ ω, (bochTensor3 P D G G) (iteratedFDeriv ℝ 3 Φ (G ω)) ∂P := by
  obtain ⟨C1, hC1, hb1⟩ := u15_bounds hΦ 1 (by norm_num)
  obtain ⟨C3, hC3, hb3⟩ := u15_bounds hΦ 3 le_rfl
  have hc1 := u15_cont_fderiv hΦ
  have hc3 := u15_cont_iter hΦ 3 le_rfl
  have hint1 : Integrable (fun ω => fderiv ℝ Φ (G ω) (D ω)) P := by
    refine (hD1.const_mul C1).mono' ?_ (Eventually.of_forall fun ω => ?_)
    · exact (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := B) (F := ℝ)).continuous.comp_aestronglyMeasurable
        ((hc1.comp_aestronglyMeasurable hGa).prodMk hDa)
    · calc ‖fderiv ℝ Φ (G ω) (D ω)‖ ≤ ‖fderiv ℝ Φ (G ω)‖ * ‖D ω‖ := (fderiv ℝ Φ (G ω)).le_opNorm _
        _ ≤ C1 * ‖D ω‖ := by
          gcongr
          rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]
          exact hb1 _
  have hevalm : ∀ (M : B [×3]→L[ℝ] ℝ) (x y z : B), ‖M ![x, y, z]‖ ≤ ‖M‖ * (‖x‖ * ‖y‖ * ‖z‖) := by
    intro M x y z
    have := M.le_opNorm ![x, y, z]
    simpa [Fin.prod_univ_three] using this
  have hint3 : Integrable (fun p : Ω × Ω => iteratedFDeriv ℝ 3 Φ (G p.1) ![D p.2, G p.2, G p.2])
      (P.prod P) := by
    refine ((hDGG.comp_snd P).const_mul C3).mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hm1 : AEStronglyMeasurable (fun p : Ω × Ω => iteratedFDeriv ℝ 3 Φ (G p.1)) (P.prod P) :=
        (hc3.comp_aestronglyMeasurable hGa).comp_fst
      have hm2 : AEStronglyMeasurable (fun p : Ω × Ω => (![D p.2, G p.2, G p.2] : Fin 3 → B)) (P.prod P) :=
        (u15_vec3_continuous (B := B)).comp_aestronglyMeasurable
          (hDa.comp_snd.prodMk (hGa.comp_snd.prodMk hGa.comp_snd))
      exact (continuous_eval : Continuous fun q : (B [×3]→L[ℝ] ℝ) × (Fin 3 → B) => q.1 q.2).comp_aestronglyMeasurable
        (hm1.prodMk hm2)
    · calc ‖iteratedFDeriv ℝ 3 Φ (G p.1) ![D p.2, G p.2, G p.2]‖
          ≤ ‖iteratedFDeriv ℝ 3 Φ (G p.1)‖ * (‖D p.2‖ * ‖G p.2‖ * ‖G p.2‖) := hevalm _ _ _ _
        _ ≤ C3 * (‖D p.2‖ * ‖G p.2‖ * ‖G p.2‖) := by gcongr; exact hb3 _
  rw [gaussian_second_contraction P ξ hξ G hG hGc D 3 le_rfl hDc Φ hΦ hint1 hint3]
  congr 1
  rw [integral_prod _ hint3]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  exact (bochTensor3_apply hDa hGa hGa hDGG (iteratedFDeriv ℝ 3 Φ (G x))).symm

theorem u15_J_generic (ξ : ℕ → Ω → ℝ) (hξ : IsStdGaussianSeq P ξ) (G : Ω → B)
    (hG : IsCenteredGaussian (law P G)) (hGc : InFirstChaos P ξ 2 G)
    (J : Ω → projTensor B 2) (q : ℝ) (hq : 2 ≤ q) (hJ : InFirstChaos P ξ q J)
    (Φ : B → ℝ) (hΦ : MemCb 3 Φ)
    (hGa : AEStronglyMeasurable G P) (hJa : AEStronglyMeasurable (fun ω => (J ω : TensorDual B 2)) P)
    (hJ1 : Integrable (fun ω => ‖(J ω : TensorDual B 2)‖) P)
    (hJG : Integrable (fun ω => ‖(J ω : TensorDual B 2)‖ * ‖G ω‖) P) :
    ∫ ω, (J ω : TensorDual B 2) (iteratedFDeriv ℝ 2 Φ (G ω)) ∂P =
      ∫ ω, (bochTensor21 P (fun ω => (J ω : TensorDual B 2)) G) (iteratedFDeriv ℝ 3 Φ (G ω)) ∂P := by
  obtain ⟨C2, hC2, hb2⟩ := u15_bounds hΦ 2 (by norm_num)
  obtain ⟨C3, hC3, hb3⟩ := u15_bounds hΦ 3 le_rfl
  have hc2 := u15_cont_iter hΦ 2 (by norm_num)
  have hc3 := u15_cont_iter hΦ 3 le_rfl
  have hint2 : Integrable (fun ω => (J ω : TensorDual B 2) (iteratedFDeriv ℝ 2 Φ (G ω))) P := by
    refine (hJ1.mul_const C2).mono' ?_ (Eventually.of_forall fun ω => ?_)
    · exact (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := B [×2]→L[ℝ] ℝ) (F := ℝ)).continuous.comp_aestronglyMeasurable
        (hJa.prodMk (hc2.comp_aestronglyMeasurable hGa))
    · calc ‖(J ω : TensorDual B 2) (iteratedFDeriv ℝ 2 Φ (G ω))‖
          ≤ ‖(J ω : TensorDual B 2)‖ * ‖iteratedFDeriv ℝ 2 Φ (G ω)‖ := (J ω : TensorDual B 2).le_opNorm _
        _ ≤ ‖(J ω : TensorDual B 2)‖ * C2 := by gcongr; exact hb2 _
  have hint3 : Integrable (fun p : Ω × Ω =>
      (J p.2 : TensorDual B 2) (lastSlot (iteratedFDeriv ℝ 3 Φ (G p.1)) (G p.2))) (P.prod P) := by
    refine ((hJG.comp_snd P).const_mul C3).mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hm1 : AEStronglyMeasurable (fun p : Ω × Ω => iteratedFDeriv ℝ 3 Φ (G p.1)) (P.prod P) :=
        (hc3.comp_aestronglyMeasurable hGa).comp_fst
      have hcont : Continuous fun q : TensorDual B 2 × (B [×3]→L[ℝ] ℝ) × B =>
          q.1 (lastSlot q.2.1 q.2.2) :=
        (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := B [×2]→L[ℝ] ℝ) (F := ℝ)).continuous.comp
          (continuous_fst.prodMk (continuous_lastSlot2 (continuous_fst.comp continuous_snd)
            (continuous_snd.comp continuous_snd)))
      exact hcont.comp_aestronglyMeasurable (hJa.comp_snd.prodMk (hm1.prodMk hGa.comp_snd))
    · calc ‖(J p.2 : TensorDual B 2) (lastSlot (iteratedFDeriv ℝ 3 Φ (G p.1)) (G p.2))‖
          ≤ ‖(J p.2 : TensorDual B 2)‖ * ‖lastSlot (iteratedFDeriv ℝ 3 Φ (G p.1)) (G p.2)‖ :=
            (J p.2 : TensorDual B 2).le_opNorm _
        _ ≤ ‖(J p.2 : TensorDual B 2)‖ * (‖iteratedFDeriv ℝ 3 Φ (G p.1)‖ * ‖G p.2‖) := by
            gcongr; exact norm_lastSlot_le _ _
        _ ≤ ‖(J p.2 : TensorDual B 2)‖ * (C3 * ‖G p.2‖) := by gcongr; exact hb3 _
        _ = C3 * (‖(J p.2 : TensorDual B 2)‖ * ‖G p.2‖) := by ring
  rw [gaussian_first_contraction P ξ hξ G hG hGc J q hq hJ Φ hΦ hint2 hint3]
  rw [integral_prod _ hint3]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  exact (bochTensor21_apply hJa hGa hJG (iteratedFDeriv ℝ 3 Φ (G x))).symm

end Generic

end HRS.MC.E213U15

end
