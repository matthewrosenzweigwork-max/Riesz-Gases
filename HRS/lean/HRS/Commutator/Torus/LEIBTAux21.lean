import HRS.Commutator.Torus.LEIBTAux20

/-!
# LEIB-T helpers, part 21: `L^p` bounds for the cut-off functions and their Bessel derivatives
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma leibt_cut_cont {η : ℝ} (hd : 1 ≤ d) {e : ℕ} (he : 1 ≤ e) {G₀ : Torus d → ℝ} (hG₀ : Continuous G₀)
    (N : ℝ) : Continuous fun y : 𝔼 => ((G₀ (Torus.mk (η • y)) : ℝ) : ℂ) * leibt_chi hd he (N⁻¹ • y) :=
  (Complex.continuous_ofReal.comp (hG₀.comp (HRS.Torus.continuous_mk.comp (continuous_const_smul η)))).mul
    ((leibt_chi hd he).continuous.comp (continuous_const_smul N⁻¹))

lemma leibt_cut_le (hd : 1 ≤ d) {η : ℝ} (hη : 0 < η) (M : ℕ) {N N' : ℝ} (hN : N = ((M : ℝ) + 1 / 2) / η)
    (hN' : N' = ((((2 * d * M + d : ℕ)) : ℝ) + 1 / 2) / η) {e : ℕ} (he : 1 ≤ e) {G₀ : Torus d → ℝ}
    (hG₀ : Continuous G₀) {p : ℝ≥0∞} (hp : p ≠ 0) :
    eLpNorm (fun y : 𝔼 => ((G₀ (Torus.mk (η • y)) : ℝ) : ℂ) * leibt_chi hd he (N⁻¹ • y)) p volume ≤
      leibt_Lam d N' p * eLpNorm G₀ p volume := by
  refine le_trans ?_ (leibt_eLpNorm_box_Lam_le hη (2 * d * M + d) hN' hG₀ hp)
  have hN0 : 0 < N := by
    rw [hN]; positivity
  have hNN : 2 * d * N ≤ N' := by
    rw [hN, hN']
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hη.le
    push_cast
    nlinarith
  refine eLpNorm_mono (leibt_cut_cont hd he hG₀ N).aestronglyMeasurable fun y => ?_
  by_cases hy : y ∈ leibt_boxN d N'
  · rw [Set.indicator_of_mem hy, norm_mul]
    calc ‖((G₀ (Torus.mk (η • y)) : ℝ) : ℂ)‖ * ‖leibt_chi hd he (N⁻¹ • y)‖
        ≤ ‖((G₀ (Torus.mk (η • y)) : ℝ) : ℂ)‖ * 1 := by
          gcongr; exact leibt_chi_norm_le_one hd he _
      _ = _ := mul_one _
  · rw [Set.indicator_of_notMem hy, leibt_chi_zero_off_box hd he hN0 hNN hy]
    simp

lemma leibt_cut_ge (hd : 1 ≤ d) {η : ℝ} (hη : 0 < η) (M : ℕ) {N : ℝ} (hN : N = ((M : ℝ) + 1 / 2) / η)
    {e : ℕ} (he : 1 ≤ e) {G₀ : Torus d → ℝ} (hG₀ : Continuous G₀) {p : ℝ≥0∞} (hp : p ≠ 0) (hpt : p ≠ ⊤) :
    leibt_Lam d N p * eLpNorm G₀ p volume ≤
      eLpNorm (fun y : 𝔼 => ((G₀ (Torus.mk (η • y)) : ℝ) : ℂ) * leibt_chi hd he (N⁻¹ • y)) p volume := by
  rw [← leibt_eLpNorm_box_Lam_eq hη M hN hG₀ hp hpt]
  have hN0 : 0 < N := by
    rw [hN]; positivity
  have hmeas : AEStronglyMeasurable ((leibt_boxN d N).indicator
      (fun y : 𝔼 => ((G₀ (Torus.mk (η • y)) : ℝ) : ℂ))) volume :=
    ((Complex.continuous_ofReal.comp (hG₀.comp (HRS.Torus.continuous_mk.comp
      (continuous_const_smul η)))).aestronglyMeasurable).indicator (leibt_measurableSet_boxN _)
  refine eLpNorm_mono hmeas fun y => ?_
  by_cases hy : y ∈ leibt_boxN d N
  · rw [Set.indicator_of_mem hy, norm_mul, leibt_chi_one_on_box hd he hN0 hy]
    simp
  · rw [Set.indicator_of_notMem hy]
    simp only [norm_zero]
    positivity

end HRS.Commutator.TorusNote
