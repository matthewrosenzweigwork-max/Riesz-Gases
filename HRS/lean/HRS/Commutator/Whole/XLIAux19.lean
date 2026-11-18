import HRS.Commutator.Whole.XLIAux18

/-!
# X-LI part 19: evenness of the symmetric dyadic kernels and the adjoint identity for convolutions
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma cut_neg (η : 𝔼) : cut (-η) = cut η := by
  unfold cut
  exact (cutB d).neg η

lemma rhoT_neg (η : 𝔼) : rhoT (-η) = rhoT η := by
  unfold rhoT
  rw [smul_neg, smul_neg, cut_neg, cut_neg]

lemma rho_neg (η : 𝔼) : rho (-η) = rho η := by
  unfold rho
  rw [smul_neg, cut_neg, cut_neg]

/-- the dyadic kernel of an even symbol is even -/
lemma symK_even {θ : 𝔼 → ℂ} (he : ∀ η, θ (-η) = θ η) (j : ℤ) (z : 𝔼) :
    symK θ j (-z) = symK θ j z := by
  unfold symK
  rw [Real.fourierInv_eq', Real.fourierInv_eq']
  rw [← integral_neg_eq_self (fun ξ : 𝔼 => (Complex.exp (↑(2 * Real.pi * inner ℝ ξ (-z)) * Complex.I)) •
    θ (((2 : ℝ) ^ j)⁻¹ • ξ)) volume]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul, inner_neg_left, inner_neg_right, smul_neg, he]
  ring_nf

/-- the adjoint identity for convolutions: `∫ (K ⋆ u) v = ∫ u (K^~ ⋆ v)` -/
lemma adj_cv {K u v : 𝔼 → ℂ} (hK : Integrable K) (hKm : Measurable K) (hu : Integrable u)
    (hum : Measurable u) (hv : Measurable v) {B : ℝ} (hB : ∀ x, ‖v x‖ ≤ B) :
    ∫ x, cv K u x * v x = ∫ y, u y * cv (fun z => K (-z)) v y := by
  set F2 : 𝔼 → 𝔼 → ℂ := fun x y => K (x - y) * u y * v x with hF2
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hint : Integrable (Function.uncurry F2) (volume.prod volume) := by
    have h1 : Integrable (fun p : 𝔼 × 𝔼 => ‖u p.2‖ * ‖K (p.1 - p.2)‖) (volume.prod volume) := by
      have := Integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hu.norm hK.norm
      simpa using this
    refine (h1.const_mul B).mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact (((hKm.comp (measurable_fst.sub measurable_snd)).mul (hum.comp measurable_snd)).mul
        (hv.comp measurable_fst)).aestronglyMeasurable
    · simp only [Function.uncurry, hF2]
      rw [norm_mul, norm_mul]
      have := hB p.1
      calc ‖K (p.1 - p.2)‖ * ‖u p.2‖ * ‖v p.1‖ ≤ ‖K (p.1 - p.2)‖ * ‖u p.2‖ * B := by gcongr
        _ = B * (‖u p.2‖ * ‖K (p.1 - p.2)‖) := by ring
  have e1 : ∀ x, cv K u x * v x = ∫ y, F2 x y := by
    intro x
    rw [cv_apply, ← integral_mul_const]
    have := integral_sub_left_eq_self (μ := (volume : Measure 𝔼))
      (fun w => K (x - w) * u w * v x) x
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hF2, sub_sub_cancel]
  have e2 : ∀ y, u y * cv (fun z => K (-z)) v y = ∫ x, F2 x y := by
    intro y
    rw [cv_apply, ← integral_const_mul]
    have := integral_sub_left_eq_self (μ := (volume : Measure 𝔼))
      (fun x => K (x - y) * u y * v x) y
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hF2, sub_sub_cancel_left, neg_sub]
    ring
  calc ∫ x, cv K u x * v x = ∫ x, ∫ y, F2 x y := integral_congr_ae (Eventually.of_forall e1)
    _ = ∫ y, ∫ x, F2 x y := integral_integral_swap hint
    _ = ∫ y, u y * cv (fun z => K (-z)) v y := integral_congr_ae (Eventually.of_forall fun y => (e2 y).symm)

end HRS.Commutator.Whole.XLI
