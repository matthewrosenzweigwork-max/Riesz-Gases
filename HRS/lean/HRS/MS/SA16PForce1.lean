import Mathlib
import HRS.MS.CzPvAux1

/-!
# SA16P P4, part 1: the cancellation-convention convolution `Φ_K ρ` is bounded

For a scalar kernel `K` with `|K z| ≤ c |z|^{-(s+1)}` (`0 ≤ s < d`) and a function `ρ : ℝ^d → F` of class `C^1`
with `‖ρ y‖ ≤ A (1+|y|)^{-(d+3)}` and `‖Dρ y‖ ≤ A`, the integral
`Φ_K ρ (x) = ∫ K(z) (ρ(x-z) - 1_{|z| ≤ 1/4} ρ(x)) dz`
(the cancellation convention `convGradConvW`, after `y = x - z`) converges absolutely and `‖Φ_K ρ x‖ ≤ C₀ A`.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace HRS.Whole.AppendixA.Phase2SA16P

section Force
variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- the weight `(1+|y|)^{-(d+3)}` -/
def sa16p_w (d : ℕ) (y : EuclideanSpace ℝ (Fin d)) : ℝ := (1 + ‖y‖) ^ (-((d : ℝ) + 3))

lemma sa16p_w_integrable : Integrable (sa16p_w d) (volume : Measure 𝔼) := by
  unfold sa16p_w
  refine integrable_one_add_norm (E := 𝔼) ?_
  rw [finrank_euclideanSpace_fin]; linarith

lemma sa16p_w_pos (y : 𝔼) : 0 < sa16p_w d y := Real.rpow_pos_of_pos (by positivity) _

lemma sa16p_w_le_one (y : 𝔼) : sa16p_w d y ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith)

lemma sa16p_w_shift (x₀ x z : 𝔼) (hx : ‖x - x₀‖ ≤ 1) :
    sa16p_w d (x - z) ≤ 2 ^ ((d : ℝ) + 3) * sa16p_w d (x₀ - z) := by
  unfold sa16p_w
  have h1 : (1 + ‖x₀ - z‖) / 2 ≤ 1 + ‖x - z‖ := by
    have : ‖x₀ - z‖ ≤ ‖x - z‖ + ‖x - x₀‖ := by
      calc ‖x₀ - z‖ = ‖(x - z) - (x - x₀)‖ := by congr 1; abel
        _ ≤ ‖x - z‖ + ‖x - x₀‖ := norm_sub_le _ _
    linarith [norm_nonneg (x - z)]
  have h2 : (0 : ℝ) < (1 + ‖x₀ - z‖) / 2 := by positivity
  have h3 : (1 + ‖x - z‖) ^ (-((d : ℝ) + 3)) ≤ ((1 + ‖x₀ - z‖) / 2) ^ (-((d : ℝ) + 3)) :=
    Real.rpow_le_rpow_of_nonpos h2 h1 (by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith)
  refine h3.trans (le_of_eq ?_)
  rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    div_inv_eq_mul, mul_comm]

/-- the cancellation-convention integrand -/
def sa16p_phiI (K : 𝔼 → ℝ) (ρ : 𝔼 → F) (x z : 𝔼) : F :=
  K z • (ρ (x - z) - (if ‖z‖ ≤ 1 / 4 then ρ x else 0))

/-- `Φ_K ρ (x)` -/
def sa16p_phiF (K : 𝔼 → ℝ) (ρ : 𝔼 → F) (x : 𝔼) : F := ∫ z, sa16p_phiI K ρ x z

lemma sa16p_mvt {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : 𝔼 → G}
    (hf : Differentiable ℝ f) {A : ℝ} (hA : ∀ y, ‖fderiv ℝ f y‖ ≤ A) (x y : 𝔼) :
    ‖f y - f x‖ ≤ A * ‖y - x‖ :=
  Convex.norm_image_sub_le_of_norm_fderiv_le (s := Set.univ) (fun y _ => hf y) (fun y _ => hA y)
    convex_univ (Set.mem_univ x) (Set.mem_univ y)

section Bound
variable {s : ℝ}

/-- the two constants -/
def sa16p_I1 (d : ℕ) (s : ℝ) : ℝ :=
  ∫ z in closedBall (0 : EuclideanSpace ℝ (Fin d)) (1 / 4), ‖z‖ ^ (-s)

def sa16p_I2 (d : ℕ) : ℝ := ∫ z : EuclideanSpace ℝ (Fin d), sa16p_w d z

/-- the constant `C₀` -/
def sa16p_C0 (d : ℕ) (c s : ℝ) : ℝ := c * (sa16p_I1 d s + 4 ^ (s + 1) * sa16p_I2 d)

lemma sa16p_I1_integrable (hd : 1 ≤ d) (hsd : s < d) :
    IntegrableOn (fun z : 𝔼 => ‖z‖ ^ (-s)) (closedBall (0 : 𝔼) (1 / 4)) :=
  (HRS.CZ.Pv.pvapi_integrableOn_ball_rpow hd hsd 1).mono_set
    (closedBall_subset_ball (by norm_num))

/-- pointwise bound of the integrand by `B1 + B2` -/
lemma sa16p_phiI_bound {K : 𝔼 → ℝ} {c s A : ℝ} {ρ : 𝔼 → F} (hc : 0 ≤ c) (hs0 : 0 ≤ s) (hK : ∀ z, z ≠ 0 → |K z| ≤ c * ‖z‖ ^ (-s - 1))
    (hρ : Differentiable ℝ ρ) (hρw : ∀ y, ‖ρ y‖ ≤ A * sa16p_w d y) (hρ1 : ∀ y, ‖fderiv ℝ ρ y‖ ≤ A)
    (x z : 𝔼) :
    ‖sa16p_phiI K ρ x z‖ ≤ (closedBall (0 : 𝔼) (1 / 4)).indicator (fun z => c * A * ‖z‖ ^ (-s)) z +
      c * 4 ^ (s + 1) * A * sa16p_w d (x - z) := by
  have hA : 0 ≤ A := (norm_nonneg _).trans (hρ1 0)
  have hw0 := sa16p_w_pos (d := d) (x - z)
  by_cases hz0 : z = 0
  · subst hz0
    have hL : sa16p_phiI K ρ x 0 = 0 := by simp [sa16p_phiI]
    rw [hL, norm_zero]
    have h1 : 0 ≤ (closedBall (0 : 𝔼) (1 / 4)).indicator (fun z => c * A * ‖z‖ ^ (-s)) 0 := by
      rw [Set.indicator_of_mem (by simp)]
      exact mul_nonneg (mul_nonneg hc hA) (Real.rpow_nonneg (norm_nonneg _) _)
    have h2 : 0 ≤ c * 4 ^ (s + 1) * A * sa16p_w d (x - 0) := by positivity
    exact add_nonneg h1 h2
  · have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
    have hKz := hK z hz0
    by_cases hn : ‖z‖ ≤ 1 / 4
    · have hmem : z ∈ closedBall (0 : 𝔼) (1 / 4) := by simpa using hn
      rw [Set.indicator_of_mem hmem]
      have h2 : 0 ≤ c * 4 ^ (s + 1) * A * sa16p_w d (x - z) := by positivity
      simp only [sa16p_phiI, hn, if_true, norm_smul, Real.norm_eq_abs]
      have h3 : ‖ρ (x - z) - ρ x‖ ≤ A * ‖z‖ := by
        have := sa16p_mvt hρ hρ1 x (x - z)
        rwa [sub_sub_cancel_left, norm_neg] at this
      calc |K z| * ‖ρ (x - z) - ρ x‖ ≤ (c * ‖z‖ ^ (-s - 1)) * (A * ‖z‖) :=
            mul_le_mul hKz h3 (norm_nonneg _) (by positivity)
        _ = c * A * ‖z‖ ^ (-s) := by
            have : ‖z‖ ^ (-s) = ‖z‖ ^ (-s - 1) * ‖z‖ := by
              rw [← Real.rpow_add_one hzpos.ne']; congr 1; ring
            rw [this]; ring
        _ ≤ _ := le_add_of_nonneg_right h2
    · have hmem : z ∉ closedBall (0 : 𝔼) (1 / 4) := by simpa using hn
      rw [Set.indicator_of_notMem hmem, zero_add]
      push_neg at hn
      simp only [sa16p_phiI, not_le.2 hn, if_false, sub_zero, norm_smul, Real.norm_eq_abs]
      have h4 : ‖z‖ ^ (-s - 1) ≤ 4 ^ (s + 1) := by
        have : (4 : ℝ) ^ (s + 1) = (1 / 4 : ℝ) ^ (-s - 1) := by
          rw [show (1 / 4 : ℝ) = 4⁻¹ by norm_num, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
          congr 1; ring
        rw [this]
        exact Real.rpow_le_rpow_of_nonpos (by norm_num) hn.le (by linarith)
      calc |K z| * ‖ρ (x - z)‖ ≤ (c * 4 ^ (s + 1)) * (A * sa16p_w d (x - z)) :=
            mul_le_mul ((hKz).trans (mul_le_mul_of_nonneg_left h4 hc)) (hρw _) (norm_nonneg _) (by positivity)
        _ = _ := by ring

lemma sa16p_phiI_aesm {K : 𝔼 → ℝ} (hKm : Measurable K) {ρ : 𝔼 → F} (hρ : Continuous ρ) (x : 𝔼) :
    AEStronglyMeasurable (sa16p_phiI K ρ x) (volume : Measure 𝔼) := by
  have h1 : AEStronglyMeasurable (fun z : 𝔼 => if ‖z‖ ≤ 1 / 4 then ρ x else 0) volume := by
    have := (aestronglyMeasurable_const (b := ρ x)).indicator
      (measurableSet_closedBall (x := (0 : 𝔼)) (ε := 1 / 4)) (μ := volume)
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp [Set.indicator, mem_closedBall_zero_iff]
  exact hKm.aestronglyMeasurable.smul ((hρ.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.sub h1)

/-- integrability and the bound `‖Φ_K ρ x‖ ≤ C₀ A` -/
lemma sa16p_phi_bound (hd : 1 ≤ d) {K : 𝔼 → ℝ} (hKm : Measurable K) {c s A : ℝ} (hc : 0 ≤ c)
    (hs0 : 0 ≤ s) (hsd : s < d) (hK : ∀ z, z ≠ 0 → |K z| ≤ c * ‖z‖ ^ (-s - 1)) {ρ : 𝔼 → F}
    (hρ : Differentiable ℝ ρ) (hρw : ∀ y, ‖ρ y‖ ≤ A * sa16p_w d y) (hρ1 : ∀ y, ‖fderiv ℝ ρ y‖ ≤ A)
    (x : 𝔼) :
    Integrable (sa16p_phiI K ρ x) volume ∧ ‖sa16p_phiF K ρ x‖ ≤ sa16p_C0 d c s * A := by
  have hA : 0 ≤ A := (norm_nonneg _).trans (hρ1 0)
  have hB1 : Integrable ((closedBall (0 : 𝔼) (1 / 4)).indicator (fun z => c * A * ‖z‖ ^ (-s))) volume :=
    (integrable_indicator_iff measurableSet_closedBall).2 ((sa16p_I1_integrable hd hsd).const_mul (c * A))
  have hB2 : Integrable (fun z : 𝔼 => c * 4 ^ (s + 1) * A * sa16p_w d (x - z)) volume :=
    (sa16p_w_integrable.comp_sub_left x).const_mul _
  have hint : Integrable (sa16p_phiI K ρ x) volume :=
    Integrable.mono' (hB1.add hB2) (sa16p_phiI_aesm hKm hρ.continuous x)
      (Eventually.of_forall fun z => sa16p_phiI_bound hc hs0 hK hρ hρw hρ1 x z)
  refine ⟨hint, ?_⟩
  calc ‖sa16p_phiF K ρ x‖ ≤ ∫ z, ‖sa16p_phiI K ρ x z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, ((closedBall (0 : 𝔼) (1 / 4)).indicator (fun z => c * A * ‖z‖ ^ (-s)) z +
          c * 4 ^ (s + 1) * A * sa16p_w d (x - z)) :=
        integral_mono hint.norm (hB1.add hB2) (fun z => sa16p_phiI_bound hc hs0 hK hρ hρw hρ1 x z)
    _ = c * A * sa16p_I1 d s + c * 4 ^ (s + 1) * A * sa16p_I2 d := by
        rw [integral_add hB1 hB2, integral_indicator measurableSet_closedBall, integral_const_mul,
          integral_const_mul, integral_sub_left_eq_self (fun z => sa16p_w d z) volume x]
        rfl
    _ = sa16p_C0 d c s * A := by unfold sa16p_C0; ring

end Bound

end Force

end HRS.Whole.AppendixA.Phase2SA16P
