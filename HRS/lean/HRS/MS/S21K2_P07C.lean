import HRS.MS.S21K2_P07A
import HRS.MS.S21K2_P07B

/-!
# S21K2 P07C -- one Gaussian step of the heat function (R26-T3.P07)

For `Phi in C^3` with bounded `Phi, D^2 Phi, D^3 Phi` and PSD matrices `S, D`, with `U S = E Phi(y + G_S)`,
`hh S i j = E d_i d_j Phi(y + G_S)`:
`|U(S+D) - U S - 1/2 sum D_ij hh S i j| <= C E|W_D|^3` and `|hh(S+D) i j - hh S i j| <= C E|W_D|`.
(Independent sum `G_S + W_D ~ G_{S+D}` through characteristic functions; Taylor estimate of file `P07B`.)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace HRS.MS.R26T3

theorem s21k2_p07_inner_step {n : ℕ} {Φ : HRS.Euc n → ℝ} (hΦ : ContDiff ℝ 3 Φ) {B0 C : ℝ}
    (hB0 : ∀ z, ‖Φ z‖ ≤ B0) (hC : ∀ z, ‖iteratedFDeriv ℝ 3 Φ z‖ ≤ C)
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosSemidef) (z : HRS.Euc n) :
    |∫ w, Φ (z + w) ∂(s21k2_p07_gam D) - Φ z - (1 / 2) * ∑ i, ∑ j, D i j *
        iteratedFDeriv ℝ 2 Φ z ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]| ≤
      C * ∫ w, ‖w‖ ^ 3 ∂(s21k2_p07_gam D) := by
  set κ := s21k2_p07_gam D with hκ
  have hΦc : Continuous Φ := hΦ.continuous
  set L : HRS.Euc n →L[ℝ] ℝ := fderiv ℝ Φ z with hL
  set Bm : HRS.Euc n →L[ℝ] HRS.Euc n →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ Φ) z with hBm
  have hB2 : ∀ w : HRS.Euc n, iteratedFDeriv ℝ 2 Φ z ![w, w] = Bm w w := fun w => by
    rw [iteratedFDeriv_two_apply]; rfl
  have hBe : ∀ i j, iteratedFDeriv ℝ 2 Φ z ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] =
      Bm (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := fun i j => by
    rw [iteratedFDeriv_two_apply]; rfl
  have hint2 : ∀ i j, Integrable (fun w : HRS.Euc n => w.ofLp i * w.ofLp j) κ := fun i j =>
    (s21k2_p07_coord_memLp κ i).integrable_mul (s21k2_p07_coord_memLp κ j)
  have hint1 : ∀ i, Integrable (fun w : HRS.Euc n => w.ofLp i) κ := fun i =>
    (s21k2_p07_coord_memLp κ i).integrable one_le_two
  have hf1 : Integrable (fun w : HRS.Euc n => Φ (z + w)) κ :=
    Integrable.of_bound (C := B0) ((hΦc.comp (continuous_const.add continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall fun w => hB0 _)
  have hf2 : Integrable (fun w : HRS.Euc n => L w) κ := by
    have h : Integrable (fun w : HRS.Euc n => ∑ i, w.ofLp i * L (EuclideanSpace.single i 1)) κ :=
      integrable_finsetSum _ fun i _ => (hint1 i).mul_const _
    exact h.congr (Eventually.of_forall fun w => (s21k2_p07_expand1 L w).symm)
  have hf3 : Integrable (fun w : HRS.Euc n => Bm w w) κ := by
    have h : Integrable (fun w : HRS.Euc n => ∑ i, ∑ j, w.ofLp i * w.ofLp j *
        Bm (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) κ :=
      integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hint2 i j).mul_const _
    exact h.congr (Eventually.of_forall fun w => (s21k2_p07_expand2 Bm w).symm)
  have hI2 : ∫ w, L w ∂κ = 0 := by
    have e : (fun w : HRS.Euc n => L w) = fun w => ∑ i, w.ofLp i * L (EuclideanSpace.single i 1) :=
      funext (s21k2_p07_expand1 L)
    rw [e, integral_finsetSum _ fun i _ => (hint1 i).mul_const _]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_mul_const, hκ, s21k2_p07_mean_zero, zero_mul]
  have hI3 : ∫ w, Bm w w ∂κ = ∑ i, ∑ j, D i j * Bm (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    have e : (fun w : HRS.Euc n => Bm w w) = fun w => ∑ i, ∑ j, w.ofLp i * w.ofLp j *
        Bm (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := funext (s21k2_p07_expand2 Bm)
    rw [e, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hint2 i j).mul_const _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hint2 i j).mul_const _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_mul_const, hκ, s21k2_p07_second hD]
  have hnorm : Integrable (fun w : HRS.Euc n => ‖w‖ ^ 3) κ :=
    (IsGaussian.memLp_id κ (3 : ℕ) (by simp)).integrable_norm_pow (by simp)
  have hsum : ∑ i, ∑ j, D i j *
      iteratedFDeriv ℝ 2 Φ z ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] =
      ∑ i, ∑ j, D i j * Bm (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    simp only [hBe]
  have h1 : ∫ w, (Φ (z + w) - Φ z - L w - (1 / 2) * Bm w w) ∂κ =
      ∫ w, Φ (z + w) ∂κ - Φ z - ∫ w, L w ∂κ - (1 / 2) * ∫ w, Bm w w ∂κ := by
    have hi1 : Integrable (fun w : HRS.Euc n => Φ (z + w) - Φ z) κ := hf1.sub (integrable_const _)
    have hi2 : Integrable (fun w : HRS.Euc n => Φ (z + w) - Φ z - L w) κ := hi1.sub hf2
    have hi3 : Integrable (fun w : HRS.Euc n => (1 / 2 : ℝ) * Bm w w) κ := hf3.const_mul _
    rw [integral_sub hi2 hi3, integral_sub hi1 hf2, integral_sub hf1 (integrable_const _),
      integral_const_mul]
    simp
  have hmain : ∫ w, Φ (z + w) ∂κ - Φ z - (1 / 2) * ∑ i, ∑ j, D i j *
      iteratedFDeriv ℝ 2 Φ z ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] =
      ∫ w, (Φ (z + w) - Φ z - L w - (1 / 2) * Bm w w) ∂κ := by
    rw [h1, hI2, hI3, hsum]; ring
  rw [hmain, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (hnorm.const_mul C) (Eventually.of_forall fun w => ?_)).trans
    (le_of_eq (integral_const_mul _ _))
  have := s21k2_p07_taylor hΦ hC z w
  rw [Real.norm_eq_abs]
  simpa [hB2, hL, hBm] using this


/-- `U S = ∫ Φ(y + x) d gam S`. -/
def s21k2_p07_U {n : ℕ} (Φ : HRS.Euc n → ℝ) (y : HRS.Euc n) (S : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∫ x, Φ (y + x) ∂(s21k2_p07_gam S)

/-- `hh S i j = ∫ ∂_i ∂_j Φ(y + x) d gam S`. -/
def s21k2_p07_hh {n : ℕ} (Φ : HRS.Euc n → ℝ) (y : HRS.Euc n) (S : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) : ℝ :=
  ∫ x, iteratedFDeriv ℝ 2 Φ (y + x) ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] ∂(s21k2_p07_gam S)

theorem s21k2_p07_conv_shift {n : ℕ} {S D : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef)
    (hD : D.PosSemidef) {f : HRS.Euc n → ℝ} (hf : Continuous f) {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B)
    (y : HRS.Euc n) :
    ∫ x, f (y + x) ∂(s21k2_p07_gam (S + D)) =
      ∫ g, ∫ w, f ((y + g) + w) ∂(s21k2_p07_gam D) ∂(s21k2_p07_gam S) := by
  rw [s21k2_p07_gam_conv hS hD]
  have := s21k2_p07_conv_integral (s21k2_p07_gam S) (s21k2_p07_gam D)
    (f := fun x => f (y + x)) (hf.comp (continuous_const.add continuous_id)) (B := B) (fun x => hB _)
  simpa [add_assoc] using this

theorem s21k2_p07_integrable_inner {n : ℕ} (ν κ : Measure (HRS.Euc n)) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure κ] {f : HRS.Euc n → ℝ} (hf : Continuous f) {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B)
    (y : HRS.Euc n) : Integrable (fun g => ∫ w, f ((y + g) + w) ∂κ) ν := by
  have : Integrable (fun p : HRS.Euc n × HRS.Euc n => f ((y + p.1) + p.2)) (ν.prod κ) :=
    Integrable.of_bound (C := B) ((hf.comp ((continuous_const.add continuous_fst).add continuous_snd)).aestronglyMeasurable)
      (Eventually.of_forall fun p => hB _)
  exact this.integral_prod_left

theorem s21k2_p07_core_lin {n : ℕ} (ν κ : Measure (HRS.Euc n)) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure κ] {f : HRS.Euc n → ℝ} (hf : Continuous f) {B0 : ℝ} (hB0 : ∀ z, ‖f z‖ ≤ B0)
    (F : Fin n → Fin n → HRS.Euc n → ℝ) (hF : ∀ i j, Continuous (F i j)) {B2 : ℝ}
    (hFb : ∀ i j z, ‖F i j z‖ ≤ B2) (c : Fin n → Fin n → ℝ) {M : ℝ}
    (hM : ∀ z, |∫ w, f (z + w) ∂κ - f z - (1 / 2) * ∑ i, ∑ j, c i j * F i j z| ≤ M) (y : HRS.Euc n) :
    |∫ g, ∫ w, f ((y + g) + w) ∂κ ∂ν - ∫ g, f (y + g) ∂ν -
      (1 / 2) * ∑ i, ∑ j, c i j * ∫ g, F i j (y + g) ∂ν| ≤ M := by
  have hi1 := s21k2_p07_integrable_inner ν κ hf hB0 y
  have hi2 : Integrable (fun g : HRS.Euc n => f (y + g)) ν :=
    Integrable.of_bound (C := B0) ((hf.comp (continuous_const.add continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall fun w => hB0 _)
  have hi3 : ∀ i j : Fin n, Integrable (fun g : HRS.Euc n => F i j (y + g)) ν := fun i j =>
    Integrable.of_bound (C := B2) (((hF i j).comp (continuous_const.add continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall fun w => hFb i j _)
  have hs : Integrable (fun g : HRS.Euc n => (1 / 2 : ℝ) * ∑ i, ∑ j, c i j * F i j (y + g)) ν :=
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hi3 i j).const_mul _).const_mul _
  have hd1 : Integrable (fun g : HRS.Euc n => ∫ w, f ((y + g) + w) ∂κ - f (y + g)) ν := hi1.sub hi2
  have hlin : ∫ g, ∫ w, f ((y + g) + w) ∂κ ∂ν - ∫ g, f (y + g) ∂ν -
      (1 / 2) * ∑ i, ∑ j, c i j * ∫ g, F i j (y + g) ∂ν =
      ∫ g, (∫ w, f ((y + g) + w) ∂κ - f (y + g) - (1 / 2) * ∑ i, ∑ j, c i j * F i j (y + g)) ∂ν := by
    rw [integral_sub hd1 hs, integral_sub hi1 hi2, integral_const_mul,
      integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hi3 i j).const_mul _]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hi3 i j).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
  rw [hlin, ← Real.norm_eq_abs]
  refine le_trans (norm_integral_le_of_norm_le_const (C := M) (Eventually.of_forall fun g => ?_)) ?_
  · rw [Real.norm_eq_abs]
    exact hM (y + g)
  · simp

theorem s21k2_p07_hF {n : ℕ} {Φ : HRS.Euc n → ℝ} (hΦ : ContDiff ℝ 3 Φ) {B2 : ℝ}
    (hB2 : ∀ z, ‖iteratedFDeriv ℝ 2 Φ z‖ ≤ B2) (i j : Fin n) :
    Continuous (fun z => iteratedFDeriv ℝ 2 Φ z ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]) ∧
    ∀ z, ‖iteratedFDeriv ℝ 2 Φ z ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]‖ ≤ B2 := by
  refine ⟨(ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => HRS.Euc n) ℝ
      ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]).continuous.comp
      (hΦ.continuous_iteratedFDeriv (by exact_mod_cast (by norm_num : 2 ≤ 3))), fun z => ?_⟩
  refine ((iteratedFDeriv ℝ 2 Φ z).le_opNorm _).trans ?_
  simp [Fin.prod_univ_two]
  exact hB2 z

theorem s21k2_p07_step_U {n : ℕ} {Φ : HRS.Euc n → ℝ} (hΦ : ContDiff ℝ 3 Φ) {B0 B2 C : ℝ}
    (hB0 : ∀ z, ‖Φ z‖ ≤ B0) (hB2 : ∀ z, ‖iteratedFDeriv ℝ 2 Φ z‖ ≤ B2)
    (hC : ∀ z, ‖iteratedFDeriv ℝ 3 Φ z‖ ≤ C) {S D : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef)
    (hD : D.PosSemidef) (y : HRS.Euc n) :
    |s21k2_p07_U Φ y (S + D) - s21k2_p07_U Φ y S - (1 / 2) * ∑ i, ∑ j, D i j * s21k2_p07_hh Φ y S i j| ≤
      C * ∫ w, ‖w‖ ^ 3 ∂(s21k2_p07_gam D) := by
  have hU1 : s21k2_p07_U Φ y (S + D) = ∫ g, ∫ w, Φ ((y + g) + w) ∂(s21k2_p07_gam D) ∂(s21k2_p07_gam S) :=
    s21k2_p07_conv_shift hS hD hΦ.continuous hB0 y
  have := s21k2_p07_core_lin (s21k2_p07_gam S) (s21k2_p07_gam D) hΦ.continuous hB0
    (fun i j z => iteratedFDeriv ℝ 2 Φ z ![EuclideanSpace.single i 1, EuclideanSpace.single j 1])
    (fun i j => (s21k2_p07_hF hΦ hB2 i j).1) (fun i j => (s21k2_p07_hF hΦ hB2 i j).2)
    (fun i j => D i j) (M := C * ∫ w, ‖w‖ ^ 3 ∂(s21k2_p07_gam D))
    (fun z => s21k2_p07_inner_step hΦ hB0 hC hD z) y
  rw [← hU1] at this
  exact this


theorem s21k2_p07_inner_hh {n : ℕ} {Φ : HRS.Euc n → ℝ} (hΦ : ContDiff ℝ 3 Φ) {B2 C : ℝ}
    (hB2 : ∀ z, ‖iteratedFDeriv ℝ 2 Φ z‖ ≤ B2) (hC : ∀ z, ‖iteratedFDeriv ℝ 3 Φ z‖ ≤ C)
    (κ : Measure (HRS.Euc n)) [IsGaussian κ] (i j : Fin n) (z : HRS.Euc n) :
    |∫ w, iteratedFDeriv ℝ 2 Φ (z + w) ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] ∂κ -
        iteratedFDeriv ℝ 2 Φ z ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]| ≤
      C * ∫ w, ‖w‖ ∂κ := by
  obtain ⟨hFc, hFb⟩ := s21k2_p07_hF hΦ hB2 i j
  have hi1 : Integrable (fun w : HRS.Euc n => iteratedFDeriv ℝ 2 Φ (z + w)
      ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]) κ :=
    Integrable.of_bound (C := B2) ((hFc.comp (continuous_const.add continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall fun w => hFb _)
  have hnorm : Integrable (fun w : HRS.Euc n => ‖w‖) κ :=
    (IsGaussian.memLp_id κ (1 : ℕ) (by simp)).integrable_norm_pow (by simp) |>.congr
      (Eventually.of_forall fun w => by simp)
  have e : ∫ w, iteratedFDeriv ℝ 2 Φ (z + w) ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] ∂κ -
        iteratedFDeriv ℝ 2 Φ z ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] =
      ∫ w, (iteratedFDeriv ℝ 2 Φ (z + w) ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] -
        iteratedFDeriv ℝ 2 Φ z ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]) ∂κ := by
    rw [integral_sub hi1 (integrable_const _)]; simp
  rw [e, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (hnorm.const_mul C) (Eventually.of_forall fun w => ?_)).trans
    (le_of_eq (integral_const_mul _ _))
  have h1 := s21k2_p07_lip2 hΦ hC z w
  have h2 := ((iteratedFDeriv ℝ 2 Φ (z + w) - iteratedFDeriv ℝ 2 Φ z).le_opNorm
    ![EuclideanSpace.single i 1, EuclideanSpace.single j 1])
  simp only [ContinuousMultilinearMap.sub_apply, Fin.prod_univ_two] at h2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, EuclideanSpace.norm_single, norm_one, mul_one] at h2
  exact h2.trans h1

theorem s21k2_p07_step_hh {n : ℕ} {Φ : HRS.Euc n → ℝ} (hΦ : ContDiff ℝ 3 Φ) {B2 C : ℝ}
    (hB2 : ∀ z, ‖iteratedFDeriv ℝ 2 Φ z‖ ≤ B2) (hC : ∀ z, ‖iteratedFDeriv ℝ 3 Φ z‖ ≤ C)
    {S D : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef) (hD : D.PosSemidef) (y : HRS.Euc n)
    (i j : Fin n) :
    |s21k2_p07_hh Φ y (S + D) i j - s21k2_p07_hh Φ y S i j| ≤ C * ∫ w, ‖w‖ ∂(s21k2_p07_gam D) := by
  obtain ⟨hFc, hFb⟩ := s21k2_p07_hF hΦ hB2 i j
  have h1 : s21k2_p07_hh Φ y (S + D) i j = ∫ g, ∫ w, iteratedFDeriv ℝ 2 Φ ((y + g) + w)
      ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] ∂(s21k2_p07_gam D) ∂(s21k2_p07_gam S) :=
    s21k2_p07_conv_shift hS hD hFc hFb y
  have hi1 := s21k2_p07_integrable_inner (s21k2_p07_gam S) (s21k2_p07_gam D) hFc hFb y
  have hi2 : Integrable (fun g : HRS.Euc n => iteratedFDeriv ℝ 2 Φ (y + g)
      ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]) (s21k2_p07_gam S) :=
    Integrable.of_bound (C := B2) ((hFc.comp (continuous_const.add continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall fun w => hFb _)
  have hd : Integrable (fun g : HRS.Euc n => ∫ w, iteratedFDeriv ℝ 2 Φ ((y + g) + w)
      ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] ∂(s21k2_p07_gam D) -
      iteratedFDeriv ℝ 2 Φ (y + g) ![EuclideanSpace.single i 1, EuclideanSpace.single j 1])
      (s21k2_p07_gam S) := hi1.sub hi2
  have e : s21k2_p07_hh Φ y (S + D) i j - s21k2_p07_hh Φ y S i j =
      ∫ g, (∫ w, iteratedFDeriv ℝ 2 Φ ((y + g) + w)
      ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] ∂(s21k2_p07_gam D) -
      iteratedFDeriv ℝ 2 Φ (y + g) ![EuclideanSpace.single i 1, EuclideanSpace.single j 1])
      ∂(s21k2_p07_gam S) := by
    rw [integral_sub hi1 hi2, h1]; rfl
  rw [e, ← Real.norm_eq_abs]
  refine le_trans (norm_integral_le_of_norm_le_const (C := C * ∫ w, ‖w‖ ∂(s21k2_p07_gam D))
    (Eventually.of_forall fun g => ?_)) ?_
  · rw [Real.norm_eq_abs]
    exact s21k2_p07_inner_hh hΦ hB2 hC (s21k2_p07_gam D) i j (y + g)
  · simp

end HRS.MS.R26T3
