import HRS.MS.S21G2_M16

/-!
# S21K2 P07A -- finite-dimensional Gaussian toolbox for the heat-equation packet (R26-T3.P07)

`gam S = multivariateGaussian 0 S`: convolution `gam (S+D) = gam S ∗ gam D`, identification of a centered Gaussian measure on
`Euc n` by its coordinate covariance, coordinate moments, and the absolute moments `E‖w‖^(m+1) <= K (sqrt tr D)^(m+1)`.
Helper prefix `s21k2_p07_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace HRS.MS.R26T3

def s21k2_p07_gam {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) : Measure (HRS.Euc n) :=
  multivariateGaussian 0 S

instance s21k2_p07_gam_gauss {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) : IsGaussian (s21k2_p07_gam S) := by
  unfold s21k2_p07_gam; infer_instance

theorem s21k2_p07_gam_conv {n : ℕ} {S D : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef)
    (hD : D.PosSemidef) : s21k2_p07_gam (S + D) = s21k2_p07_gam S ∗ s21k2_p07_gam D := by
  refine Measure.ext_of_charFun (funext fun x => ?_)
  rw [charFun_conv]
  unfold s21k2_p07_gam
  rw [charFun_multivariateGaussian (hS.add hD), charFun_multivariateGaussian hS,
    charFun_multivariateGaussian hD, ← Complex.exp_add]
  congr 1
  simp [Matrix.add_mulVec, dotProduct_add]
  ring

theorem s21k2_p07_integral_coord {n : ℕ} (ν : Measure (HRS.Euc n)) [IsGaussian ν] (i : Fin n) :
    ∫ w, w.ofLp i ∂ν = (∫ w, w ∂ν).ofLp i :=
  ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj i : HRS.Euc n →L[ℝ] ℝ)
    (IsGaussian.integrable_id (μ := ν))

theorem s21k2_p07_mean_zero {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    ∫ w, w i ∂(s21k2_p07_gam S) = 0 := by
  have h := s21k2_p07_integral_coord (s21k2_p07_gam S) i
  rw [h]
  unfold s21k2_p07_gam
  simp

theorem s21k2_p07_second {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef) (i j : Fin n) :
    ∫ w, w i * w j ∂(s21k2_p07_gam S) = S i j := by
  have h := covariance_eval_multivariateGaussian (μ := (0 : HRS.Euc n)) hS i j
  unfold covariance at h
  have hm := s21k2_p07_mean_zero S
  unfold s21k2_p07_gam at hm ⊢
  simpa [hm] using h

theorem s21k2_p07_coord_memLp {n : ℕ} (ν : Measure (HRS.Euc n)) [IsGaussian ν] (i : Fin n) :
    MemLp (fun w : HRS.Euc n => w.ofLp i) 2 ν :=
  (EuclideanSpace.proj i : HRS.Euc n →L[ℝ] ℝ).comp_memLp' (IsGaussian.memLp_two_id)

/-- covariance form of a centered Gaussian measure in coordinates -/
theorem s21k2_p07_cov_form {n : ℕ} (ν : Measure (HRS.Euc n)) [IsGaussian ν]
    (hm : ∀ i, ∫ w, w i ∂ν = 0) (x y : HRS.Euc n) :
    covarianceBilin ν x y = ∑ i, ∑ j, x i * y j * ∫ w, w i * w j ∂ν := by
  have hmean : ∫ z, id z ∂ν = 0 := by
    ext i
    have h := s21k2_p07_integral_coord ν i
    simp only [id]
    rw [← h]; simpa using hm i
  rw [covarianceBilin_apply (IsGaussian.memLp_two_id), hmean]
  simp only [sub_zero]
  have hint : ∀ i j, Integrable (fun w : HRS.Euc n => w.ofLp i * w.ofLp j) ν := fun i j =>
    (s21k2_p07_coord_memLp ν i).integrable_mul (s21k2_p07_coord_memLp ν j)
  have e : ∀ w : HRS.Euc n, inner ℝ x w * inner ℝ y w =
      ∑ i, ∑ j, x i * y j * (w i * w j) := fun w => by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hint i j).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (hint i j).const_mul _]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

/-- a centered Gaussian measure with covariance matrix `S` is `gam S` -/
theorem s21k2_p07_eq_gam {n : ℕ} (ν : Measure (HRS.Euc n)) [IsGaussian ν]
    (hm : ∀ i, ∫ w, w i ∂ν = 0) {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef)
    (hc : ∀ i j, ∫ w, w i * w j ∂ν = S i j) : ν = s21k2_p07_gam S := by
  refine IsGaussian.ext ?_ ?_
  · have h1 : ∫ z, id z ∂ν = 0 := by
      ext i
      have h := s21k2_p07_integral_coord ν i
      simp only [id]
      rw [← h]; simpa using hm i
    rw [h1]
    unfold s21k2_p07_gam
    simp
  · ext x y
    rw [s21k2_p07_cov_form ν hm, s21k2_p07_cov_form (s21k2_p07_gam S) (s21k2_p07_mean_zero S)]
    simp_rw [hc, s21k2_p07_second hS]


theorem s21k2_p07_abs_moment (p : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ v : ℝ≥0, ∫ x, |x| ^ p ∂(gaussianReal 0 v) = c * (Real.sqrt v) ^ p := by
  refine ⟨∫ x, |x| ^ p ∂(gaussianReal 0 1), integral_nonneg fun x => by positivity, fun v => ?_⟩
  have h := gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt v)
  have e : (NNReal.mk (Real.sqrt v ^ 2) (sq_nonneg _)) * 1 = v := by
    ext; simp [Real.sq_sqrt]
  rw [mul_zero, e] at h
  rw [← h, integral_map (measurable_const_mul _).aemeasurable
    (by fun_prop : Continuous fun x : ℝ => |x| ^ p).aestronglyMeasurable]
  simp_rw [abs_mul, mul_pow, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [integral_const_mul, mul_comm]

theorem s21k2_p07_norm_le_sum {n : ℕ} (w : HRS.Euc n) : ‖w‖ ≤ ∑ i, |w.ofLp i| := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr w]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  simp [norm_smul]

theorem s21k2_p07_moment (n m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ D : Matrix (Fin n) (Fin n) ℝ, D.PosSemidef →
      ∫ w, ‖w‖ ^ (m + 1) ∂(s21k2_p07_gam D) ≤ K * (Real.sqrt D.trace) ^ (m + 1) := by
  obtain ⟨c, hc0, hc⟩ := s21k2_p07_abs_moment (m + 1)
  refine ⟨(n : ℝ) ^ m * (n * c), by positivity, fun D hD => ?_⟩
  have hdiag : ∀ i, 0 ≤ D i i := fun i => hD.diag_nonneg
  have hint : ∀ i, Integrable (fun w : HRS.Euc n => |w.ofLp i| ^ (m + 1)) (s21k2_p07_gam D) := fun i => by
    have h := (EuclideanSpace.proj i : HRS.Euc n →L[ℝ] ℝ).comp_memLp'
      (IsGaussian.memLp_id (s21k2_p07_gam D) (m + 1 : ℕ) (by simp))
    simpa [Real.norm_eq_abs] using h.integrable_norm_pow (by simp)
  have hpt : ∀ w : HRS.Euc n, ‖w‖ ^ (m + 1) ≤ (n : ℝ) ^ m * ∑ i, |w.ofLp i| ^ (m + 1) := fun w => by
    refine (pow_le_pow_left₀ (norm_nonneg _) (s21k2_p07_norm_le_sum w) _).trans ?_
    simpa using pow_sum_le_card_mul_sum_pow (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => |w.ofLp i|) (fun i _ => abs_nonneg _) m
  have hnorm : Integrable (fun w : HRS.Euc n => ‖w‖ ^ (m + 1)) (s21k2_p07_gam D) :=
    ((IsGaussian.memLp_id (s21k2_p07_gam D) (m + 1 : ℕ) (by simp)).integrable_norm_pow (by simp))
  calc ∫ w, ‖w‖ ^ (m + 1) ∂(s21k2_p07_gam D)
      ≤ ∫ w, (n : ℝ) ^ m * ∑ i, |w.ofLp i| ^ (m + 1) ∂(s21k2_p07_gam D) :=
        integral_mono hnorm ((integrable_finsetSum _ fun i _ => hint i).const_mul _) hpt
    _ = (n : ℝ) ^ m * ∑ i, ∫ w, |w.ofLp i| ^ (m + 1) ∂(s21k2_p07_gam D) := by
        rw [integral_const_mul, integral_finsetSum _ fun i _ => hint i]
    _ ≤ (n : ℝ) ^ m * (n * c * (Real.sqrt D.trace) ^ (m + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have : ∀ i, ∫ w, |w.ofLp i| ^ (m + 1) ∂(s21k2_p07_gam D) ≤ c * (Real.sqrt D.trace) ^ (m + 1) := fun i => by
          have hm := (measurePreserving_eval_multivariateGaussian (μ := (0 : HRS.Euc n)) hD (i := i))
          have e := integral_map (μ := s21k2_p07_gam D) hm.measurable.aemeasurable
            (f := fun x : ℝ => |x| ^ (m + 1))
            (by fun_prop : Continuous fun x : ℝ => |x| ^ (m + 1)).aestronglyMeasurable
          have hmap : (s21k2_p07_gam D).map (fun w : HRS.Euc n => w.ofLp i) =
              gaussianReal 0 (D i i).toNNReal := by
            have := hm.map_eq
            simpa [s21k2_p07_gam] using this
          rw [hmap, hc] at e
          rw [← e]
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.sqrt_nonneg _) ?_ _) hc0
          rw [Real.coe_toNNReal _ (hdiag i)]
          exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j => D j j) (fun j _ => hdiag j)
            (Finset.mem_univ i))
        calc _ ≤ ∑ _i : Fin n, c * (Real.sqrt D.trace) ^ (m + 1) := Finset.sum_le_sum fun i _ => this i
          _ = _ := by simp; ring
    _ = _ := by ring

end HRS.MS.R26T3
