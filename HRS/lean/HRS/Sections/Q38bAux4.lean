import HRS.Sections.Q38bAux3

/-!
# Packet Q38b, part 4: the stationary lag covariance on `e_k` and Gaussian moments

* `stationaryLagCov` for the homogeneous model on `e_k` is `exp(-λ_k|τ_a - τ_b|)/(1 + βĝ(k))`;
* a centred Gaussian vector in `ℝ²` with positive semidefinite covariance `S` has
  `E[W₀ W₁] = S₀₁`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS

variable {d : ℕ}

/-! ### The susceptibility form on `e_k` -/

theorem q38b_susc_left (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : NonzeroLattice d) (c : ℝ) :
    susceptibilityCov (periodicRiesz d s) (volume : Measure (Torus d)) β (Torus.realMode k)
      (fun y => c * Torus.realMode k y) = c * (1 + β * rieszCoeff d s k.1)⁻¹ := by
  unfold susceptibilityCov l2Inner
  have hp : projMean (volume : Measure (Torus d)) (Torus.realMode k) = Torus.realMode k := by
    funext x
    unfold projMean pair
    rw [Torus.integral_realMode, sub_zero]
  rw [hp]
  have hae := q38b_responseInverse_eq hd hs0 hsd hβ k c
  have : ∫ x : Torus d, Torus.realMode k x *
      responseInverse (periodicRiesz d s) (volume : Measure (Torus d)) β
        (fun y => c * Torus.realMode k y) x =
      ∫ x : Torus d, (c * (1 + β * rieszCoeff d s k.1)⁻¹) *
        (Torus.realMode k x * Torus.realMode k x) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
    ring
  rw [this, integral_const_mul, Torus.realMode_orthonormal k k]
  simp

theorem q38b_susc_right (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : NonzeroLattice d) (c : ℝ) :
    susceptibilityCov (periodicRiesz d s) (volume : Measure (Torus d)) β
      (fun y => c * Torus.realMode k y) (Torus.realMode k) =
      c * (1 + β * rieszCoeff d s k.1)⁻¹ := by
  unfold susceptibilityCov l2Inner
  have hp : projMean (volume : Measure (Torus d)) (fun y => c * Torus.realMode k y) =
      fun y => c * Torus.realMode k y := by
    funext x
    unfold projMean pair
    rw [q38b_int_c_realMode, sub_zero]
  rw [hp]
  have hf : (Torus.realMode k) = fun y => (1 : ℝ) * Torus.realMode k y := by
    funext y; simp
  have hae := q38b_responseInverse_eq hd hs0 hsd hβ k 1
  rw [← hf] at hae
  have : ∫ x : Torus d, c * Torus.realMode k x *
      responseInverse (periodicRiesz d s) (volume : Measure (Torus d)) β (Torus.realMode k) x =
      ∫ x : Torus d, (c * (1 + β * rieszCoeff d s k.1)⁻¹) *
        (Torus.realMode k x * Torus.realMode k x) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
    ring
  rw [this, integral_const_mul, Torus.realMode_orthonormal k k]
  simp

/-- The stationary lag covariance of the homogeneous model on the real mode `e_k`. -/
theorem q38b_lagCov_eq (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : NonzeroLattice d) {p : ℕ} (τ : Fin p → ℝ) (hτ : ∀ a, 0 ≤ τ a) :
    PDE.stationaryLagCov d s β (PDE.mfData d s hs0 hsd (fun _ => (0 : ℝ)) β hβ)
      (fun _ => (1 : ℝ)) τ (fun _ => Torus.realMode k) =
    Matrix.of fun a b => (1 + β * rieszCoeff d s k.1)⁻¹ *
      Real.exp (-(q38b_rate d s β k) * |τ a - τ b|) := by
  have hvol : (withDensityReal (fun _ : Torus d => (1 : ℝ))) = (volume : Measure (Torus d)) := by
    unfold withDensityReal
    simp
  ext a b
  unfold PDE.stationaryLagCov
  simp only [Matrix.of_apply, hvol]
  split_ifs with h
  · rw [q38b_equilibriumSemigroup hd hs0 hsd hβ k _ (sub_nonneg.2 h)]
    rw [q38b_susc_left hd hs0 hsd hβ k, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)]
    ring
  · have h' : τ b ≤ τ a := le_of_not_ge h
    rw [q38b_equilibriumSemigroup hd hs0 hsd hβ k _ (sub_nonneg.2 h')]
    rw [q38b_susc_right hd hs0 hsd hβ k, abs_of_nonneg (sub_nonneg.2 h')]
    ring

/-! ### Measurability of the mode coordinates -/

theorem q38b_continuous_coord {m : ℝ} (k : NonzeroLattice d) :
    Continuous (fun F : NegSobolev d m => NegSobolev.coord F k) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun F G => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm]
  let F' : lp (fun _ : NonzeroLattice d => ℝ) 2 := F
  let G' : lp (fun _ : NonzeroLattice d => ℝ) 2 := G
  have h := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (F' - G') k
  have h2 : (F' - G' : lp (fun _ : NonzeroLattice d => ℝ) 2) k = F' k - G' k := by
    rw [lp.coeFn_sub]; rfl
  rw [h2, Real.norm_eq_abs] at h
  rw [Real.norm_eq_abs, NNReal.coe_one, one_mul]
  exact h

theorem q38b_eval_realMode {m : ℝ} (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.eval F (Torus.realMode k) = NegSobolev.fourierCoeff F k := by
  classical
  unfold NegSobolev.eval
  rw [tsum_eq_single k]
  · unfold Torus.funRealCoeff
    rw [Torus.realMode_orthonormal k k]
    simp
  · intro l hl
    unfold Torus.funRealCoeff
    rw [Torus.realMode_orthonormal l k, if_neg hl]
    simp

theorem q38b_measurable_eval_realMode {m : ℝ} (k : NonzeroLattice d) :
    Measurable (fun F : NegSobolev d m => NegSobolev.eval F (Torus.realMode k)) := by
  have : (fun F : NegSobolev d m => NegSobolev.eval F (Torus.realMode k)) =
      fun F => Lattice.jp k.1 ^ m * NegSobolev.coord F k := by
    funext F
    rw [q38b_eval_realMode]
    rfl
  rw [this]
  exact (continuous_const.mul (q38b_continuous_coord k)).measurable

/-! ### Two-dimensional Gaussian moments -/

theorem q38b_posSemidef_two (A rate : ℝ) (hA : 0 ≤ A) (hr : 0 ≤ rate) (τ : Fin 2 → ℝ) :
    (Matrix.of fun a b : Fin 2 => A * Real.exp (-rate * |τ a - τ b|)).PosSemidef := by
  have hc0 : 0 < Real.exp (-rate * |τ 0 - τ 1|) := Real.exp_pos _
  have hc1 : Real.exp (-rate * |τ 0 - τ 1|) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [abs_nonneg (τ 0 - τ 1)]
  have hsym : Real.exp (-rate * |τ 1 - τ 0|) = Real.exp (-rate * |τ 0 - τ 1|) := by
    rw [abs_sub_comm]
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial, abs_sub_comm]
  · simp only [star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.of_apply, sub_self,
      abs_zero, mul_zero, Real.exp_zero, hsym]
    set c := Real.exp (-rate * |τ 0 - τ 1|)
    have h1 : 0 ≤ A * (|x 0| - |x 1|) ^ 2 := mul_nonneg hA (sq_nonneg _)
    have h2 : 0 ≤ A * ((1 - c) * (|x 0 * x 1|)) :=
      mul_nonneg hA (mul_nonneg (by linarith) (abs_nonneg _))
    have h3 : -|x 0 * x 1| ≤ x 0 * x 1 := neg_abs_le _
    have h4 : 0 ≤ A * (c * (x 0 * x 1 + |x 0 * x 1|)) :=
      mul_nonneg hA (mul_nonneg hc0.le (by linarith))
    have h5 : |x 0 * x 1| = |x 0| * |x 1| := abs_mul _ _
    have h6 : |x 0| ^ 2 = x 0 ^ 2 := sq_abs _
    have h7 : |x 1| ^ 2 = x 1 ^ 2 := sq_abs _
    nlinarith [h1, h2, h4, h5, h6, h7]

/-- A centred Gaussian vector in `ℝ²` has `E[W₀ W₁] = S₀₁`. -/
theorem q38b_gauss_prod {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : Ω → EuclideanSpace ℝ (Fin 2)) (hW : AEMeasurable W P) (S : Matrix (Fin 2) (Fin 2) ℝ)
    (hS : S.PosSemidef) (h : Measure.map W P = multivariateGaussian 0 S) :
    ∫ ω, W ω 0 * W ω 1 ∂P = S 0 1 := by
  have hcont : Continuous fun x : EuclideanSpace ℝ (Fin 2) => x 0 * x 1 := by fun_prop
  have hint : ∫ ω, W ω 0 * W ω 1 ∂P =
      ∫ x, x 0 * x 1 ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) S) := by
    rw [← h, integral_map hW hcont.aestronglyMeasurable]
  rw [hint]
  set γ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) S with hγ
  have hmem : ∀ i : Fin 2, MemLp (fun x : EuclideanSpace ℝ (Fin 2) => x i) 2 γ := by
    intro i
    have := (IsGaussian.memLp_two_id (μ := γ))
    exact (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).comp_memLp' this
  have hmean : ∀ i : Fin 2, ∫ x, x i ∂γ = 0 := by
    intro i
    have h := (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).integral_comp_id_comm
      (μ := γ) IsGaussian.integrable_id
    simpa [hγ, integral_id_multivariateGaussian] using h
  have hcov := covariance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin 2))) hS 0 1
  rw [covariance_eq_sub (hmem 0) (hmem 1), hmean 0, hmean 1] at hcov
  simpa using hcov

end HRS
