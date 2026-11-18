import Mathlib

/-!
# Lemma 7.5: Gaussian moments for the chaos packet (prefix `q08c_ch_`)

Fourth moment of one-dimensional Gaussians (via the mgf), law of linear functionals of a
multivariate Gaussian and the pair formula `E[X²Y²] = E X² E Y² + 2 (E XY)²`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal RealInnerProductSpace

noncomputable section
namespace HRS.Q08


theorem q08c_ch_gauss_moment (v : ℝ≥0) (k : ℕ) :
    ∫ x, x ^ k ∂(gaussianReal 0 v) = iteratedDeriv k (fun t : ℝ => Real.exp ((v : ℝ) * t ^ 2 / 2)) 0 := by
  have h := iteratedDeriv_mgf_zero (X := id) (μ := gaussianReal 0 v)
    (by rw [integrableExpSet_id_gaussianReal]; simp) k
  have hm : mgf id (gaussianReal 0 v) = fun t : ℝ => Real.exp ((v : ℝ) * t ^ 2 / 2) := by
    rw [mgf_id_gaussianReal]; ext t; simp
  rw [hm] at h
  rw [h]; rfl

theorem q08c_ch_gauss_two (v : ℝ≥0) : ∫ x, x ^ 2 ∂(gaussianReal 0 v) = v := by
  rw [q08c_ch_gauss_moment]
  have h1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Real.exp ((v : ℝ) * t ^ 2 / 2))
      ((v : ℝ) * t * Real.exp ((v : ℝ) * t ^ 2 / 2)) t := by
    intro t
    have := ((hasDerivAt_pow 2 t).const_mul (v : ℝ)).div_const 2 |>.exp
    exact this.congr_deriv (by ring)
  have h2 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (v : ℝ) * t * Real.exp ((v : ℝ) * t ^ 2 / 2))
      (((v : ℝ) + (v : ℝ) ^ 2 * t ^ 2) * Real.exp ((v : ℝ) * t ^ 2 / 2)) t := by
    intro t
    have := ((hasDerivAt_id t).const_mul (v : ℝ)).mul (h1 t)
    exact this.congr_deriv (by simp only [id]; ring)
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  have e1 : deriv (fun t : ℝ => Real.exp ((v : ℝ) * t ^ 2 / 2)) = fun t => (v : ℝ) * t * Real.exp ((v : ℝ) * t ^ 2 / 2) := by
    ext t; exact (h1 t).deriv
  rw [e1, (h2 0).deriv]; simp

theorem q08c_ch_gauss_four (v : ℝ≥0) : ∫ x, x ^ 4 ∂(gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  rw [q08c_ch_gauss_moment]
  have h1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Real.exp ((v : ℝ) * t ^ 2 / 2))
      ((v : ℝ) * t * Real.exp ((v : ℝ) * t ^ 2 / 2)) t := by
    intro t
    have := ((hasDerivAt_pow 2 t).const_mul (v : ℝ)).div_const 2 |>.exp
    exact this.congr_deriv (by ring)
  have h2 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (v : ℝ) * t * Real.exp ((v : ℝ) * t ^ 2 / 2))
      (((v : ℝ) + (v : ℝ) ^ 2 * t ^ 2) * Real.exp ((v : ℝ) * t ^ 2 / 2)) t := by
    intro t
    have := ((hasDerivAt_id t).const_mul (v : ℝ)).mul (h1 t)
    exact this.congr_deriv (by simp only [id]; ring)
  have h3 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => ((v : ℝ) + (v : ℝ) ^ 2 * t ^ 2) * Real.exp ((v : ℝ) * t ^ 2 / 2))
      ((3 * (v : ℝ) ^ 2 * t + (v : ℝ) ^ 3 * t ^ 3) * Real.exp ((v : ℝ) * t ^ 2 / 2)) t := by
    intro t
    have := (((hasDerivAt_pow 2 t).const_mul ((v : ℝ) ^ 2)).const_add (v : ℝ)).mul (h1 t)
    exact this.congr_deriv (by ring)
  have h4 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (3 * (v : ℝ) ^ 2 * t + (v : ℝ) ^ 3 * t ^ 3) * Real.exp ((v : ℝ) * t ^ 2 / 2))
      ((3 * (v : ℝ) ^ 2 + 6 * (v : ℝ) ^ 3 * t ^ 2 + (v : ℝ) ^ 4 * t ^ 4) * Real.exp ((v : ℝ) * t ^ 2 / 2)) t := by
    intro t
    have := (((hasDerivAt_id t).const_mul (3 * (v : ℝ) ^ 2)).add ((hasDerivAt_pow 3 t).const_mul ((v : ℝ) ^ 3))).mul (h1 t)
    exact this.congr_deriv (by simp only [id, Pi.add_apply]; ring)
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  have e1 : deriv (fun t : ℝ => Real.exp ((v : ℝ) * t ^ 2 / 2)) = fun t => (v : ℝ) * t * Real.exp ((v : ℝ) * t ^ 2 / 2) := by
    ext t; exact (h1 t).deriv
  have e2 : deriv (fun t : ℝ => (v : ℝ) * t * Real.exp ((v : ℝ) * t ^ 2 / 2)) = fun t => ((v : ℝ) + (v : ℝ) ^ 2 * t ^ 2) * Real.exp ((v : ℝ) * t ^ 2 / 2) := by
    ext t; exact (h2 t).deriv
  have e3 : deriv (fun t : ℝ => ((v : ℝ) + (v : ℝ) ^ 2 * t ^ 2) * Real.exp ((v : ℝ) * t ^ 2 / 2)) = fun t => (3 * (v : ℝ) ^ 2 * t + (v : ℝ) ^ 3 * t ^ 3) * Real.exp ((v : ℝ) * t ^ 2 / 2) := by
    ext t; exact (h3 t).deriv
  rw [e1, e2, e3, (h4 0).deriv]; simp


variable {n : ℕ}

def q08c_ch_lin (w : Fin n → ℝ) (z : EuclideanSpace ℝ (Fin n)) : ℝ := ∑ i, w i * z i

def q08c_ch_q (C : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) : ℝ := ∑ i, ∑ j, w i * w j * C i j

theorem q08c_ch_lin_eq (w : Fin n → ℝ) :
    q08c_ch_lin w = fun z => ⟪WithLp.toLp 2 w, z⟫ := by
  ext z; simp [q08c_ch_lin, PiLp.inner_apply, mul_comm]

theorem q08c_ch_q_eq (C : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) :
    q08c_ch_q C w = w ⬝ᵥ C *ᵥ w := by
  simp only [q08c_ch_q, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem q08c_ch_lin_law {C : Matrix (Fin n) (Fin n) ℝ} (hS : C.PosSemidef) (w : Fin n → ℝ) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) C).map (q08c_ch_lin w) =
      gaussianReal 0 (q08c_ch_q C w).toNNReal := by
  set μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) C with hμ
  have hL : q08c_ch_lin w = ⇑(innerSL ℝ (WithLp.toLp 2 w)) := by
    rw [q08c_ch_lin_eq]; ext z; simp
  rw [hL, IsGaussian.map_eq_gaussianReal]
  have h0 : μ[innerSL ℝ (WithLp.toLp 2 w)] = 0 := by
    have := ContinuousLinearMap.integral_comp_id_comm (μ := μ) IsGaussian.integrable_id (innerSL ℝ (WithLp.toLp 2 w))
    simp only at this
    rw [this, hμ, integral_id_multivariateGaussian]; simp
  have hv : Var[innerSL ℝ (WithLp.toLp 2 w); μ] = q08c_ch_q C w := by
    have := covarianceBilin_self (μ := μ) IsGaussian.memLp_two_id (WithLp.toLp 2 w)
    rw [covarianceBilin_multivariateGaussian hS] at this
    rw [q08c_ch_q_eq]
    have e : (fun u : EuclideanSpace ℝ (Fin n) => ⟪WithLp.toLp 2 w, u⟫) = ⇑(innerSL ℝ (WithLp.toLp 2 w)) := by
      ext z; simp
    rw [e] at this
    rw [← this]
  rw [h0, hv]


theorem q08c_ch_lin_add (u v : Fin n → ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    q08c_ch_lin (u + v) z = q08c_ch_lin u z + q08c_ch_lin v z := by
  simp [q08c_ch_lin, add_mul, Finset.sum_add_distrib]

theorem q08c_ch_lin_sub (u v : Fin n → ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    q08c_ch_lin (u - v) z = q08c_ch_lin u z - q08c_ch_lin v z := by
  simp [q08c_ch_lin, sub_mul, Finset.sum_sub_distrib]

theorem q08c_ch_lin_meas (w : Fin n → ℝ) : Measurable (q08c_ch_lin w) := by
  unfold q08c_ch_lin; fun_prop

theorem q08c_ch_gauss_int (v : ℝ≥0) (k : ℕ) : Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 v) := by
  by_cases hk : k = 0
  · subst hk; simp
  have h := (memLp_id_gaussianReal (μ := 0) (v := v) k).integrable_norm_pow hk
  refine h.mono' ((measurable_id.pow_const k).aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
  simp [norm_pow]

theorem q08c_ch_lin_int {C : Matrix (Fin n) (Fin n) ℝ} (hS : C.PosSemidef) (w : Fin n → ℝ) (k : ℕ) :
    Integrable (fun z => q08c_ch_lin w z ^ k) (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) C) := by
  have h := q08c_ch_gauss_int (q08c_ch_q C w).toNNReal k
  rw [← q08c_ch_lin_law hS w] at h
  exact (integrable_map_measure (by exact (measurable_id.pow_const k).aestronglyMeasurable)
    (q08c_ch_lin_meas w).aemeasurable).1 h

theorem q08c_ch_lin_nonneg {C : Matrix (Fin n) (Fin n) ℝ} (hS : C.PosSemidef) (w : Fin n → ℝ) :
    0 ≤ q08c_ch_q C w := by
  rw [q08c_ch_q_eq]
  have := (Matrix.posSemidef_iff_dotProduct_mulVec.1 hS).2 w
  simpa using this

theorem q08c_ch_lin_int_pow {C : Matrix (Fin n) (Fin n) ℝ} (hS : C.PosSemidef) (w : Fin n → ℝ) (k : ℕ) :
    ∫ z, q08c_ch_lin w z ^ k ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) C) =
      ∫ x, x ^ k ∂(gaussianReal 0 (q08c_ch_q C w).toNNReal) := by
  rw [← q08c_ch_lin_law hS w]
  exact (integral_map (q08c_ch_lin_meas w).aemeasurable
    (measurable_id.pow_const k).aestronglyMeasurable).symm

theorem q08c_ch_second {C : Matrix (Fin n) (Fin n) ℝ} (hS : C.PosSemidef) (w : Fin n → ℝ) :
    ∫ z, q08c_ch_lin w z ^ 2 ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) C) =
      q08c_ch_q C w := by
  rw [q08c_ch_lin_int_pow hS, q08c_ch_gauss_two, Real.coe_toNNReal _ (q08c_ch_lin_nonneg hS w)]

theorem q08c_ch_fourth {C : Matrix (Fin n) (Fin n) ℝ} (hS : C.PosSemidef) (w : Fin n → ℝ) :
    ∫ z, q08c_ch_lin w z ^ 4 ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) C) =
      3 * q08c_ch_q C w ^ 2 := by
  rw [q08c_ch_lin_int_pow hS, q08c_ch_gauss_four, Real.coe_toNNReal _ (q08c_ch_lin_nonneg hS w)]

theorem q08c_ch_q_add {C : Matrix (Fin n) (Fin n) ℝ} (hS : C.PosSemidef) (u v : Fin n → ℝ) :
    q08c_ch_q C (u + v) = q08c_ch_q C u + q08c_ch_q C v + 2 * ∑ i, ∑ j, u i * v j * C i j := by
  have hsym : ∀ i j, C i j = C j i := fun i j => by
    have := hS.isHermitian.apply j i
    simpa using this
  have e : ∑ i, ∑ j, v i * u j * C i j = ∑ i, ∑ j, u i * v j * C i j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsym j i]; ring
  simp only [q08c_ch_q, Pi.add_apply]
  have : ∀ i j, (u i + v i) * (u j + v j) * C i j =
      u i * u j * C i j + v i * v j * C i j + u i * v j * C i j + v i * u j * C i j := fun i j => by ring
  simp only [this, Finset.sum_add_distrib]
  rw [e]; ring

theorem q08c_ch_q_sub {C : Matrix (Fin n) (Fin n) ℝ} (hS : C.PosSemidef) (u v : Fin n → ℝ) :
    q08c_ch_q C (u - v) = q08c_ch_q C u + q08c_ch_q C v - 2 * ∑ i, ∑ j, u i * v j * C i j := by
  have h := q08c_ch_q_add hS u (-v)
  have e1 : q08c_ch_q C (-v) = q08c_ch_q C v := by simp [q08c_ch_q]
  have e2 : ∑ i, ∑ j, u i * (-v) j * C i j = - ∑ i, ∑ j, u i * v j * C i j := by
    simp [← Finset.sum_neg_distrib]
  rw [e1, e2] at h
  rw [sub_eq_add_neg, h]; ring

theorem q08c_ch_pair {C : Matrix (Fin n) (Fin n) ℝ} (hS : C.PosSemidef) (u v : Fin n → ℝ) :
    ∫ z, q08c_ch_lin u z ^ 2 * q08c_ch_lin v z ^ 2 ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) C) =
      q08c_ch_q C u * q08c_ch_q C v + 2 * (∑ i, ∑ j, u i * v j * C i j) ^ 2 := by
  set μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) C
  set b := ∑ i, ∑ j, u i * v j * C i j with hb
  have i1 := q08c_ch_lin_int hS (u + v) 4
  have i2 := q08c_ch_lin_int hS (u - v) 4
  have i3 := q08c_ch_lin_int hS u 4
  have i4 := q08c_ch_lin_int hS v 4
  have key : ∀ z, 12 * (q08c_ch_lin u z ^ 2 * q08c_ch_lin v z ^ 2) =
      q08c_ch_lin (u + v) z ^ 4 + q08c_ch_lin (u - v) z ^ 4 - 2 * q08c_ch_lin u z ^ 4
        - 2 * q08c_ch_lin v z ^ 4 := by
    intro z; rw [q08c_ch_lin_add, q08c_ch_lin_sub]; ring
  have hint : ∫ z, 12 * (q08c_ch_lin u z ^ 2 * q08c_ch_lin v z ^ 2) ∂μ =
      3 * q08c_ch_q C (u + v) ^ 2 + 3 * q08c_ch_q C (u - v) ^ 2 - 2 * (3 * q08c_ch_q C u ^ 2)
        - 2 * (3 * q08c_ch_q C v ^ 2) := by
    simp_rw [key]
    have h12 : Integrable (fun z => q08c_ch_lin (u + v) z ^ 4 + q08c_ch_lin (u - v) z ^ 4) μ := i1.add i2
    have h123 : Integrable (fun z => q08c_ch_lin (u + v) z ^ 4 + q08c_ch_lin (u - v) z ^ 4
        - 2 * q08c_ch_lin u z ^ 4) μ := h12.sub (i3.const_mul 2)
    rw [integral_sub h123 (i4.const_mul 2),
      integral_sub h12 (i3.const_mul 2), integral_add i1 i2, integral_const_mul,
      integral_const_mul, q08c_ch_fourth hS, q08c_ch_fourth hS, q08c_ch_fourth hS, q08c_ch_fourth hS]
  rw [integral_const_mul, q08c_ch_q_add hS, q08c_ch_q_sub hS] at hint
  linarith


theorem q08c_ch_pair_int {C : Matrix (Fin n) (Fin n) ℝ} (hS : C.PosSemidef) (u v : Fin n → ℝ) :
    Integrable (fun z => q08c_ch_lin u z ^ 2 * q08c_ch_lin v z ^ 2)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) C) := by
  have i1 := q08c_ch_lin_int hS (u + v) 4
  have i2 := q08c_ch_lin_int hS (u - v) 4
  have i3 := q08c_ch_lin_int hS u 4
  have i4 := q08c_ch_lin_int hS v 4
  have h := ((((i1.add i2).sub (i3.const_mul 2)).sub (i4.const_mul 2)).const_mul (1 / 12))
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.add_apply, Pi.sub_apply, q08c_ch_lin_add, q08c_ch_lin_sub]
  ring

end HRS.Q08
