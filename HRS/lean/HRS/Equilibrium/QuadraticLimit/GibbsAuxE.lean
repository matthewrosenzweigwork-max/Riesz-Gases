import HRS.Equilibrium.QuadraticLimit.Features
import HRS.Equilibrium.QuadraticLimit.Chaos
import HRS.Equilibrium.QuadraticLimit.GibbsAuxA

/-!
# Lemma 7.5, `q08_gibbs_approx`: Gaussian side (prefix `q08gl_`)

Dimension-free exponential moments of the Wick-centred quadratic weight under the standard Gaussian
(via `det (1 + t A) ≥ exp (t tr A - t² ‖A‖²_F)` for positive semidefinite `A`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal NNReal BigOperators MatrixOrder

noncomputable section

namespace HRS.Q08

section Det

variable {m : ℕ}

theorem q08gl_det_one_add (A : Matrix (Fin m) (Fin m) ℝ) (hH : A.IsHermitian) (t : ℝ) :
    (1 + t • A).det = ∏ i, (1 + t * hH.eigenvalues i) := by
  set U : Matrix (Fin m) (Fin m) ℝ := (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ) with hU
  have hUU : U * star U = 1 := by
    have := (hH.eigenvectorUnitary).2.2
    simpa [hU] using this
  set D : Matrix (Fin m) (Fin m) ℝ := diagonal hH.eigenvalues with hD
  have hs : A = U * D * star U := by
    have := hH.spectral_theorem
    simpa [hU, hD] using this
  have h1 : 1 + t • A = U * (1 + t • D) * star U := by
    rw [mul_add, add_mul, mul_one, hUU, mul_smul_comm, smul_mul_assoc, ← hs]
  rw [h1, det_mul, det_mul, mul_comm (det U) _, mul_assoc, ← det_mul, hUU, det_one, mul_one]
  rw [show (1 : Matrix (Fin m) (Fin m) ℝ) + t • D = diagonal (fun i => 1 + t * hH.eigenvalues i) by
    rw [hD]; ext i j; by_cases h : i = j <;> simp [h]]
  rw [det_diagonal]

theorem q08gl_sum_sq (A : Matrix (Fin m) (Fin m) ℝ) (hH : A.IsHermitian) :
    ∑ i, ∑ j, A i j ^ 2 = ∑ i, hH.eigenvalues i ^ 2 := by
  set U : Matrix (Fin m) (Fin m) ℝ := (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ) with hU
  have hUU : star U * U = 1 := by
    have := (hH.eigenvectorUnitary).2.1
    simpa [hU] using this
  set D : Matrix (Fin m) (Fin m) ℝ := diagonal hH.eigenvalues with hD
  have hs : A = U * D * star U := by
    have := hH.spectral_theorem
    simpa [hU, hD] using this
  have h1 : ∑ i, ∑ j, A i j ^ 2 = (A * A).trace := by
    unfold Matrix.trace
    simp only [Matrix.diag_apply, Matrix.mul_apply, sq]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have := hH.apply j i
    simp at this
    rw [this]
  have h2 : A * A = U * (D * D) * star U := by
    rw [hs]
    calc U * D * star U * (U * D * star U) = U * D * (star U * U) * D * star U := by simp only [mul_assoc]
      _ = _ := by rw [hUU]; simp [mul_assoc]
  rw [h1, h2, Matrix.trace_mul_comm, ← mul_assoc, hUU, one_mul, hD, diagonal_mul_diagonal]
  simp [Matrix.trace, sq]

theorem q08gl_exp_le_one_add (x : ℝ) (hx : 0 ≤ x) : Real.exp (x - x ^ 2) ≤ 1 + x := by
  have h1 : 1 - (1 + x)⁻¹ ≤ Real.log (1 + x) := Real.one_sub_inv_le_log_of_pos (by linarith)
  have h2 : x - x ^ 2 ≤ 1 - (1 + x)⁻¹ := by
    have : 1 - (1 + x)⁻¹ = x / (1 + x) := by field_simp; ring
    rw [this, le_div_iff₀ (by linarith)]
    nlinarith [pow_nonneg hx 3]
  calc Real.exp (x - x ^ 2) ≤ Real.exp (Real.log (1 + x)) := Real.exp_le_exp.2 (h2.trans h1)
    _ = 1 + x := Real.exp_log (by linarith)

theorem q08gl_det_lower (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosSemidef) (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (t * A.trace - t ^ 2 * ∑ i, ∑ j, A i j ^ 2) ≤ (1 + t • A).det := by
  have hH : A.IsHermitian := hA.isHermitian
  rw [q08gl_det_one_add A hH t, q08gl_sum_sq A hH]
  have htr : A.trace = ∑ i, hH.eigenvalues i := by
    have := hH.trace_eq_sum_eigenvalues
    simpa using this
  rw [htr, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Real.exp_sum]
  refine Finset.prod_le_prod₀ (fun i _ => (Real.exp_pos _).le) fun i _ => ?_
  have h0 : 0 ≤ t * hH.eigenvalues i := mul_nonneg ht (hA.eigenvalues_nonneg i)
  have := q08gl_exp_le_one_add (t * hH.eigenvalues i) h0
  convert this using 2
  ring

end Det

section GaussBound

variable {m : ℕ}

theorem q08gl_gauss_quad_le (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosSemidef) (t : ℝ) (ht : 0 ≤ t) :
    ∫ s, Real.exp (-(t / 2) * ∑ i, ∑ j, A i j * s i * s j)
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (1 : Matrix (Fin m) (Fin m) ℝ)) ≤
      Real.exp (-(t * A.trace - t ^ 2 * ∑ i, ∑ j, A i j ^ 2) / 2) := by
  have hdet := q08gl_det_lower A hA t ht
  have hdpos : 0 < (1 + t • A).det := lt_of_lt_of_le (Real.exp_pos _) hdet
  set M : Matrix (Fin m) (Fin m) ℝ := (1 + t • A)⁻¹ with hMdef
  have hM : M * (1 + t • A) = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdpos.ne')
  have hMp := q08g_M_psd A M hA t ht hM
  have htilt := q08g_tilt_aux A M hA t ht hM (fun _ => 1) measurable_const
  simp only [one_mul, integral_const, probReal_univ, smul_eq_mul, mul_one] at htilt
  rw [htilt]
  set R := CFC.sqrt M with hR
  have hRR : R * R = M := CFC.sqrt_mul_sqrt_self M hMp.nonneg
  have h1 : R.det ^ 2 = M.det := by rw [sq, ← det_mul, hRR]
  have h2 : M.det * (1 + t • A).det = 1 := by rw [← det_mul, hM, det_one]
  have h3 : M.det ≤ Real.exp (-(t * A.trace - t ^ 2 * ∑ i, ∑ j, A i j ^ 2)) := by
    have : M.det = ((1 + t • A).det)⁻¹ := by
      field_simp; linarith
    rw [this, Real.exp_neg]
    exact inv_anti₀ (Real.exp_pos _) hdet
  have h4 : |R.det| ^ 2 ≤ (Real.exp (-(t * A.trace - t ^ 2 * ∑ i, ∑ j, A i j ^ 2) / 2)) ^ 2 := by
    rw [sq_abs, h1, ← Real.exp_nat_mul]
    refine h3.trans (le_of_eq ?_)
    congr 1; push_cast; ring
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (Real.exp_pos _).le two_ne_zero).1 h4

end GaussBound

section FiniteRankObjects

variable {m : ℕ}

/-- The quadratic form `s ↦ ∑ A_ij s_i s_j`. -/
def q08gl_Q (A : Matrix (Fin m) (Fin m) ℝ) (s : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∑ i, ∑ j, A i j * s i * s j

/-- The exponent of the finite-rank weight: `½ (sᵀ A s - tr A) - ½ ḡ`. -/
def q08gl_psi (A : Matrix (Fin m) (Fin m) ℝ) (g : ℝ) (s : EuclideanSpace ℝ (Fin m)) : ℝ :=
  (1 / 2) * (q08gl_Q A s - A.trace) - (1 / 2) * g

/-- The Wick quadratic statistic `½ (sᵀ H s - tr H)`. -/
def q08gl_fq (H : Matrix (Fin m) (Fin m) ℝ) (s : EuclideanSpace ℝ (Fin m)) : ℝ :=
  (1 / 2) * (q08gl_Q H s - H.trace)

/-- The linear statistic `∑ α_k s_k`. -/
def q08gl_fl (α : Fin m → ℝ) (s : EuclideanSpace ℝ (Fin m)) : ℝ := ∑ k, α k * s k

theorem q08gl_Q_cont (A : Matrix (Fin m) (Fin m) ℝ) : Continuous (q08gl_Q A) := by
  unfold q08gl_Q; fun_prop

theorem q08gl_Q_nonneg (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosSemidef) (s : EuclideanSpace ℝ (Fin m)) :
    0 ≤ q08gl_Q A s := by
  have h := hA.dotProduct_mulVec_nonneg (fun i => s i)
  have e : q08gl_Q A s = star (fun i => s i) ⬝ᵥ A.mulVec (fun i => s i) := by
    simp only [q08gl_Q, dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]; exact h

theorem q08gl_psi_cont (A : Matrix (Fin m) (Fin m) ℝ) (g : ℝ) : Continuous (q08gl_psi A g) := by
  unfold q08gl_psi
  exact (continuous_const.mul ((q08gl_Q_cont A).sub continuous_const)).sub continuous_const

theorem q08gl_fq_cont (H : Matrix (Fin m) (Fin m) ℝ) : Continuous (q08gl_fq H) := by
  unfold q08gl_fq
  exact continuous_const.mul ((q08gl_Q_cont H).sub continuous_const)

theorem q08gl_fl_cont (α : Fin m → ℝ) : Continuous (q08gl_fl α) := by
  unfold q08gl_fl; fun_prop

/-- The finite-rank weight is bounded. -/
theorem q08gl_b_bound (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosSemidef) (β g : ℝ) (hβ : 0 ≤ β)
    (s : EuclideanSpace ℝ (Fin m)) :
    Real.exp (-β * q08gl_psi A g s) ≤ Real.exp (β * (A.trace + g) / 2) := by
  refine Real.exp_le_exp.2 ?_
  have := q08gl_Q_nonneg A hA s
  unfold q08gl_psi
  nlinarith

theorem q08gl_b_pow (A : Matrix (Fin m) (Fin m) ℝ) (β g : ℝ) (q : ℕ) (s : EuclideanSpace ℝ (Fin m)) :
    Real.exp (-β * q08gl_psi A g s) ^ q =
      Real.exp (q * β * (A.trace + g) / 2) * Real.exp (-(q * β / 2) * q08gl_Q A s) := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  unfold q08gl_psi
  ring

/-- Dimension-free `L^q` bound of the finite-rank weight under the standard Gaussian. -/
theorem q08gl_b_int_le (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosSemidef) (β g F2 : ℝ) (hβ : 0 ≤ β)
    (hF2 : ∑ i, ∑ j, A i j ^ 2 ≤ F2) (q : ℕ) :
    ∫ s, Real.exp (-β * q08gl_psi A g s) ^ q
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (1 : Matrix (Fin m) (Fin m) ℝ)) ≤
      Real.exp (q * β * g / 2 + (q * β) ^ 2 * F2 / 2) := by
  simp_rw [q08gl_b_pow]
  rw [integral_const_mul]
  have h := q08gl_gauss_quad_le A hA (q * β) (by positivity)
  have h2 : Real.exp (q * β * (A.trace + g) / 2) *
      ∫ s, Real.exp (-(q * β / 2) * q08gl_Q A s)
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (1 : Matrix (Fin m) (Fin m) ℝ)) ≤
      Real.exp (q * β * (A.trace + g) / 2) *
        Real.exp (-(q * β * A.trace - (q * β) ^ 2 * ∑ i, ∑ j, A i j ^ 2) / 2) :=
    mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
  refine h2.trans ?_
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have : (q * β) ^ 2 * ∑ i, ∑ j, A i j ^ 2 ≤ (q * β) ^ 2 * F2 :=
    mul_le_mul_of_nonneg_left hF2 (sq_nonneg _)
  nlinarith

end FiniteRankObjects

section Moments

variable {m : ℕ}

/-- The standard Gaussian on `ℝ^m`. -/
abbrev q08gl_gam (m : ℕ) : Measure (EuclideanSpace ℝ (Fin m)) :=
  multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (1 : Matrix (Fin m) (Fin m) ℝ)

theorem q08gl_gauss_coord_memLp (S : Matrix (Fin m) (Fin m) ℝ) (i : Fin m) :
    MemLp (fun s : EuclideanSpace ℝ (Fin m) => s i) 2
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S) := by
  have := IsGaussian.memLp_dual (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S)
    (EuclideanSpace.proj i : StrongDual ℝ (EuclideanSpace ℝ (Fin m))) 2 (by norm_num)
  simpa using this

theorem q08gl_gauss_coord_memLp4 (S : Matrix (Fin m) (Fin m) ℝ) (i : Fin m) :
    MemLp (fun s : EuclideanSpace ℝ (Fin m) => s i) 4
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S) := by
  have := IsGaussian.memLp_dual (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S)
    (EuclideanSpace.proj i : StrongDual ℝ (EuclideanSpace ℝ (Fin m))) 4 (by norm_num)
  simpa using this

theorem q08gl_gauss_mean (S : Matrix (Fin m) (Fin m) ℝ) (i : Fin m) :
    ∫ s : EuclideanSpace ℝ (Fin m), s i ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S) = 0 := by
  have h := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
    (IsGaussian.integrable_id (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S))
  simp at h
  simpa using h

theorem q08gl_gauss_moment (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.PosSemidef) (i j : Fin m) :
    ∫ s : EuclideanSpace ℝ (Fin m), s i * s j
      ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S) = S i j := by
  have h := covariance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin m))) hS i j
  rw [covariance_eq_sub (q08gl_gauss_coord_memLp S i) (q08gl_gauss_coord_memLp S j),
    q08gl_gauss_mean S i, zero_mul, sub_zero] at h
  simpa using h

theorem q08gl_gauss_prod_memLp (S : Matrix (Fin m) (Fin m) ℝ) (i j : Fin m) :
    MemLp (fun s : EuclideanSpace ℝ (Fin m) => s i * s j) 2
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S) := by
  have := MemLp.mul (r := 2) (q08gl_gauss_coord_memLp4 S i) (q08gl_gauss_coord_memLp4 S j)
  exact this

theorem q08gl_Q_memLp (S A : Matrix (Fin m) (Fin m) ℝ) :
    MemLp (q08gl_Q A) 2 (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S) := by
  unfold q08gl_Q
  refine memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ => ?_
  have := (q08gl_gauss_prod_memLp S i j).const_mul (A i j)
  simpa [mul_assoc] using this

theorem q08gl_fq_memLp (S H : Matrix (Fin m) (Fin m) ℝ) :
    MemLp (q08gl_fq H) 2 (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S) := by
  unfold q08gl_fq
  exact ((q08gl_Q_memLp S H).sub (memLp_const _)).const_mul _

theorem q08gl_fl_memLp (S : Matrix (Fin m) (Fin m) ℝ) (α : Fin m → ℝ) :
    MemLp (q08gl_fl α) 2 (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S) := by
  unfold q08gl_fl
  refine memLp_finsetSum _ fun k _ => ?_
  exact (q08gl_gauss_coord_memLp S k).const_mul (α k)

theorem q08gl_fl_L2 (α : Fin m → ℝ) :
    ∫ s, q08gl_fl α s ^ 2 ∂(q08gl_gam m) = ∑ k, α k ^ 2 := by
  have h1 : ∀ s : EuclideanSpace ℝ (Fin m), q08gl_fl α s ^ 2 = ∑ k, ∑ l, α k * α l * (s k * s l) := by
    intro s
    unfold q08gl_fl
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  simp_rw [h1]
  have hint : ∀ k l : Fin m, Integrable (fun s : EuclideanSpace ℝ (Fin m) => α k * α l * (s k * s l)) (q08gl_gam m) :=
    fun k l => ((q08gl_gauss_prod_memLp 1 k l).integrable one_le_two).const_mul _
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun l _ => hint k l]
  simp_rw [integral_const_mul]
  have : ∀ l, ∫ s : EuclideanSpace ℝ (Fin m), s k * s l ∂(q08gl_gam m) = if k = l then 1 else 0 := by
    intro l
    have := q08gl_gauss_moment (1 : Matrix (Fin m) (Fin m) ℝ) Matrix.PosSemidef.one k l
    simpa [Matrix.one_apply] using this
  simp_rw [this]
  simp [sq]

/-- The `L²` norm of the Wick quadratic statistic under the standard Gaussian (via `q08_chaos_l2_bound`). -/
theorem q08gl_fq_L2 (H : Matrix (Fin m) (Fin m) ℝ) (hH : ∀ i j, H i j = H j i) :
    ∫ s, q08gl_fq H s ^ 2 ∂(q08gl_gam m) ≤ (1 / 2) * ∑ i, ∑ j, H i j ^ 2 := by
  set C : ℕ → ℕ → ℝ := fun i j => if i = j then 1 else 0 with hCdef
  have hsum : ∀ (n : ℕ) (v : ℕ → ℝ), ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * C i j =
      ∑ i ∈ Finset.range n, v i ^ 2 := by
    intro n v
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [hCdef, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq, if_pos hi, sq]
  have hC : q08_IsCov C := ⟨fun i j => by simp [hCdef, eq_comm],
    fun n v => by rw [hsum]; exact Finset.sum_nonneg fun i _ => sq_nonneg _,
    fun n v => le_of_eq (hsum n v)⟩
  obtain ⟨Ω, mΩ, P, hP, G, Q, Lin, hGm, hQm, hLm, hlaw, -, -⟩ := q08_chaos_exists (p := 0) C
    (fun _ _ => 0) (fun b => Fin.elim0 b) hC (fun _ _ => rfl) (by simp [summable_zero])
    (fun b => Fin.elim0 b)
  have hone : (Matrix.of fun i j : Fin m => C i j) = (1 : Matrix (Fin m) (Fin m) ℝ) := by
    ext i j
    simp [hCdef, Matrix.one_apply, Fin.val_inj]
  have hlC := hlaw m
  have hl := hlC
  rw [hone] at hl
  have hbound := q08_chaos_l2_bound P G hGm C hC m hlC (fun i j => H i j) hH
  set g : Ω → EuclideanSpace ℝ (Fin m) := fun ω => (WithLp.toLp 2 fun i : Fin m => G i ω) with hg
  have hgm : Measurable g := by
    refine (WithLp.measurable_toLp 2 (Fin m → ℝ)).comp (measurable_pi_iff.2 fun i => hGm i)
  have hγ : q08gl_gam m = P.map g := by
    have : q08gl_gam m = law P g := hl.symm
    exact this
  rw [hγ, integral_map (f := fun s => q08gl_fq H s ^ 2) hgm.aemeasurable
    (((q08gl_fq_cont H).pow 2).aestronglyMeasurable)]
  refine le_trans (le_of_eq ?_) hbound
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [hg, q08gl_fq, q08gl_Q, hCdef]
  congr 2
  have e1 : ∑ i : Fin m, ∑ j : Fin m, H i j * (G i ω * G j ω - (if (i : ℕ) = (j : ℕ) then 1 else 0)) =
      ∑ i : Fin m, ∑ j : Fin m, H i j * (G i ω * G j ω) - H.trace := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    congr 1
    simp only [Matrix.trace, Matrix.diag_apply, mul_ite, mul_one, mul_zero, Fin.val_inj]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  rw [e1]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [mul_assoc]

end Moments

section Ident

variable {m p : ℕ}

/-- Transport of a test function on `ℝ × (Fin p → ℝ)` to `Option (Fin p) → ℝ`. -/
def q08gl_Ft (F : ℝ × (Fin p → ℝ) → ℝ) (v : Option (Fin p) → ℝ) : ℝ := F (v none, fun b => v (some b))

/-- The finite-rank statistics (quadratic Wick one first, then the linear ones). -/
def q08gl_fvec (H : Matrix (Fin m) (Fin m) ℝ) (α : Fin p → Fin m → ℝ) (o : Option (Fin p))
    (s : EuclideanSpace ℝ (Fin m)) : ℝ :=
  Option.elim o (q08gl_fq H s) (fun b => q08gl_fl (α b) s)

theorem q08gl_Ft_cont (F : ℝ × (Fin p → ℝ) → ℝ) (hF : Continuous F) : Continuous (q08gl_Ft F) := by
  unfold q08gl_Ft
  refine hF.comp (Continuous.prodMk (continuous_apply none) (continuous_pi fun b => continuous_apply (some b)))

theorem q08gl_fvec_cont (H : Matrix (Fin m) (Fin m) ℝ) (α : Fin p → Fin m → ℝ) (o : Option (Fin p)) :
    Continuous (q08gl_fvec H α o) := by
  cases o
  · exact q08gl_fq_cont H
  · exact q08gl_fl_cont _

/-- Identification of the tilted Gaussian functional with the Wick-centred integral against `N(0, M)`. -/
theorem q08gl_tilt_ident (A H M : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosSemidef) (β g : ℝ) (hβ : 0 ≤ β)
    (hM : M * (1 + β • A) = 1) (α : Fin p → Fin m → ℝ) (F : ℝ × (Fin p → ℝ) → ℝ) (hFc : Continuous F)
    (MF : ℝ) (hMF : ∀ z, |F z| ≤ MF) :
    q08gl_Phi (q08gl_gam m) (q08gl_Ft F) (fun s => Real.exp (-β * q08gl_psi A g s)) (q08gl_fvec H α)
        (∫ s, Real.exp (-β * q08gl_psi A g s) ∂(q08gl_gam m)) =
      ∫ s, F ((1 / 2) * ∑ k, ∑ l, H k l * (s k * s l - M k l), fun b => ∑ k, α b k * s k)
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) M) := by
  have hMp := q08g_M_psd A M hA β hβ hM
  obtain ⟨hdet, -, -⟩ := q08g_alg A M hA β hβ hM
  set D : ℝ := |(CFC.sqrt M).det| with hD
  have hDpos : 0 < D := abs_pos.2 hdet
  set C₀ : ℝ := Real.exp (β * (A.trace + g) / 2) with hC₀
  have hC₀pos : 0 < C₀ := Real.exp_pos _
  set ν : Measure (EuclideanSpace ℝ (Fin m)) := multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) M with hν
  have hb : ∀ s : EuclideanSpace ℝ (Fin m), Real.exp (-β * q08gl_psi A g s) =
      C₀ * Real.exp (-(β / 2) * ∑ i, ∑ j, A i j * s i * s j) := by
    intro s
    have := q08gl_b_pow A β g 1 s
    simpa [q08gl_Q, hC₀] using this
  -- the tilt identity for measurable `G`
  have htilt : ∀ G : EuclideanSpace ℝ (Fin m) → ℝ, Measurable G →
      ∫ s, G s * Real.exp (-β * q08gl_psi A g s) ∂(q08gl_gam m) = C₀ * D * ∫ s, G s ∂ν := by
    intro G hG
    have := q08g_tilt_aux A M hA β hβ hM G hG
    calc ∫ s, G s * Real.exp (-β * q08gl_psi A g s) ∂(q08gl_gam m)
        = ∫ s, C₀ * (G s * Real.exp (-(β / 2) * ∑ i, ∑ j, A i j * s i * s j)) ∂(q08gl_gam m) := by
          refine integral_congr_ae (Eventually.of_forall fun s => ?_)
          simp only [hb]; ring
      _ = C₀ * D * ∫ s, G s ∂ν := by
          rw [integral_const_mul, this]; ring
  have hz : ∫ s, Real.exp (-β * q08gl_psi A g s) ∂(q08gl_gam m) = C₀ * D := by
    have := htilt (fun _ => 1) measurable_const
    simpa using this
  rw [hz]
  have hzpos : 0 < C₀ * D := mul_pos hC₀pos hDpos
  -- Gaussian moments under `ν`
  have hint : ∀ k l : Fin m, Integrable (fun s : EuclideanSpace ℝ (Fin m) => s k * s l) ν := fun k l =>
    (q08gl_gauss_prod_memLp M k l).integrable one_le_two
  have hQint : ∫ s, q08gl_Q H s ∂ν = ∑ k, ∑ l, H k l * M k l := by
    unfold q08gl_Q
    have h1 : ∀ k l : Fin m, Integrable (fun s : EuclideanSpace ℝ (Fin m) => H k l * s k * s l) ν := fun k l => by
      simpa [mul_assoc] using (hint k l).const_mul (H k l)
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => h1 k l]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun l _ => h1 k l]
    refine Finset.sum_congr rfl fun l _ => ?_
    have h2 := q08gl_gauss_moment M hMp k l
    calc ∫ s : EuclideanSpace ℝ (Fin m), H k l * s k * s l ∂ν
        = ∫ s : EuclideanSpace ℝ (Fin m), H k l * (s k * s l) ∂ν := by
          refine integral_congr_ae (Eventually.of_forall fun s => ?_); simp only; ring
      _ = H k l * ∫ s : EuclideanSpace ℝ (Fin m), s k * s l ∂ν := integral_const_mul _ _
      _ = H k l * M k l := by rw [h2]
  have hmean : ∀ k : Fin m, ∫ s : EuclideanSpace ℝ (Fin m), s k ∂ν = 0 := fun k => q08gl_gauss_mean M k
  have hflint : ∀ b : Fin p, ∫ s, q08gl_fl (α b) s ∂ν = 0 := by
    intro b
    unfold q08gl_fl
    have h1 : ∀ k : Fin m, Integrable (fun s : EuclideanSpace ℝ (Fin m) => α b k * s k) ν := fun k =>
      ((q08gl_gauss_coord_memLp M k).integrable one_le_two).const_mul _
    rw [integral_finsetSum _ fun k _ => h1 k]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [integral_const_mul, hmean k, mul_zero]
  have hfqint : ∫ s, q08gl_fq H s ∂ν = (1 / 2) * (∑ k, ∑ l, H k l * M k l - H.trace) := by
    unfold q08gl_fq
    rw [integral_const_mul, integral_sub ((q08gl_Q_memLp M H).integrable one_le_two) (integrable_const _),
      hQint]
    simp
  set e : Option (Fin p) → ℝ := fun o => ∫ s, q08gl_fvec H α o s ∂ν with he
  have he_none : e none = (1 / 2) * (∑ k, ∑ l, H k l * M k l - H.trace) := by
    simp only [he, q08gl_fvec, Option.elim]; exact hfqint
  have he_some : ∀ b, e (some b) = 0 := fun b => by
    simp only [he, q08gl_fvec, Option.elim]; exact hflint b
  -- measurability of the statistics
  have hfm : ∀ o, Measurable (q08gl_fvec H α o) := fun o => (q08gl_fvec_cont H α o).measurable
  have hc : ∀ i, (1 / (C₀ * D)) * ∫ s, q08gl_fvec H α i s * Real.exp (-β * q08gl_psi A g s) ∂(q08gl_gam m) = e i := by
    intro i
    rw [htilt _ (hfm i)]
    field_simp
    rfl
  unfold q08gl_Phi
  simp_rw [hc]
  have hGm : Measurable (fun s : EuclideanSpace ℝ (Fin m) => q08gl_Ft F (fun i => q08gl_fvec H α i s - e i)) :=
    (q08gl_Ft_cont F hFc).measurable.comp (measurable_pi_iff.2 fun i => (hfm i).sub_const _)
  rw [htilt _ hGm]
  field_simp
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [q08gl_Ft, q08gl_fvec, Option.elim, he_none, he_some, sub_zero]
  refine congrArg F (Prod.ext ?_ ?_)
  · dsimp only
    unfold q08gl_fq q08gl_Q
    simp only [mul_sub, Finset.sum_sub_distrib]
    have : ∀ k l : Fin m, H k l * (s k * s l) = H k l * s k * s l := fun k l => by ring
    simp_rw [this]
    ring
  · funext b
    rfl

end Ident

end HRS.Q08

end
