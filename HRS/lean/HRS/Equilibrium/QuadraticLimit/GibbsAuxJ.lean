import HRS.Equilibrium.QuadraticLimit.Features
import HRS.Equilibrium.QuadraticLimit.GibbsAuxF
import HRS.Equilibrium.QuadraticLimit.GibbsAuxI
import HRS.Equilibrium.QuadraticLimit.GibbsAuxG

/-!
# Lemma 7.5, `q08_gibbs_approx`: the resolvent estimate for the bounded orthonormal family
(prefix `q08gl_`)

Concrete instantiation of `q08gl_abstract_est` in `L²(μ)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Q08

open ResponseAux InnerProductSpace

variable {d : ℕ} (D : Q08Data d)

instance q08gl_isProb_wd : IsProbabilityMeasure (withDensityReal D.ρ) := q08_isProb_μ D

section Setup

variable {m : ℕ} {u : Fin m → Torus d → ℝ}

theorem q08gl_memLp_u (hu : q08gl_UData D.μ u) (k : Fin m) : MemLp (u k) 2 (withDensityReal D.ρ) := by
  obtain ⟨M, hM⟩ := hu.bdd k
  exact MemLp.of_bound (hu.meas k).aestronglyMeasurable M
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hM x)

/-- `u_k` as an element of `L²(μ)`. -/
def q08gl_ub (hu : q08gl_UData D.μ u) (k : Fin m) : Lp ℝ 2 (withDensityReal D.ρ) :=
  (q08gl_memLp_u D hu k).toLp (u k)

theorem q08gl_ub_coe (hu : q08gl_UData D.μ u) (k : Fin m) :
    (q08gl_ub D hu k : Torus d → ℝ) =ᵐ[withDensityReal D.ρ] u k :=
  (q08gl_memLp_u D hu k).coeFn_toLp

theorem q08gl_inner_ub (hu : q08gl_UData D.μ u) (k l : Fin m) :
    inner ℝ (q08gl_ub D hu k) (q08gl_ub D hu l) = ∫ x, u k x * u l x ∂D.μ :=
  q08s_inner_toLp (withDensityReal D.ρ) (q08gl_memLp_u D hu k) (q08gl_memLp_u D hu l)

theorem q08gl_ub_orthonormal (hu : q08gl_UData D.μ u) : Orthonormal ℝ (q08gl_ub D hu) := by
  rw [orthonormal_iff_ite]
  intro k l
  rw [q08gl_inner_ub, hu.orth]

theorem q08gl_ub_P (hu : q08gl_UData D.μ u) (k : Fin m) :
    projL (oneL D.hρ.density) (q08gl_ub D hu k) = q08gl_ub D hu k := by
  haveI := q08_isProb_μ D
  rw [projL_eq_self_iff (norm_oneL D.hρ.density), inner_oneL, integral_congr_ae (q08gl_ub_coe D hu k)]
  exact hu.cent k

end Setup

section Resolvent

variable {m : ℕ} {u : Fin m → Torus d → ℝ}

/-- The operator `T = I + β P K P` on `L²(μ)`. -/
def q08gl_T : Lp ℝ 2 (withDensityReal D.ρ) →L[ℝ] Lp ℝ 2 (withDensityReal D.ρ) :=
  Top (oneL D.hρ.density) (KL (q08s_setup D)) D.β

theorem q08gl_T_selfadj (x y : Lp ℝ 2 (withDensityReal D.ρ)) :
    inner ℝ (q08gl_T D x) y = inner ℝ x (q08gl_T D y) := by
  have hone : ‖oneL D.hρ.density‖ = 1 := norm_oneL D.hρ.density
  unfold q08gl_T
  rw [Top_apply, Top_apply, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  have h1 : inner ℝ (projL (oneL D.hρ.density) (KL (q08s_setup D) (projL (oneL D.hρ.density) x))) y =
      inner ℝ (KL (q08s_setup D) (projL (oneL D.hρ.density) x)) (projL (oneL D.hρ.density) y) :=
    inner_projL_left _ _ _
  have h2 : inner ℝ x (projL (oneL D.hρ.density) (KL (q08s_setup D) (projL (oneL D.hρ.density) y))) =
      inner ℝ (projL (oneL D.hρ.density) x) (KL (q08s_setup D) (projL (oneL D.hρ.density) y)) :=
    (inner_projL_left _ _ _).symm
  rw [h1, h2, q08s_KL_symm (q08s_setup D) (projL (oneL D.hρ.density) x) (projL (oneL D.hρ.density) y)]
  have : inner ℝ (KL (q08s_setup D) (projL (oneL D.hρ.density) y)) (projL (oneL D.hρ.density) x) =
      inner ℝ (projL (oneL D.hρ.density) x) (KL (q08s_setup D) (projL (oneL D.hρ.density) y)) :=
    real_inner_comm _ _
  rw [this]

theorem q08gl_T_coercive (x : Lp ℝ 2 (withDensityReal D.ρ)) : ‖x‖ * ‖x‖ ≤ inner ℝ (q08gl_T D x) x :=
  Top_coercive (inner_KL_nonneg (q08s_setup D)) D.hβ.le x

theorem q08gl_exists_R : ∃ R : Lp ℝ 2 (withDensityReal D.ρ) →L[ℝ] Lp ℝ 2 (withDensityReal D.ρ),
    (∀ x, q08gl_T D (R x) = x) ∧ (∀ x, R (q08gl_T D x) = x) ∧ (∀ x, ‖R x‖ ≤ ‖x‖) ∧
      (∀ x y, inner ℝ (R x) y = inner ℝ x (R y)) :=
  q08gl_inv_op (q08gl_T D) (q08gl_T_selfadj D) (q08gl_T_coercive D)

/-- The inverse of `T`. -/
def q08gl_R : Lp ℝ 2 (withDensityReal D.ρ) →L[ℝ] Lp ℝ 2 (withDensityReal D.ρ) := (q08gl_exists_R D).choose

theorem q08gl_R_T (x) : q08gl_T D (q08gl_R D x) = x := (q08gl_exists_R D).choose_spec.1 x
theorem q08gl_T_R (x) : q08gl_R D (q08gl_T D x) = x := (q08gl_exists_R D).choose_spec.2.1 x
theorem q08gl_R_contr (x) : ‖q08gl_R D x‖ ≤ ‖x‖ := (q08gl_exists_R D).choose_spec.2.2.1 x
theorem q08gl_R_selfadj (x y) : inner ℝ (q08gl_R D x) y = inner ℝ x (q08gl_R D y) :=
  (q08gl_exists_R D).choose_spec.2.2.2 x y

/-- The responses `U_j = R E_j`. -/
theorem q08gl_U_eq (j : ℕ) : q08s_U D j = q08gl_R D (q08s_E D j) := by
  have A := q08s_abs D
  have hone : ‖oneL D.hρ.density‖ = 1 := norm_oneL D.hρ.density
  have h1 : projL (oneL D.hρ.density) (q08s_U D j) = q08s_U D j := q08s_PU A j
  have h2 : q08gl_T D (q08s_U D j) = q08s_E D j := by
    unfold q08gl_T
    rw [Top_apply, h1]
    exact A.hUeq j
  rw [← h2, q08gl_T_R]

/-- `K^U_{jk} = ∬ g(x - y) u_j(x) u_k(y)`. -/
def q08gl_KUe (u : Fin m → Torus d → ℝ) (j k : Fin m) : ℝ :=
  ∫ x, ∫ y, periodicRiesz d D.s (x - y) * u j x * u k y ∂D.μ ∂D.μ

theorem q08gl_KUe_eq (hu : q08gl_UData D.μ u) (j k : Fin m) :
    inner ℝ (q08gl_ub D hu j) (KL (q08s_setup D) (q08gl_ub D hu k)) = q08gl_KUe D u j k := by
  rw [real_inner_comm, q08s_inner_KL]
  have h1 : Kt (periodicRiesz d D.s) (withDensityReal D.ρ) (q08gl_ub D hu k) =
      Kt (periodicRiesz d D.s) (withDensityReal D.ρ) (u k) := Kt_congr _ (q08gl_ub_coe D hu k)
  rw [h1]
  unfold q08gl_KUe
  have h2 : ∀ x, ∫ y, periodicRiesz d D.s (x - y) * u j x * u k y ∂D.μ =
      Kt (periodicRiesz d D.s) (withDensityReal D.ρ) (u k) x * u j x := by
    intro x
    unfold Kt
    rw [← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    ring
  simp_rw [h2]
  refine integral_congr_ae ?_
  filter_upwards [q08gl_ub_coe D hu j] with x hx
  rw [hx]

end Resolvent

section Kernel

variable {m : ℕ} {u : Fin m → Torus d → ℝ}

/-- The Riesz kernel `g(x - y)`. -/
def q08gl_kg (x y : Torus d) : ℝ := periodicRiesz d D.s (x - y)

theorem q08gl_kg_eq : q08gl_kg D = fun x y => periodicRiesz d D.s (x - y) := rfl

theorem q08gl_kg_meas' : Measurable (Function.uncurry (q08gl_kg D)) := q08gl_kg_meas D

theorem q08gl_kg_symm' (x y : Torus d) : q08gl_kg D x y = q08gl_kg D y x := q08gl_kg_symm D x y

theorem q08gl_kg_sq_int : Integrable (fun z : Torus d × Torus d => q08gl_kg D z.1 z.2 ^ 2) (D.μ.prod D.μ) :=
  q08s_g_sq_int D

theorem q08gl_kg_memLp : MemLp (Function.uncurry (q08gl_kg D)) 2 (D.μ.prod D.μ) := q08s_g_memLp D

theorem q08gl_Kt_eq (f : Torus d → ℝ) (x : Torus d) :
    Kt (periodicRiesz d D.s) (withDensityReal D.ρ) f x = ∫ y, q08gl_kg D x y * f y ∂D.μ := rfl

/-- The row integral is bounded. -/
theorem q08gl_a_bdd : ∃ M : ℝ, ∀ x, |q08e_a D.μ (q08gl_kg D) x| ≤ M := by
  obtain ⟨M, hM⟩ := (q08f_rowOK_g D).bound
  refine ⟨M, fun x => ?_⟩
  have := norm_integral_le_integral_norm (μ := D.μ) (fun y => q08gl_kg D x y)
  simpa [q08e_a, Real.norm_eq_abs] using this.trans (hM x)

theorem q08gl_arow_meas : Measurable (q08e_a D.μ (q08gl_kg D)) :=
  q08e_a_meas' D.μ (q08gl_kg D) (q08gl_kg_meas' D) (q08gl_kg_sq_int D)

theorem q08gl_kt_row (hu : q08gl_UData D.μ u) (j : Fin m) (x : Torus d) :
    ∫ y, q08e_kt D.μ (q08gl_kg D) x y * u j y ∂D.μ =
      ∫ y, q08gl_kg D x y * u j y ∂D.μ - ∫ y, q08e_a D.μ (q08gl_kg D) y * u j y ∂D.μ := by
  haveI := q08_isProb_μ D
  obtain ⟨Ma, hMa⟩ := q08gl_a_bdd D
  obtain ⟨Mu, hMu⟩ := hu.bdd j
  have hui : Integrable (u j) D.μ := q08gl_int_u hu j
  have I1 : Integrable (fun y => q08gl_kg D x y * u j y) D.μ := by
    have := (q08f_rowOK_g D).int x
    exact this.mul_bdd (hu.meas j).aestronglyMeasurable (c := Mu)
      (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hMu y)
  have I2 : Integrable (fun y => q08e_a D.μ (q08gl_kg D) x * u j y) D.μ := hui.const_mul _
  have I3 : Integrable (fun y => q08e_a D.μ (q08gl_kg D) y * u j y) D.μ :=
    hui.bdd_mul (q08gl_arow_meas D).aestronglyMeasurable (c := Ma)
      (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hMa y)
  have I4 : Integrable (fun y => q08e_m D.μ (q08gl_kg D) * u j y) D.μ := hui.const_mul _
  have hpt : ∀ y, q08e_kt D.μ (q08gl_kg D) x y * u j y = q08gl_kg D x y * u j y -
      q08e_a D.μ (q08gl_kg D) x * u j y - q08e_a D.μ (q08gl_kg D) y * u j y +
        q08e_m D.μ (q08gl_kg D) * u j y := fun y => by unfold q08e_kt; ring
  have I12 : Integrable (fun y => q08gl_kg D x y * u j y - q08e_a D.μ (q08gl_kg D) x * u j y) D.μ := I1.sub I2
  have I123 : Integrable (fun y => q08gl_kg D x y * u j y - q08e_a D.μ (q08gl_kg D) x * u j y -
      q08e_a D.μ (q08gl_kg D) y * u j y) D.μ := I12.sub I3
  simp_rw [hpt]
  rw [integral_add I123 I4, integral_sub I12 I3, integral_sub I1 I2,
    integral_const_mul, integral_const_mul, hu.cent j]
  ring

theorem q08gl_Kt_mean (hu : q08gl_UData D.μ u) (j : Fin m) :
    ∫ x, ∫ y, q08gl_kg D x y * u j y ∂D.μ ∂D.μ = ∫ y, q08e_a D.μ (q08gl_kg D) y * u j y ∂D.μ := by
  haveI := q08_isProb_μ D
  obtain ⟨Mu, hMu⟩ := hu.bdd j
  have hint : Integrable (Function.uncurry fun x y => q08gl_kg D x y * u j y) (D.μ.prod D.μ) := by
    have h1 : Integrable (fun z : Torus d × Torus d => q08gl_kg D z.1 z.2) (D.μ.prod D.μ) :=
      (q08gl_kg_memLp D).integrable one_le_two
    have h2 : AEStronglyMeasurable (fun z : Torus d × Torus d => u j z.2) (D.μ.prod D.μ) :=
      ((hu.meas j).comp measurable_snd).aestronglyMeasurable
    exact h1.mul_bdd h2 (c := Mu) (Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hMu z.2)
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [integral_mul_const]
  congr 1
  simp only [q08e_a]
  exact integral_congr_ae (Eventually.of_forall fun x => q08gl_kg_symm' D x y)

/-- The kernel-integral form of `P K u_j`. -/
theorem q08gl_PK_ae (hu : q08gl_UData D.μ u) (j : Fin m) :
    ∀ᵐ x ∂D.μ, (projL (oneL D.hρ.density) (KL (q08s_setup D) (q08gl_ub D hu j)) : Torus d → ℝ) x =
      ∫ y, q08e_kt D.μ (q08gl_kg D) x y * u j y ∂D.μ := by
  have h1 : Kt (periodicRiesz d D.s) (withDensityReal D.ρ) (q08gl_ub D hu j) =
      Kt (periodicRiesz d D.s) (withDensityReal D.ρ) (u j) := Kt_congr _ (q08gl_ub_coe D hu j)
  have hint : ∫ y, (KL (q08s_setup D) (q08gl_ub D hu j) : Torus d → ℝ) y ∂(withDensityReal D.ρ) =
      ∫ y, Kt (periodicRiesz d D.s) (withDensityReal D.ρ) (q08gl_ub D hu j) y ∂(withDensityReal D.ρ) :=
    integral_congr_ae (KLfun_coe (q08s_setup D) (q08gl_ub D hu j))
  filter_upwards [projL_coe D.hρ.density (KL (q08s_setup D) (q08gl_ub D hu j)),
    KLfun_coe (q08s_setup D) (q08gl_ub D hu j)] with x hx1 hx2
  rw [hx1, hint]
  have e1 : (KL (q08s_setup D) (q08gl_ub D hu j) : Torus d → ℝ) x =
      Kt (periodicRiesz d D.s) (withDensityReal D.ρ) (q08gl_ub D hu j) x := hx2
  rw [e1, h1, q08gl_kt_row D hu j x, ← q08gl_Kt_mean D hu j]
  rfl

theorem q08gl_norm_sq_lp {ν : Measure (Torus d)} (f : Lp ℝ 2 ν) :
    ‖f‖ ^ 2 = ∫ x, (f x) ^ 2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [sq]

theorem q08gl_PK_norm_eq (hu : q08gl_UData D.μ u) (j : Fin m) :
    ‖projL (oneL D.hρ.density) (KL (q08s_setup D) (q08gl_ub D hu j))‖ ^ 2 =
      ∫ x, (∫ y, q08e_kt D.μ (q08gl_kg D) x y * u j y ∂D.μ) ^ 2 ∂D.μ := by
  rw [q08gl_norm_sq_lp]
  refine integral_congr_ae ?_
  filter_upwards [q08gl_PK_ae D hu j] with x hx
  rw [hx]

theorem q08gl_PK_sq_int (hu : q08gl_UData D.μ u) (j : Fin m) :
    Integrable (fun x => (∫ y, q08e_kt D.μ (q08gl_kg D) x y * u j y ∂D.μ) ^ 2) D.μ := by
  have hmem := Lp.memLp (projL (oneL D.hρ.density) (KL (q08s_setup D) (q08gl_ub D hu j)))
  refine (hmem.integrable_sq).congr ?_
  filter_upwards [q08gl_PK_ae D hu j] with x hx
  rw [hx]

theorem q08gl_row_meas {T : Type*} [MeasurableSpace T] (k : T → T → ℝ) (hk : Measurable (Function.uncurry k))
    (x : T) : Measurable (fun y => k x y) := hk.comp (measurable_const.prodMk measurable_id)

theorem q08gl_bessel_pt (hu : q08gl_UData D.μ u) (x : Torus d)
    (hx : Integrable (fun y => q08e_kt D.μ (q08gl_kg D) x y ^ 2) D.μ) :
    ∑ j, (∫ y, q08e_kt D.μ (q08gl_kg D) x y * u j y ∂D.μ) ^ 2 ≤ ∫ y, q08e_kt D.μ (q08gl_kg D) x y ^ 2 ∂D.μ := by
  have hkm : Measurable (Function.uncurry (q08e_kt D.μ (q08gl_kg D))) :=
    q08e_kt_meas D.μ (q08gl_kg D) (q08gl_kg_meas' D) (q08gl_kg_sq_int D)
  have hrm : Measurable (fun y => q08e_kt D.μ (q08gl_kg D) x y) := q08gl_row_meas _ hkm x
  have hmem : MemLp (fun y => q08e_kt D.μ (q08gl_kg D) x y) 2 D.μ :=
    (memLp_two_iff_integrable_sq hrm.aestronglyMeasurable).2 hx
  have hmu : ∀ j, MemLp (u j) 2 D.μ := fun j => q08gl_memLp_u D hu j
  have := (q08s_bessel D.μ u hmu hu.orth (fun y => q08e_kt D.μ (q08gl_kg D) x y) hmem).2
  rw [tsum_fintype] at this
  exact this

/-- Bessel's inequality for the kernel `k_c` against the orthonormal family `u`. -/
theorem q08gl_PK_norm_sum (hu : q08gl_UData D.μ u) :
    ∑ j, ‖projL (oneL D.hρ.density) (KL (q08s_setup D) (q08gl_ub D hu j))‖ ^ 2 ≤
      ∫ z : Torus d × Torus d, q08e_kt D.μ (q08gl_kg D) z.1 z.2 ^ 2 ∂(D.μ.prod D.μ) := by
  have hksq : Integrable (fun z : Torus d × Torus d => q08e_kt D.μ (q08gl_kg D) z.1 z.2 ^ 2) (D.μ.prod D.μ) :=
    (q08e_kt_memLp D.μ (q08gl_kg D) (q08gl_kg_meas' D) (q08gl_kg_sq_int D)).integrable_sq
  simp_rw [q08gl_PK_norm_eq D hu]
  rw [← integral_finsetSum _ fun j _ => q08gl_PK_sq_int D hu j]
  rw [integral_prod _ hksq]
  have hrow : ∀ᵐ x ∂D.μ, Integrable (fun y => q08e_kt D.μ (q08gl_kg D) x y ^ 2) D.μ :=
    ((integrable_prod_iff hksq.aestronglyMeasurable).1 hksq).1
  refine integral_mono_ae (integrable_finsetSum _ fun j _ => q08gl_PK_sq_int D hu j) hksq.integral_prod_left ?_
  filter_upwards [hrow] with x hx
  exact q08gl_bessel_pt D hu x hx

theorem q08gl_inner_PK (hu : q08gl_UData D.μ u) (k l : Fin m) :
    q08gl_KUe D u k l = ∫ x, u k x * ∫ y, q08e_kt D.μ (q08gl_kg D) x y * u l y ∂D.μ ∂D.μ := by
  rw [← q08gl_KUe_eq D hu k l]
  have h1 : inner ℝ (q08gl_ub D hu k) (KL (q08s_setup D) (q08gl_ub D hu l)) =
      inner ℝ (q08gl_ub D hu k) (projL (oneL D.hρ.density) (KL (q08s_setup D) (q08gl_ub D hu l))) := by
    conv_lhs => rw [← q08gl_ub_P D hu k]
    rw [inner_projL_left]
  rw [h1, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [q08gl_ub_coe D hu k, q08gl_PK_ae D hu l] with x h1 h2
  simp only [h1, h2]
  simp [mul_comm]

theorem q08gl_kt_tensor_int (hu : q08gl_UData D.μ u) (k l : Fin m) :
    Integrable (fun z : Torus d × Torus d => q08e_kt D.μ (q08gl_kg D) z.1 z.2 * (u k z.1 * u l z.2))
      (D.μ.prod D.μ) := by
  haveI := q08_isProb_μ D
  obtain ⟨Mk, hMk⟩ := hu.bdd k
  obtain ⟨Ml, hMl⟩ := hu.bdd l
  have hk1 : Integrable (fun z : Torus d × Torus d => q08e_kt D.μ (q08gl_kg D) z.1 z.2) (D.μ.prod D.μ) :=
    (q08e_kt_memLp D.μ (q08gl_kg D) (q08gl_kg_meas' D) (q08gl_kg_sq_int D)).integrable one_le_two
  have hb : AEStronglyMeasurable (fun z : Torus d × Torus d => u k z.1 * u l z.2) (D.μ.prod D.μ) :=
    (((hu.meas k).comp measurable_fst).mul ((hu.meas l).comp measurable_snd)).aestronglyMeasurable
  exact hk1.mul_bdd hb (c := Mk * Ml) (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hMk z.1) (hMl z.2) (abs_nonneg _) ((abs_nonneg _).trans (hMk z.1)))

theorem q08gl_kt_tensor (hu : q08gl_UData D.μ u) (k l : Fin m) :
    ∫ z : Torus d × Torus d, q08e_kt D.μ (q08gl_kg D) z.1 z.2 * (u k z.1 * u l z.2) ∂(D.μ.prod D.μ) =
      q08gl_KUe D u k l := by
  haveI := q08_isProb_μ D
  have hint := q08gl_kt_tensor_int D hu k l
  rw [integral_prod _ hint, q08gl_inner_PK D hu k l]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  ring

/-- Pythagoras for the projection onto an orthonormal family. -/
theorem q08gl_pyth {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (v : Fin m → H)
    (hv : Orthonormal ℝ v) (x : H) :
    ‖x - ∑ k, inner ℝ (v k) x • v k‖ ^ 2 = ‖x‖ ^ 2 - ∑ k, inner ℝ (v k) x ^ 2 := by
  have h1 : inner ℝ x (∑ k, inner ℝ (v k) x • v k) = ∑ k, inner ℝ (v k) x ^ 2 := by
    rw [inner_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [real_inner_smul_right, real_inner_comm]; ring
  have h2 : ‖∑ k, inner ℝ (v k) x • v k‖ ^ 2 = ∑ k, inner ℝ (v k) x ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_sum]
    simp_rw [sum_inner, real_inner_smul_left, real_inner_smul_right]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := orthonormal_iff_ite.1 hv
    simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  rw [norm_sub_sq_real, h1, h2]
  ring

/-- The matrix `K^U`. -/
def q08gl_KU (u : Fin m → Torus d → ℝ) : Matrix (Fin m) (Fin m) ℝ := Matrix.of (q08gl_KUe D u)

theorem q08gl_rho_eq (hu : q08gl_UData D.μ u) :
    ∫ z : Torus d × Torus d, (q08e_kt D.μ (q08gl_kg D) z.1 z.2 - q08gl_kap u (q08gl_KU D u) z.1 z.2) ^ 2
        ∂(D.μ.prod D.μ) =
      ∫ z : Torus d × Torus d, q08e_kt D.μ (q08gl_kg D) z.1 z.2 ^ 2 ∂(D.μ.prod D.μ) -
        ∑ k, ∑ l, q08gl_KUe D u k l ^ 2 := by
  haveI := q08_isProb_μ D
  have hkt : MemLp (fun z : Torus d × Torus d => q08e_kt D.μ (q08gl_kg D) z.1 z.2) 2 (D.μ.prod D.μ) :=
    q08e_kt_memLp D.μ (q08gl_kg D) (q08gl_kg_meas' D) (q08gl_kg_sq_int D)
  have hkap : MemLp (fun z : Torus d × Torus d => q08gl_kap u (q08gl_KU D u) z.1 z.2) 2 (D.μ.prod D.μ) :=
    q08gl_kap_memLp (q08gl_KU D u) hu
  have i1 := hkt.integrable_sq
  have i2 := hkap.integrable_sq
  have i3 : Integrable (fun z : Torus d × Torus d => q08e_kt D.μ (q08gl_kg D) z.1 z.2 *
      q08gl_kap u (q08gl_KU D u) z.1 z.2) (D.μ.prod D.μ) := hkt.integrable_mul hkap
  have e1 : ∀ z : Torus d × Torus d, (q08e_kt D.μ (q08gl_kg D) z.1 z.2 - q08gl_kap u (q08gl_KU D u) z.1 z.2) ^ 2 =
      q08e_kt D.μ (q08gl_kg D) z.1 z.2 ^ 2 - 2 * (q08e_kt D.μ (q08gl_kg D) z.1 z.2 *
        q08gl_kap u (q08gl_KU D u) z.1 z.2) + q08gl_kap u (q08gl_KU D u) z.1 z.2 ^ 2 := fun z => by ring
  have i3' : Integrable (fun z : Torus d × Torus d => 2 * (q08e_kt D.μ (q08gl_kg D) z.1 z.2 *
      q08gl_kap u (q08gl_KU D u) z.1 z.2)) (D.μ.prod D.μ) := i3.const_mul 2
  have i13 : Integrable (fun z : Torus d × Torus d => q08e_kt D.μ (q08gl_kg D) z.1 z.2 ^ 2 -
      2 * (q08e_kt D.μ (q08gl_kg D) z.1 z.2 * q08gl_kap u (q08gl_KU D u) z.1 z.2)) (D.μ.prod D.μ) := i1.sub i3'
  simp_rw [e1]
  rw [integral_add i13 i2, integral_sub i1 i3', integral_const_mul,
    q08gl_kap_sq (q08gl_KU D u) hu]
  -- the cross term
  have hcross : ∫ z : Torus d × Torus d, q08e_kt D.μ (q08gl_kg D) z.1 z.2 *
      q08gl_kap u (q08gl_KU D u) z.1 z.2 ∂(D.μ.prod D.μ) = ∑ k, ∑ l, q08gl_KUe D u k l ^ 2 := by
    have hb : ∀ k l : Fin m, Integrable (fun z : Torus d × Torus d => q08gl_KU D u k l *
        (q08e_kt D.μ (q08gl_kg D) z.1 z.2 * (u k z.1 * u l z.2))) (D.μ.prod D.μ) := fun k l =>
      (q08gl_kt_tensor_int D hu k l).const_mul _
    have hpt : ∀ z : Torus d × Torus d, q08e_kt D.μ (q08gl_kg D) z.1 z.2 *
        q08gl_kap u (q08gl_KU D u) z.1 z.2 = ∑ k, ∑ l, q08gl_KU D u k l *
          (q08e_kt D.μ (q08gl_kg D) z.1 z.2 * (u k z.1 * u l z.2)) := by
      intro z
      unfold q08gl_kap
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    simp_rw [hpt]
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hb k l]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun l _ => hb k l]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul, q08gl_kt_tensor D hu k l]
    simp [q08gl_KU, sq]
  have hKU : ∀ x y, q08gl_KU D u x y = q08gl_KUe D u x y := fun _ _ => rfl
  simp only [hKU]
  rw [hcross]
  ring

end Kernel

section SigmaEst

variable {m : ℕ} {u : Fin m → Torus d → ℝ}

/-- `Σ_{kl} = ⟨u_k, R u_l⟩`. -/
def q08gl_Sig (hu : q08gl_UData D.μ u) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun k l => inner ℝ (q08gl_ub D hu k) (q08gl_R D (q08gl_ub D hu l))

theorem q08gl_Sig_est (hu : q08gl_UData D.μ u) :
    ∑ j, ∑ l, (((1 + D.β • q08gl_KU D u) * q08gl_Sig D hu - 1) j l) ^ 2 ≤
      D.β ^ 2 * ∫ z : Torus d × Torus d, (q08e_kt D.μ (q08gl_kg D) z.1 z.2 -
        q08gl_kap u (q08gl_KU D u) z.1 z.2) ^ 2 ∂(D.μ.prod D.μ) := by
  have hone : ‖oneL D.hρ.density‖ = 1 := norm_oneL D.hρ.density
  have hKs : ∀ x y, inner ℝ (KL (q08s_setup D) x) y = inner ℝ x (KL (q08s_setup D) y) := fun x y => by
    rw [q08s_KL_symm (q08s_setup D) x y, real_inner_comm]
  have hR : ∀ x, q08gl_R D x + D.β • projL (oneL D.hρ.density) (KL (q08s_setup D)
      (projL (oneL D.hρ.density) (q08gl_R D x))) = x := fun x => by
    have := q08gl_R_T D x
    unfold q08gl_T at this
    rw [Top_apply] at this
    exact this
  have h := q08gl_abstract_est (KL (q08s_setup D)) (projL (oneL D.hρ.density)) (q08gl_R D) D.β hKs
    (projL_projL hone) (inner_projL_left _) hR (q08gl_R_contr D) (q08gl_R_selfadj D)
    (q08gl_ub D hu) (q08gl_ub_orthonormal D hu) (q08gl_ub_P D hu)
  have hmat : ∀ j l, ((1 + D.β • q08gl_KU D u) * q08gl_Sig D hu - 1) j l =
      (inner ℝ (q08gl_ub D hu j) (q08gl_R D (q08gl_ub D hu l)) + D.β * ∑ k,
        inner ℝ (q08gl_ub D hu j) (KL (q08s_setup D) (q08gl_ub D hu k)) *
          inner ℝ (q08gl_ub D hu k) (q08gl_R D (q08gl_ub D hu l))) - (if j = l then 1 else 0) := by
    intro j l
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
      add_mul, Finset.sum_add_distrib, smul_eq_mul, q08gl_Sig, Matrix.of_apply, q08gl_KU]
    simp only [q08gl_KUe_eq D hu, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true, Finset.mul_sum]
    refine congrArg₂ _ (congrArg₂ _ rfl ?_) rfl
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp_rw [hmat]
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
  -- the kernel estimate
  have hP : ∀ k j, inner ℝ (q08gl_ub D hu k) (projL (oneL D.hρ.density) (KL (q08s_setup D) (q08gl_ub D hu j))) =
      q08gl_KUe D u k j := by
    intro k j
    rw [← inner_projL_left, q08gl_ub_P D hu k, q08gl_KUe_eq D hu]
  have hw : ∀ j, ‖projL (oneL D.hρ.density) (KL (q08s_setup D) (q08gl_ub D hu j)) -
      ∑ k, inner ℝ (q08gl_ub D hu k) (projL (oneL D.hρ.density) (KL (q08s_setup D) (q08gl_ub D hu j))) •
        q08gl_ub D hu k‖ ^ 2 = ‖projL (oneL D.hρ.density) (KL (q08s_setup D) (q08gl_ub D hu j))‖ ^ 2 -
          ∑ k, q08gl_KUe D u k j ^ 2 := by
    intro j
    rw [q08gl_pyth (q08gl_ub D hu) (q08gl_ub_orthonormal D hu)]
    simp_rw [hP]
  simp_rw [hw]
  rw [Finset.sum_sub_distrib, q08gl_rho_eq D hu, Finset.sum_comm (f := fun j k => q08gl_KUe D u k j ^ 2)]
  linarith [q08gl_PK_norm_sum D hu]

end SigmaEst

end HRS.Q08

end
