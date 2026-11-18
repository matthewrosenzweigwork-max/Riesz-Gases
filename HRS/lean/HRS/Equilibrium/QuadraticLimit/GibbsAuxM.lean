import HRS.Equilibrium.QuadraticLimit.GibbsAuxL
import HRS.Equilibrium.QuadraticLimit.Chaos
import HRS.Equilibrium.QuadraticLimit.Features

/-!
# Lemma 7.5, `q08_gibbs_approx`: Gaussian coupling (prefix `q08gl_`)
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Matrix

noncomputable section

namespace HRS.Q08

section Push

/-- Linear image of a centred multivariate Gaussian. -/
theorem q08gl_push {L m : ℕ} (c : Matrix (Fin m) (Fin L) ℝ) (C : Matrix (Fin L) (Fin L) ℝ)
    (hC : C.PosSemidef) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin L)) C).map
      (fun g : EuclideanSpace ℝ (Fin L) =>
        (WithLp.toLp 2 (c *ᵥ (WithLp.ofLp g)) : EuclideanSpace ℝ (Fin m))) =
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (c * C * cᵀ) := by
  have hP : (c * C * cᵀ).PosSemidef := by
    simpa using hC.mul_mul_conjTranspose_same c
  have hmeas : Measurable (fun g : EuclideanSpace ℝ (Fin L) =>
      (WithLp.toLp 2 (c *ᵥ (WithLp.ofLp g)) : EuclideanSpace ℝ (Fin m))) := by fun_prop
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_multivariateGaussian hP, charFun_apply, integral_map hmeas.aemeasurable (by fun_prop)]
  have hin : ∀ g : EuclideanSpace ℝ (Fin L),
      inner ℝ (WithLp.toLp 2 (c *ᵥ (WithLp.ofLp g)) : EuclideanSpace ℝ (Fin m)) t =
        inner ℝ g (WithLp.toLp 2 (cᵀ *ᵥ (WithLp.ofLp t)) : EuclideanSpace ℝ (Fin L)) := by
    intro g
    simp only [PiLp.inner_apply, Matrix.mulVec, dotProduct, RCLike.inner_apply, conj_trivial]
    simp only [Finset.sum_mul, Finset.mul_sum, Matrix.transpose_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  simp_rw [hin]
  rw [← charFun_apply, charFun_multivariateGaussian hC]
  congr 2
  · simp
  · have h3 : (c * C * cᵀ) *ᵥ WithLp.ofLp t = c *ᵥ (C *ᵥ (cᵀ *ᵥ WithLp.ofLp t)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have key : t.ofLp ⬝ᵥ (c *ᵥ (C *ᵥ (cᵀ *ᵥ WithLp.ofLp t))) =
        (cᵀ *ᵥ WithLp.ofLp t) ⬝ᵥ (C *ᵥ (cᵀ *ᵥ WithLp.ofLp t)) := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    rw [h3, key]

end Push

theorem q08gl_memLp_u' {T : Type*} [MeasurableSpace T] {μ : Measure T} [IsProbabilityMeasure μ] {m : ℕ}
    {u : Fin m → T → ℝ} (hu : q08gl_UData μ u) (k : Fin m) : MemLp (u k) 2 μ := by
  obtain ⟨M, hM⟩ := hu.bdd k
  exact MemLp.of_bound (hu.meas k).aestronglyMeasurable M
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hM x)

section Coef

variable {T : Type*} [MeasurableSpace T] {μ : Measure T} [IsProbabilityMeasure μ]

/-- Bessel for the orthonormal family `e_i ⊗ e_j` in `L²(μ ⊗ μ)` (finite sections). -/
theorem q08gl_bessel2 (e : ℕ → T → ℝ) (he : ∀ i, MemLp (e i) 2 μ)
    (ho : ∀ i j, ∫ x, e i x * e j x ∂μ = if i = j then 1 else 0) (w : T → T → ℝ)
    (hw : MemLp (fun z : T × T => w z.1 z.2) 2 (μ.prod μ)) (L : ℕ) :
    ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
      (∫ z : T × T, w z.1 z.2 * (e i z.1 * e j z.2) ∂(μ.prod μ)) ^ 2 ≤
      ∫ z : T × T, w z.1 z.2 ^ 2 ∂(μ.prod μ) := by
  set f : ℕ × ℕ → T × T → ℝ := fun ij z => e ij.1 z.1 * e ij.2 z.2 with hf
  have hfm : ∀ ij, MemLp (f ij) 2 (μ.prod μ) := fun ij => q08s_memLp_tensor (he _) (he _)
  have hfo : ∀ ij kl, ∫ z, f ij z * f kl z ∂(μ.prod μ) = if ij = kl then 1 else 0 := by
    intro ij kl
    have : ∀ z : T × T, f ij z * f kl z = (e ij.1 z.1 * e kl.1 z.1) * (e ij.2 z.2 * e kl.2 z.2) := by
      intro z; simp only [hf]; ring
    simp_rw [this]
    rw [integral_prod_mul (fun x => e ij.1 x * e kl.1 x) (fun y => e ij.2 y * e kl.2 y), ho, ho]
    rcases ij with ⟨a, b⟩
    rcases kl with ⟨c, d⟩
    by_cases h1 : a = c <;> by_cases h2 : b = d <;> simp [h1, h2]
  obtain ⟨hs, hle⟩ := q08s_bessel (μ.prod μ) f hfm hfo _ hw
  have hterm : ∀ ij : ℕ × ℕ, (∫ z : T × T, w z.1 z.2 * f ij z ∂(μ.prod μ)) =
      ∫ z : T × T, w z.1 z.2 * (e ij.1 z.1 * e ij.2 z.2) ∂(μ.prod μ) := fun ij => rfl
  have h1 : ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
      (∫ z : T × T, w z.1 z.2 * (e i z.1 * e j z.2) ∂(μ.prod μ)) ^ 2 =
      ∑ ij ∈ Finset.range L ×ˢ Finset.range L, (∫ z : T × T, w z.1 z.2 * f ij z ∂(μ.prod μ)) ^ 2 := by
    rw [Finset.sum_product]
  rw [h1]
  exact (hs.sum_le_tsum _ fun _ _ => sq_nonneg _).trans hle

/-- Coefficients of the degenerate part of a kernel against centred functions. -/
theorem q08gl_kt_coef (k : T → T → ℝ) (hm : Measurable (Function.uncurry k))
    (hk : Integrable (fun z : T × T => k z.1 z.2 ^ 2) (μ.prod μ)) (e1 e2 : T → ℝ)
    (h1 : MemLp e1 2 μ) (h2 : MemLp e2 2 μ) (c1 : ∫ x, e1 x ∂μ = 0) (c2 : ∫ x, e2 x ∂μ = 0) :
    ∫ z : T × T, q08e_kt μ k z.1 z.2 * (e1 z.1 * e2 z.2) ∂(μ.prod μ) =
      ∫ z : T × T, k z.1 z.2 * (e1 z.1 * e2 z.2) ∂(μ.prod μ) := by
  have hk2 := q08e_k_memLp μ k hm hk
  have hA : MemLp (q08e_a μ k) 2 μ := (q08e_a_memLp μ k hm hk).1
  have hi1 : Integrable e1 μ := h1.integrable one_le_two
  have hi2 : Integrable e2 μ := h2.integrable one_le_two
  have hAe1 : Integrable (fun x => q08e_a μ k x * e1 x) μ := hA.integrable_mul h1
  have hAe2 : Integrable (fun x => q08e_a μ k x * e2 x) μ := hA.integrable_mul h2
  have P0 : Integrable (fun z : T × T => k z.1 z.2 * (e1 z.1 * e2 z.2)) (μ.prod μ) :=
    hk2.integrable_mul (q08s_memLp_tensor h1 h2)
  have P1 : Integrable (fun z : T × T => (q08e_a μ k z.1 * e1 z.1) * e2 z.2) (μ.prod μ) :=
    hAe1.mul_prod hi2
  have P2 : Integrable (fun z : T × T => e1 z.1 * (q08e_a μ k z.2 * e2 z.2)) (μ.prod μ) :=
    hi1.mul_prod hAe2
  have P3 : Integrable (fun z : T × T => q08e_m μ k * (e1 z.1 * e2 z.2)) (μ.prod μ) :=
    (hi1.mul_prod hi2).const_mul _
  have hdec : ∀ z : T × T, q08e_kt μ k z.1 z.2 * (e1 z.1 * e2 z.2) =
      k z.1 z.2 * (e1 z.1 * e2 z.2) - (q08e_a μ k z.1 * e1 z.1) * e2 z.2 -
        e1 z.1 * (q08e_a μ k z.2 * e2 z.2) + q08e_m μ k * (e1 z.1 * e2 z.2) := by
    intro z; unfold q08e_kt; ring
  have Q1 : Integrable (fun z : T × T => k z.1 z.2 * (e1 z.1 * e2 z.2) -
      (q08e_a μ k z.1 * e1 z.1) * e2 z.2) (μ.prod μ) := P0.sub P1
  have Q2 : Integrable (fun z : T × T => k z.1 z.2 * (e1 z.1 * e2 z.2) -
      (q08e_a μ k z.1 * e1 z.1) * e2 z.2 - e1 z.1 * (q08e_a μ k z.2 * e2 z.2)) (μ.prod μ) := Q1.sub P2
  simp_rw [hdec]
  rw [integral_add Q2 P3, integral_sub Q1 P2, integral_sub P0 P1,
    integral_prod_mul (fun x => q08e_a μ k x * e1 x) e2, integral_prod_mul e1 (fun x => q08e_a μ k x * e2 x),
    integral_const_mul, integral_prod_mul e1 e2, c1, c2]
  simp

/-- Coefficients of the finite-rank kernel `κ_A` against `e1 ⊗ e2`. -/
theorem q08gl_kap_coef {m : ℕ} {u : Fin m → T → ℝ} (hu : q08gl_UData μ u)
    (A : Matrix (Fin m) (Fin m) ℝ) (e1 e2 : T → ℝ) (h1 : MemLp e1 2 μ) (h2 : MemLp e2 2 μ) :
    ∫ z : T × T, q08gl_kap u A z.1 z.2 * (e1 z.1 * e2 z.2) ∂(μ.prod μ) =
      ∑ k, ∑ l, A k l * (∫ x, u k x * e1 x ∂μ) * (∫ y, u l y * e2 y ∂μ) := by
  have hI : ∀ k : Fin m, Integrable (fun x => u k x * e1 x) μ := fun k =>
    (q08gl_memLp_u' hu k).integrable_mul h1
  have hJ : ∀ l : Fin m, Integrable (fun x => u l x * e2 x) μ := fun l =>
    (q08gl_memLp_u' hu l).integrable_mul h2
  have hdec : ∀ z : T × T, q08gl_kap u A z.1 z.2 * (e1 z.1 * e2 z.2) =
      ∑ k, ∑ l, A k l * ((u k z.1 * e1 z.1) * (u l z.2 * e2 z.2)) := by
    intro z
    unfold q08gl_kap
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have hint : ∀ k l : Fin m, Integrable (fun z : T × T => A k l * ((u k z.1 * e1 z.1) * (u l z.2 * e2 z.2)))
      (μ.prod μ) := fun k l => ((hI k).mul_prod (hJ l)).const_mul _
  simp_rw [hdec]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun l _ => hint k l]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul, integral_prod_mul (fun x => u k x * e1 x) (fun y => u l y * e2 y)]
  ring

end Coef

section DCoef

variable {d : ℕ} (D : Q08Data d) {m : ℕ} {u : Fin m → Torus d → ℝ}

theorem q08gl_Hmat_coef (i j : ℕ) :
    D.Hmat i j = ∫ z : Torus d × Torus d, q08e_kt D.μ D.h z.1 z.2 * (D.e i z.1 * D.e j z.2) ∂(D.μ.prod D.μ) := by
  have hk : Integrable (fun z : Torus d × Torus d => D.h z.1 z.2 ^ 2) (D.μ.prod D.μ) :=
    (q08s_h_memLp D).integrable_sq
  rw [q08gl_kt_coef D.h D.hmeas hk (D.e i) (D.e j) (D.he.memLp i) (D.he.memLp j)
    (D.he.centered i) (D.he.centered j)]
  have hint : Integrable (fun z : Torus d × Torus d => D.h z.1 z.2 * (D.e i z.1 * D.e j z.2)) (D.μ.prod D.μ) :=
    (q08s_h_memLp D).integrable_mul (q08s_memLp_tensor (D.he.memLp i) (D.he.memLp j))
  rw [integral_prod _ hint]
  unfold Q08Data.Hmat
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  ring

/-- The kernel part of the comparison: `∑_{i,j<L} ((cᵀ H' c)_{ij} - H_{ij})² ≤ ε₀²`. -/
theorem q08gl_Hbound (hu : q08gl_UData D.μ u) (H' : Matrix (Fin m) (Fin m) ℝ) (ε0 : ℝ)
    (hH : ∫ z : Torus d × Torus d, (q08e_kt D.μ D.h z.1 z.2 - q08gl_kap u H' z.1 z.2) ^ 2 ∂(D.μ.prod D.μ) ≤ ε0 ^ 2)
    (L : ℕ) :
    ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
      (∑ k, ∑ l, q08gl_cf D u k i * H' k l * q08gl_cf D u l j - D.Hmat i j) ^ 2 ≤ ε0 ^ 2 := by
  have hk : Integrable (fun z : Torus d × Torus d => D.h z.1 z.2 ^ 2) (D.μ.prod D.μ) :=
    (q08s_h_memLp D).integrable_sq
  have hw : MemLp (fun z : Torus d × Torus d => q08e_kt D.μ D.h z.1 z.2 - q08gl_kap u H' z.1 z.2) 2
      (D.μ.prod D.μ) :=
    (q08e_kt_memLp D.μ D.h D.hmeas hk).sub (q08gl_kap_memLp H' hu)
  have hb : ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
      (∫ z : Torus d × Torus d, (q08e_kt D.μ D.h z.1 z.2 - q08gl_kap u H' z.1 z.2) *
        (D.e i z.1 * D.e j z.2) ∂(D.μ.prod D.μ)) ^ 2 ≤
      ∫ z : Torus d × Torus d, (q08e_kt D.μ D.h z.1 z.2 - q08gl_kap u H' z.1 z.2) ^ 2 ∂(D.μ.prod D.μ) :=
    q08gl_bessel2 (μ := D.μ) D.e D.he.memLp (q08s_e_ortho D)
      (fun x y => q08e_kt D.μ D.h x y - q08gl_kap u H' x y) hw L
  refine le_trans (le_of_eq ?_) (hb.trans hH)
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : ∫ z : Torus d × Torus d, (q08e_kt D.μ D.h z.1 z.2 - q08gl_kap u H' z.1 z.2) *
      (D.e i z.1 * D.e j z.2) ∂(D.μ.prod D.μ) = D.Hmat i j - ∑ k, ∑ l, q08gl_cf D u k i * H' k l * q08gl_cf D u l j := by
    have i1 : Integrable (fun z : Torus d × Torus d => q08e_kt D.μ D.h z.1 z.2 * (D.e i z.1 * D.e j z.2))
        (D.μ.prod D.μ) := (q08e_kt_memLp D.μ D.h D.hmeas hk).integrable_mul
          (q08s_memLp_tensor (D.he.memLp i) (D.he.memLp j))
    have i2 : Integrable (fun z : Torus d × Torus d => q08gl_kap u H' z.1 z.2 * (D.e i z.1 * D.e j z.2))
        (D.μ.prod D.μ) := (q08gl_kap_memLp H' hu).integrable_mul
          (q08s_memLp_tensor (D.he.memLp i) (D.he.memLp j))
    have : ∀ z : Torus d × Torus d, (q08e_kt D.μ D.h z.1 z.2 - q08gl_kap u H' z.1 z.2) * (D.e i z.1 * D.e j z.2) =
        q08e_kt D.μ D.h z.1 z.2 * (D.e i z.1 * D.e j z.2) - q08gl_kap u H' z.1 z.2 * (D.e i z.1 * D.e j z.2) := by
      intro z; ring
    simp_rw [this]
    rw [integral_sub i1 i2, ← q08gl_Hmat_coef D i j, q08gl_kap_coef hu H' (D.e i) (D.e j) (D.he.memLp i)
      (D.he.memLp j)]
    congr 1
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    unfold q08gl_cf
    ring
  rw [h1]
  ring

/-- The test-function part of the comparison. -/
theorem q08gl_phibound (hu : q08gl_UData D.μ u) (b : Fin D.p) (α : Fin m → ℝ) (ε0 : ℝ)
    (hα : ∫ x, (D.φ b x - pair D.μ (D.φ b) - ∑ k, α k * u k x) ^ 2 ∂D.μ ≤ ε0 ^ 2) (L : ℕ) :
    ∑ i ∈ Finset.range L, (D.coef b i - ∑ k, α k * q08gl_cf D u k i) ^ 2 ≤ ε0 ^ 2 := by
  obtain ⟨hm, M, hM⟩ := D.hφ b
  have hφ : MemLp (D.φ b) 2 D.μ :=
    MemLp.of_bound hm.aestronglyMeasurable M (Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hM x)
  have hG : MemLp (fun x => D.φ b x - pair D.μ (D.φ b) - ∑ k, α k * u k x) 2 D.μ :=
    (hφ.sub (memLp_const _)).sub (q08gl_memLp_comb D hu α)
  obtain ⟨hs, hle⟩ := q08s_bessel D.μ D.e D.he.memLp (q08s_e_ortho D) _ hG
  have hco : ∀ i, ∫ x, (D.φ b x - pair D.μ (D.φ b) - ∑ k, α k * u k x) * D.e i x ∂D.μ =
      D.coef b i - ∑ k, α k * q08gl_cf D u k i := by
    intro i
    have i1 : Integrable (fun x => D.φ b x * D.e i x) D.μ := hφ.integrable_mul (D.he.memLp i)
    have i2 : Integrable (fun x => pair D.μ (D.φ b) * D.e i x) D.μ :=
      ((D.he.memLp i).integrable one_le_two).const_mul _
    have i3 : Integrable (fun x => (∑ k, α k * u k x) * D.e i x) D.μ :=
      (q08gl_memLp_comb D hu α).integrable_mul (D.he.memLp i)
    have : ∀ x, (D.φ b x - pair D.μ (D.φ b) - ∑ k, α k * u k x) * D.e i x =
        D.φ b x * D.e i x - pair D.μ (D.φ b) * D.e i x - (∑ k, α k * u k x) * D.e i x := by
      intro x; ring
    simp_rw [this]
    have i12 : Integrable (fun x => D.φ b x * D.e i x - pair D.μ (D.φ b) * D.e i x) D.μ := i1.sub i2
    have hc : ∫ x, D.e i x ∂D.μ = 0 := D.he.centered i
    rw [integral_sub i12 i3, integral_sub i1 i2, integral_const_mul, hc]
    have hco2 : ∫ x, (∑ k, α k * u k x) * D.e i x ∂D.μ = ∑ k, α k * q08gl_cf D u k i := by
      have hint : ∀ k, Integrable (fun x => α k * (u k x * D.e i x)) D.μ := fun k =>
        ((q08gl_memLp_u D hu k).integrable_mul (D.he.memLp i)).const_mul (α k)
      simp_rw [Finset.sum_mul]
      rw [integral_finsetSum _ fun k _ => by simpa [mul_assoc] using hint k]
      refine Finset.sum_congr rfl fun k _ => ?_
      unfold q08gl_cf
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun x => by ring)
    rw [hco2]
    unfold Q08Data.coef l2Inner
    simp
  simp_rw [hco] at hs hle
  exact (hs.sum_le_tsum _ fun _ _ => sq_nonneg _).trans (hle.trans hα)

end DCoef

end HRS.Q08

end
