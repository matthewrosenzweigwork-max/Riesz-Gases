import HRS.MS.R2ChaosAux2
import HRS.Prob.Gaussian

/-!
# HRS.MS.R2ChaosAux3 -- Gaussian toolkit for the Wick chaos of correlated Gaussian coordinates

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

For a jointly (centered) Gaussian family `z_1..z_n` whose covariance matrix `C` satisfies `αᵀCα ≤ Λ|α|²`, the centered
quadratic form `∑_{ij} A_ij (z_i z_j - E z_i z_j)` has second moment at most `2Λ²‖A‖_F²`.  Route: fourth moment of a
real centered Gaussian (`3σ⁴`), polarisation to `E X²Y² = EX² EY² + 2 (EXY)²`, spectral decomposition of the symmetric
matrix `A`, and `∑_l (E y_k y_l)² = ‖C v_k‖² ≤ Λ²`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

/-! ### Real Gaussian moments -/

theorem s94_gaussianReal_eq_map (v : ℝ≥0) :
    gaussianReal 0 v = (gaussianReal 0 1).map (fun x => Real.sqrt v * x) := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext
    simp [Real.sq_sqrt]

theorem s94_gaussian_integral_sq (v : ℝ≥0) : ∫ x, x ^ 2 ∂(gaussianReal 0 v) = v := by
  have h := variance_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral (by fun_prop)] at h
  simpa using h

theorem s94_gaussian_integral_pow4 (v : ℝ≥0) : ∫ x, x ^ 4 ∂(gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  rw [s94_gaussianReal_eq_map v, integral_map (by fun_prop) (by fun_prop)]
  have : ∀ x : ℝ, (Real.sqrt v * x) ^ 4 = (v : ℝ) ^ 2 * x ^ 4 := fun x => by
    have h : Real.sqrt (v : ℝ) ^ 2 = v := Real.sq_sqrt v.2
    calc (Real.sqrt v * x) ^ 4 = (Real.sqrt v ^ 2) ^ 2 * x ^ 4 := by ring
      _ = _ := by rw [h]
  simp_rw [this]
  rw [integral_const_mul, HRS.gauss_m4]
  ring

theorem s94_gaussian_integrable_pow (v : ℝ≥0) (n : ℕ) : Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 v) := by
  have := (memLp_id_gaussianReal (μ := 0) (v := v) n).integrable_norm_pow'
  rw [← integrable_norm_iff (by fun_prop)]
  simpa [norm_pow] using this

/-! ### Jointly Gaussian families -/

section Family

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Every real linear combination is a centered real Gaussian. -/
structure S94GFam {n : ℕ} (P : Measure Ω) (z : Fin n → Ω → ℝ) : Prop where
  meas : ∀ i, AEMeasurable (z i) P
  gauss : ∀ α : Fin n → ℝ, ∃ v : ℝ≥0, P.map (fun ζ => ∑ i, α i * z i ζ) = gaussianReal 0 v

/-- The linear combination `∑ α_i z_i`. -/
def s94lin {n : ℕ} (z : Fin n → Ω → ℝ) (α : Fin n → ℝ) (ζ : Ω) : ℝ := ∑ i, α i * z i ζ

variable {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} {z : Fin n → Ω → ℝ}

theorem S94GFam.meas_lin (hz : S94GFam P z) (α : Fin n → ℝ) : AEMeasurable (s94lin z α) P := by
  unfold s94lin
  exact Finset.aemeasurable_fun_sum _ fun i _ => (hz.meas i).const_mul _

theorem S94GFam.integrable_pow (hz : S94GFam P z) (α : Fin n → ℝ) (k : ℕ) :
    Integrable (fun ζ => s94lin z α ζ ^ k) P := by
  obtain ⟨v, hv⟩ := hz.gauss α
  have hv' : P.map (s94lin z α) = gaussianReal 0 v := hv
  have h := s94_gaussian_integrable_pow v k
  rw [← hv'] at h
  exact (integrable_map_measure (continuous_pow k).aestronglyMeasurable (hz.meas_lin α)).1 h

theorem S94GFam.integral_sq (hz : S94GFam P z) (α : Fin n → ℝ) :
    ∃ v : ℝ≥0, ∫ ζ, s94lin z α ζ ^ 2 ∂P = v ∧ ∫ ζ, s94lin z α ζ ^ 4 ∂P = 3 * (v : ℝ) ^ 2 := by
  obtain ⟨v, hv⟩ := hz.gauss α
  have hv' : P.map (s94lin z α) = gaussianReal 0 v := hv
  refine ⟨v, ?_, ?_⟩
  · have := s94_gaussian_integral_sq v
    rw [← hv', integral_map (hz.meas_lin α) (continuous_pow 2).aestronglyMeasurable] at this
    exact this
  · have := s94_gaussian_integral_pow4 v
    rw [← hv', integral_map (hz.meas_lin α) (continuous_pow 4).aestronglyMeasurable] at this
    exact this

/-- Variance form. -/
def s94q (P : Measure Ω) (z : Fin n → Ω → ℝ) (α : Fin n → ℝ) : ℝ := ∫ ζ, s94lin z α ζ ^ 2 ∂P

/-- Covariance bilinear form. -/
def s94b (P : Measure Ω) (z : Fin n → Ω → ℝ) (α β : Fin n → ℝ) : ℝ :=
  ∫ ζ, s94lin z α ζ * s94lin z β ζ ∂P

theorem S94GFam.four (hz : S94GFam P z) (α : Fin n → ℝ) :
    ∫ ζ, s94lin z α ζ ^ 4 ∂P = 3 * s94q P z α ^ 2 := by
  obtain ⟨v, h2, h4⟩ := hz.integral_sq α
  unfold s94q
  rw [h4, h2]

theorem s94lin_add (z : Fin n → Ω → ℝ) (α β : Fin n → ℝ) (ζ : Ω) :
    s94lin z (α + β) ζ = s94lin z α ζ + s94lin z β ζ := by
  unfold s94lin
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem s94lin_sub (z : Fin n → Ω → ℝ) (α β : Fin n → ℝ) (ζ : Ω) :
    s94lin z (α - β) ζ = s94lin z α ζ - s94lin z β ζ := by
  unfold s94lin
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem S94GFam.integrable_mul (hz : S94GFam P z) (α β : Fin n → ℝ) :
    Integrable (fun ζ => s94lin z α ζ * s94lin z β ζ) P := by
  have h1 := hz.integrable_pow α 2
  have h2 := hz.integrable_pow β 2
  refine Integrable.mono' ((h1.add h2).const_mul (1 / 2 : ℝ))
    ((hz.meas_lin α).mul (hz.meas_lin β)).aestronglyMeasurable (ae_of_all _ fun ζ => ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs]
  set x := s94lin z α ζ
  set y := s94lin z β ζ
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]

theorem S94GFam.integrable_sq_mul_sq (hz : S94GFam P z) (α β : Fin n → ℝ) :
    Integrable (fun ζ => s94lin z α ζ ^ 2 * s94lin z β ζ ^ 2) P := by
  have h1 := hz.integrable_pow α 4
  have h2 := hz.integrable_pow β 4
  refine Integrable.mono' ((h1.add h2).const_mul (1 / 2 : ℝ))
    (((hz.meas_lin α).pow_const 2).mul ((hz.meas_lin β).pow_const 2)).aestronglyMeasurable
    (ae_of_all _ fun ζ => ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs]
  set x := s94lin z α ζ
  set y := s94lin z β ζ
  rw [abs_of_nonneg (by positivity)]
  nlinarith [sq_nonneg (x ^ 2 - y ^ 2)]

theorem S94GFam.q_add (hz : S94GFam P z) (α β : Fin n → ℝ) :
    s94q P z (α + β) = s94q P z α + s94q P z β + 2 * s94b P z α β := by
  unfold s94q s94b
  have e : ∀ ζ, s94lin z (α + β) ζ ^ 2 =
      s94lin z α ζ ^ 2 + 2 * (s94lin z α ζ * s94lin z β ζ) + s94lin z β ζ ^ 2 := fun ζ => by
    rw [s94lin_add]; ring
  simp_rw [e]
  have i1 : Integrable (fun ζ => s94lin z α ζ ^ 2) P := hz.integrable_pow α 2
  have i2 : Integrable (fun ζ => 2 * (s94lin z α ζ * s94lin z β ζ)) P := (hz.integrable_mul α β).const_mul 2
  have i3 : Integrable (fun ζ => s94lin z β ζ ^ 2) P := hz.integrable_pow β 2
  have i12 : Integrable (fun ζ => s94lin z α ζ ^ 2 + 2 * (s94lin z α ζ * s94lin z β ζ)) P := i1.add i2
  rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul]
  ring

theorem S94GFam.q_sub (hz : S94GFam P z) (α β : Fin n → ℝ) :
    s94q P z (α - β) = s94q P z α + s94q P z β - 2 * s94b P z α β := by
  unfold s94q s94b
  have e : ∀ ζ, s94lin z (α - β) ζ ^ 2 =
      s94lin z α ζ ^ 2 - 2 * (s94lin z α ζ * s94lin z β ζ) + s94lin z β ζ ^ 2 := fun ζ => by
    rw [s94lin_sub]; ring
  simp_rw [e]
  have i1 : Integrable (fun ζ => s94lin z α ζ ^ 2) P := hz.integrable_pow α 2
  have i2 : Integrable (fun ζ => 2 * (s94lin z α ζ * s94lin z β ζ)) P := (hz.integrable_mul α β).const_mul 2
  have i3 : Integrable (fun ζ => s94lin z β ζ ^ 2) P := hz.integrable_pow β 2
  have i12 : Integrable (fun ζ => s94lin z α ζ ^ 2 - 2 * (s94lin z α ζ * s94lin z β ζ)) P := i1.sub i2
  rw [integral_add i12 i3, integral_sub i1 i2, integral_const_mul]
  ring

/-- Fourth-order polarisation (Isserlis for two variables). -/
theorem S94GFam.bivariate (hz : S94GFam P z) (α β : Fin n → ℝ) :
    ∫ ζ, s94lin z α ζ ^ 2 * s94lin z β ζ ^ 2 ∂P =
      s94q P z α * s94q P z β + 2 * s94b P z α β ^ 2 := by
  have hI := hz.integrable_sq_mul_sq α β
  have hA := hz.integrable_pow α 4
  have hB := hz.integrable_pow β 4
  have e : ∀ ζ, s94lin z (α + β) ζ ^ 4 + s94lin z (α - β) ζ ^ 4 =
      2 * s94lin z α ζ ^ 4 + 12 * (s94lin z α ζ ^ 2 * s94lin z β ζ ^ 2) + 2 * s94lin z β ζ ^ 4 :=
    fun ζ => by rw [s94lin_add, s94lin_sub]; ring
  have h1 : ∫ ζ, (s94lin z (α + β) ζ ^ 4 + s94lin z (α - β) ζ ^ 4) ∂P =
      3 * s94q P z (α + β) ^ 2 + 3 * s94q P z (α - β) ^ 2 := by
    rw [integral_add (hz.integrable_pow _ 4) (hz.integrable_pow _ 4), hz.four, hz.four]
  simp_rw [e] at h1
  have j1 : Integrable (fun ζ => 2 * s94lin z α ζ ^ 4) P := hA.const_mul 2
  have j2 : Integrable (fun ζ => 12 * (s94lin z α ζ ^ 2 * s94lin z β ζ ^ 2)) P := hI.const_mul 12
  have j3 : Integrable (fun ζ => 2 * s94lin z β ζ ^ 4) P := hB.const_mul 2
  have j12 : Integrable (fun ζ => 2 * s94lin z α ζ ^ 4 + 12 * (s94lin z α ζ ^ 2 * s94lin z β ζ ^ 2)) P :=
    j1.add j2
  rw [integral_add j12 j3, integral_add j1 j2, integral_const_mul, integral_const_mul,
    integral_const_mul, hz.four, hz.four, hz.q_add, hz.q_sub] at h1
  nlinarith [h1]

theorem s94lin_smul (z : Fin n → Ω → ℝ) (t : ℝ) (α : Fin n → ℝ) (ζ : Ω) :
    s94lin z (t • α) ζ = t * s94lin z α ζ := by
  unfold s94lin
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem S94GFam.q_smul (t : ℝ) (α : Fin n → ℝ) : s94q P z (t • α) = t ^ 2 * s94q P z α := by
  unfold s94q
  simp_rw [s94lin_smul, mul_pow]
  rw [integral_const_mul]

theorem S94GFam.b_smul (t : ℝ) (α β : Fin n → ℝ) : s94b P z α (t • β) = t * s94b P z α β := by
  unfold s94b
  simp_rw [s94lin_smul]
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun ζ => ?_)
  simp only
  ring

theorem S94GFam.q_nonneg (α : Fin n → ℝ) : 0 ≤ s94q P z α :=
  integral_nonneg fun ζ => sq_nonneg _

theorem S94GFam.cs (hz : S94GFam P z) (α β : Fin n → ℝ) :
    s94b P z α β ^ 2 ≤ s94q P z α * s94q P z β := by
  have h := discrim_le_zero (a := s94q P z β) (b := 2 * s94b P z α β) (c := s94q P z α) (fun t => by
    have h0 : 0 ≤ s94q P z (α + t • β) := S94GFam.q_nonneg _
    rw [hz.q_add, S94GFam.q_smul, S94GFam.b_smul] at h0
    nlinarith [h0])
  unfold discrim at h
  nlinarith [h]

/-- `s94b` expanded in the second argument along the coordinate vectors. -/
theorem S94GFam.b_expand (hz : S94GFam P z) (α β : Fin n → ℝ) :
    s94b P z α β = ∑ j, β j * ∫ ζ, s94lin z α ζ * z j ζ ∂P := by
  unfold s94b
  have e : ∀ ζ, s94lin z α ζ * s94lin z β ζ = ∑ j, β j * (s94lin z α ζ * z j ζ) := fun ζ => by
    unfold s94lin
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e]
  have hint : ∀ j, Integrable (fun ζ => s94lin z α ζ * z j ζ) P := fun j => by
    have := hz.integrable_mul α (Pi.single j 1)
    simpa [s94lin, Pi.single_apply] using this
  rw [integral_finset_sum _ fun j _ => (hint j).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]

theorem S94GFam.parseval_bound (hz : S94GFam P z) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ α : Fin n → ℝ, s94q P z α ≤ Λ * ∑ i, α i ^ 2)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (u : Fin n → ℝ) (hu : ∑ i, u i ^ 2 ≤ 1) :
    ∑ l, s94b P z u (⇑(b l)) ^ 2 ≤ Λ ^ 2 := by
  set w : Fin n → ℝ := fun j => ∫ ζ, s94lin z u ζ * z j ζ ∂P with hw
  have hb : ∀ l, s94b P z u (⇑(b l)) = inner ℝ (b l) (WithLp.toLp 2 w) := fun l => by
    rw [hz.b_expand, EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct, mul_comm, hw]
  have hpars : ∑ l, s94b P z u (⇑(b l)) ^ 2 = ∑ j, w j ^ 2 := by
    have := b.sum_sq_norm_inner_right (WithLp.toLp 2 w)
    simp_rw [hb]
    rw [EuclideanSpace.real_norm_sq_eq] at this
    simpa using this
  rw [hpars]
  set S : ℝ := ∑ j, w j ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hSb : S = s94b P z u w := by
    rw [hz.b_expand]
    simp [hS, hw, sq]
  have hcs := hz.cs u w
  rw [← hSb] at hcs
  have h1 : s94q P z u ≤ Λ := (hΛ u).trans (by nlinarith)
  have h2 : s94q P z w ≤ Λ * S := hΛ w
  have h3 : S ^ 2 ≤ Λ * (Λ * S) := by
    refine hcs.trans ?_
    exact mul_le_mul h1 h2 (S94GFam.q_nonneg _) hΛ0
  rcases hS0.eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · nlinarith [h3]

theorem S94GFam.integrable_cov4 (hz : S94GFam P z) (α β : Fin n → ℝ) :
    Integrable (fun ζ => (s94lin z α ζ ^ 2 - s94q P z α) * (s94lin z β ζ ^ 2 - s94q P z β)) P := by
  have e : ∀ ζ, (s94lin z α ζ ^ 2 - s94q P z α) * (s94lin z β ζ ^ 2 - s94q P z β) =
      s94lin z α ζ ^ 2 * s94lin z β ζ ^ 2 - s94q P z β * s94lin z α ζ ^ 2
        - s94q P z α * s94lin z β ζ ^ 2 + s94q P z α * s94q P z β := fun ζ => by ring
  simp_rw [e]
  exact (((hz.integrable_sq_mul_sq α β).sub ((hz.integrable_pow α 2).const_mul _)).sub
    ((hz.integrable_pow β 2).const_mul _)).add (integrable_const _)

theorem S94GFam.integral_cov4 (hz : S94GFam P z) (α β : Fin n → ℝ) :
    ∫ ζ, (s94lin z α ζ ^ 2 - s94q P z α) * (s94lin z β ζ ^ 2 - s94q P z β) ∂P =
      2 * s94b P z α β ^ 2 := by
  have e : ∀ ζ, (s94lin z α ζ ^ 2 - s94q P z α) * (s94lin z β ζ ^ 2 - s94q P z β) =
      s94lin z α ζ ^ 2 * s94lin z β ζ ^ 2 - s94q P z β * s94lin z α ζ ^ 2
        - s94q P z α * s94lin z β ζ ^ 2 + s94q P z α * s94q P z β := fun ζ => by ring
  simp_rw [e]
  have i1 := hz.integrable_sq_mul_sq α β
  have i2 : Integrable (fun ζ => s94q P z β * s94lin z α ζ ^ 2) P := (hz.integrable_pow α 2).const_mul _
  have i3 : Integrable (fun ζ => s94q P z α * s94lin z β ζ ^ 2) P := (hz.integrable_pow β 2).const_mul _
  have i12 : Integrable (fun ζ => s94lin z α ζ ^ 2 * s94lin z β ζ ^ 2 - s94q P z β * s94lin z α ζ ^ 2) P :=
    i1.sub i2
  have i123 : Integrable (fun ζ => s94lin z α ζ ^ 2 * s94lin z β ζ ^ 2 - s94q P z β * s94lin z α ζ ^ 2
      - s94q P z α * s94lin z β ζ ^ 2) P := i12.sub i3
  rw [integral_add i123 (integrable_const _), integral_sub i12 i3, integral_sub i1 i2, integral_const_mul,
    integral_const_mul, hz.bivariate]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  unfold s94q
  ring

theorem S94GFam.integrable_zz (hz : S94GFam P z) (i j : Fin n) :
    Integrable (fun ζ => z i ζ * z j ζ) P := by
  have := hz.integrable_mul (Pi.single i 1) (Pi.single j 1)
  simpa [s94lin, Pi.single_apply] using this

theorem s94_inner_basis (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (k : Fin n)
    (x : Fin n → ℝ) : inner ℝ (b k) (WithLp.toLp 2 x) = ∑ i, b k i * x i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, mul_comm]

theorem s94_basis_norm_sq (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (k : Fin n) :
    ∑ i, (b k i) ^ 2 = 1 := by
  have h := b.orthonormal.1 k
  have h2 := EuclideanSpace.real_norm_sq_eq (b k)
  rw [h] at h2
  simpa using h2.symm

/-- The key variance bound for a centered quadratic form in a jointly Gaussian family. -/
theorem S94GFam.quad_var (hz : S94GFam P z) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ α : Fin n → ℝ, s94q P z α ≤ Λ * ∑ i, α i ^ 2)
    (A : Fin n → Fin n → ℝ) (hAs : ∀ i j, A i j = A j i) :
    ∫ ζ, (∑ i, ∑ j, A i j * (z i ζ * z j ζ - ∫ ζ', z i ζ' * z j ζ' ∂P)) ^ 2 ∂P ≤
      2 * Λ ^ 2 * ∑ i, ∑ j, A i j ^ 2 := by
  have hA : (Matrix.of A).IsHermitian := Matrix.IsHermitian.ext fun i j => by simp [hAs i j]
  obtain ⟨b, l, hquad, -, hsq⟩ := HRS.quad_eig n (Matrix.of A) hA
  set y : Fin n → Ω → ℝ := fun k ζ => s94lin z (⇑(b k)) ζ with hy
  have hpt : ∀ ζ, ∑ i, ∑ j, A i j * (z i ζ * z j ζ) = ∑ k, l k * y k ζ ^ 2 := by
    intro ζ
    have h := hquad (fun i => z i ζ)
    simp only [s94_inner_basis] at h
    calc ∑ i, ∑ j, A i j * (z i ζ * z j ζ) =
          (fun i => z i ζ) ⬝ᵥ ((Matrix.of A).mulVec (fun i => z i ζ)) := by
          simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.of_apply]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = _ := h
      _ = _ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [hy, s94lin]
  have hc : ∑ i, ∑ j, A i j * ∫ ζ', z i ζ' * z j ζ' ∂P = ∑ k, l k * s94q P z (⇑(b k)) := by
    have h1 : ∑ i, ∑ j, A i j * ∫ ζ', z i ζ' * z j ζ' ∂P = ∫ ζ, ∑ i, ∑ j, A i j * (z i ζ * z j ζ) ∂P := by
      rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => (hz.integrable_zz i j).const_mul (A i j)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finset_sum _ fun j _ => (hz.integrable_zz i j).const_mul (A i j)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul]
    rw [h1]
    simp_rw [hpt]
    rw [integral_finset_sum _ fun k _ => (hz.integrable_pow (⇑(b k)) 2).const_mul _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]
    rfl
  have hW : ∀ ζ, ∑ i, ∑ j, A i j * (z i ζ * z j ζ - ∫ ζ', z i ζ' * z j ζ' ∂P) =
      ∑ k, l k * (s94lin z (⇑(b k)) ζ ^ 2 - s94q P z (⇑(b k))) := by
    intro ζ
    have e1 : ∑ i, ∑ j, A i j * (z i ζ * z j ζ - ∫ ζ', z i ζ' * z j ζ' ∂P) =
        ∑ i, ∑ j, A i j * (z i ζ * z j ζ) - ∑ i, ∑ j, A i j * ∫ ζ', z i ζ' * z j ζ' ∂P := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [e1, hpt, hc, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => by simp only [hy]; ring
  simp_rw [hW]
  set g : Fin n → Ω → ℝ := fun k ζ => s94lin z (⇑(b k)) ζ ^ 2 - s94q P z (⇑(b k)) with hg
  have hgi : ∀ k m, Integrable (fun ζ => (l k * g k ζ) * (l m * g m ζ)) P := fun k m => by
    have := (hz.integrable_cov4 (⇑(b k)) (⇑(b m))).const_mul (l k * l m)
    refine this.congr (ae_of_all _ fun ζ => ?_)
    simp only [hg]; ring
  have hexp : ∀ ζ, (∑ k, l k * g k ζ) ^ 2 = ∑ k, ∑ m, (l k * g k ζ) * (l m * g m ζ) := fun ζ => by
    rw [sq, Finset.sum_mul_sum]
  change ∫ ζ, (∑ k, l k * g k ζ) ^ 2 ∂P ≤ _
  simp_rw [hexp]
  rw [integral_finset_sum _ fun k _ => integrable_finset_sum _ fun m _ => hgi k m]
  have hkm : ∀ k m, ∫ ζ, (l k * g k ζ) * (l m * g m ζ) ∂P =
      l k * l m * (2 * s94b P z (⇑(b k)) (⇑(b m)) ^ 2) := fun k m => by
    have := hz.integral_cov4 (⇑(b k)) (⇑(b m))
    have e : ∀ ζ, (l k * g k ζ) * (l m * g m ζ) = (l k * l m) *
        ((s94lin z (⇑(b k)) ζ ^ 2 - s94q P z (⇑(b k))) * (s94lin z (⇑(b m)) ζ ^ 2 - s94q P z (⇑(b m)))) :=
      fun ζ => by simp only [hg]; ring
    simp_rw [e]
    rw [integral_const_mul, this]
  have hint2 : ∀ k, ∫ ζ, ∑ m, (l k * g k ζ) * (l m * g m ζ) ∂P =
      ∑ m, l k * l m * (2 * s94b P z (⇑(b k)) (⇑(b m)) ^ 2) := fun k => by
    rw [integral_finset_sum _ fun m _ => hgi k m]
    exact Finset.sum_congr rfl fun m _ => hkm k m
  simp_rw [hint2]
  set β : Fin n → Fin n → ℝ := fun k m => s94b P z (⇑(b k)) (⇑(b m)) ^ 2 with hβ
  have hβsymm : ∀ k m, β k m = β m k := fun k m => by
    simp only [hβ, s94b]
    simp_rw [mul_comm (s94lin z (⇑(b k)) _)]
  have hβ0 : ∀ k m, 0 ≤ β k m := fun k m => sq_nonneg _
  have hβsum : ∀ k, ∑ m, β k m ≤ Λ ^ 2 := fun k =>
    hz.parseval_bound hΛ0 hΛ b (⇑(b k)) (le_of_eq (s94_basis_norm_sq b k))
  have h2 : ∑ k, ∑ m, l k * l m * (2 * s94b P z (⇑(b k)) (⇑(b m)) ^ 2) ≤
      ∑ k, ∑ m, (l k ^ 2 + l m ^ 2) * β k m := by
    refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun m _ => ?_
    have := hβ0 k m
    simp only [hβ]
    nlinarith [sq_nonneg (l k - l m), sq_nonneg (s94b P z (⇑(b k)) (⇑(b m)))]
  have h3 : ∑ k, ∑ m, (l k ^ 2 + l m ^ 2) * β k m = 2 * ∑ k, l k ^ 2 * ∑ m, β k m := by
    simp_rw [add_mul, Finset.sum_add_distrib]
    have : ∑ k, ∑ m, l m ^ 2 * β k m = ∑ k, l k ^ 2 * ∑ m, β k m := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by rw [hβsymm]
    rw [this]
    simp_rw [← Finset.mul_sum]
    ring
  have h4 : ∑ k, l k ^ 2 * ∑ m, β k m ≤ ∑ k, l k ^ 2 * Λ ^ 2 :=
    Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hβsum k) (sq_nonneg _)
  calc _ ≤ _ := h2
    _ = _ := h3
    _ ≤ 2 * ∑ k, l k ^ 2 * Λ ^ 2 := by linarith
    _ = 2 * Λ ^ 2 * ∑ i, ∑ j, A i j ^ 2 := by
      have hsq' : ∑ k, l k ^ 2 = ∑ i, ∑ j, A i j ^ 2 := hsq
      rw [← hsq', ← Finset.sum_mul]
      ring

theorem S94GFam.bivariate_le (hz : S94GFam P z) (α β : Fin n → ℝ) :
    ∫ ζ, s94lin z α ζ ^ 2 * s94lin z β ζ ^ 2 ∂P ≤ 3 * (s94q P z α * s94q P z β) := by
  rw [hz.bivariate]
  have := hz.cs α β
  nlinarith [this]

end Family

end HRS.MS.R2Chaos
