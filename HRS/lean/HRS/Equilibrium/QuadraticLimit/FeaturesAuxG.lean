import Mathlib

/-!
# Lemma 7.5: Gaussian tilt (auxiliary development for `q08_gauss_tilt`, prefix `q08g_`)

Density of the product Gaussian and linear change of variables.
-/

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Q08

/-- Density of the product of one-dimensional Gaussian-type densities. -/
theorem q08g_pi_withDensity {ι : Type*} [Fintype ι] (g : ℝ → ℝ) (hg : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) (hgi : Integrable g) :
    Measure.pi (fun _ : ι => (volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (g x))) =
      (volume : Measure (ι → ℝ)).withDensity (fun x => ENNReal.ofReal (∏ i, g (x i))) := by
  refine Measure.pi_eq (μ := fun _ : ι => (volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (g x))) fun s hs => ?_
  have hset : MeasurableSet (Set.pi Set.univ s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hset]
  have hind : ∀ x : ι → ℝ, (Set.pi Set.univ s).indicator (fun x => ENNReal.ofReal (∏ i, g (x i))) x =
      ENNReal.ofReal (∏ i, (s i).indicator g (x i)) := by
    intro x
    by_cases hx : x ∈ Set.pi Set.univ s
    · rw [Set.indicator_of_mem hx]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      have : ∃ i, x i ∉ s i := by
        by_contra hcon
        push Not at hcon
        exact hx fun i _ => hcon i
      obtain ⟨i, hi⟩ := this
      rw [ENNReal.ofReal_eq_zero.2 ?_]
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)]
  rw [← lintegral_indicator hset]
  simp_rw [hind]
  have hint : Integrable (fun x : ι → ℝ => ∏ i, (s i).indicator g (x i)) volume := by
    refine Integrable.fintype_prod (f := fun i x => (s i).indicator g x) fun i => ?_
    exact hgi.indicator (hs i)
  have hnn : 0 ≤ᵐ[volume] fun x : ι → ℝ => ∏ i, (s i).indicator g (x i) :=
    Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun i _ =>
      Set.indicator_nonneg (fun y _ => hg0 y) _
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_fintype_prod_volume_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg fun y => Set.indicator_nonneg (fun y _ => hg0 y) _)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), ← lintegral_indicator (hs i)]
  rw [ofReal_integral_eq_lintegral_ofReal (hgi.indicator (hs i))
    (Filter.Eventually.of_forall fun y => Set.indicator_nonneg (fun y _ => hg0 y) _)]
  refine lintegral_congr fun y => ?_
  by_cases hy : y ∈ s i <;> simp [hy]


section Alg

variable {L : ℕ}

theorem q08g_M_psd (A M : Matrix (Fin L) (Fin L) ℝ) (hA : A.PosSemidef) (β : ℝ) (hβ : 0 ≤ β)
    (hM : M * (1 + β • A) = 1) : M.PosSemidef := by
  have hS : (1 + β • A).PosSemidef := Matrix.PosSemidef.add Matrix.PosSemidef.one (hA.smul hβ)
  have := hS.inv
  rwa [Matrix.inv_eq_left_inv hM] at this

theorem q08g_alg (A M : Matrix (Fin L) (Fin L) ℝ) (hA : A.PosSemidef) (β : ℝ) (hβ : 0 ≤ β)
    (hM : M * (1 + β • A) = 1) :
    (CFC.sqrt M).det ≠ 0 ∧ (CFC.sqrt M)ᵀ = CFC.sqrt M ∧
      CFC.sqrt M * (1 + β • A) * CFC.sqrt M = 1 := by
  have hMp := q08g_M_psd A M hA β hβ hM
  set R := CFC.sqrt M with hR
  have hRR : R * R = M := CFC.sqrt_mul_sqrt_self M hMp.nonneg
  have hSM : (1 + β • A) * M = 1 := mul_eq_one_comm.1 hM
  refine ⟨?_, ?_, ?_⟩
  · have h1 : M.det * (1 + β • A).det = 1 := by rw [← Matrix.det_mul, hM, Matrix.det_one]
    have h2 : M.det ≠ 0 := left_ne_zero_of_mul_eq_one h1
    rw [← hRR, Matrix.det_mul] at h2
    exact left_ne_zero_of_mul h2
  · have : IsSelfAdjoint R := (CFC.sqrt_nonneg M).isSelfAdjoint
    have h := this.star_eq
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  · have h3 : ((1 + β • A) * R) * R = 1 := by rw [mul_assoc, hRR, hSM]
    have h4 : R * ((1 + β • A) * R) = 1 := mul_eq_one_comm.1 h3
    rw [← mul_assoc] at h4
    exact h4

end Alg


section Main

variable {L : ℕ}

/-- The density of the standard Gaussian in coordinates. -/
def q08g_phi (x : Fin L → ℝ) : ℝ := ∏ i, gaussianPDFReal 0 1 (x i)

theorem q08g_phi_pos (x : Fin L → ℝ) : 0 ≤ q08g_phi x :=
  Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 (x i)

theorem q08g_phi_eq (x : Fin L → ℝ) :
    q08g_phi x = ((Real.sqrt (2 * Real.pi)) ⁻¹) ^ L * Real.exp (-(x ⬝ᵥ x) / 2) := by
  unfold q08g_phi gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 2
  simp only [dotProduct, neg_div, Finset.sum_neg_distrib, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem q08g_stdGaussian_integral (G : EuclideanSpace ℝ (Fin L) → ℝ) (hG : Measurable G) :
    ∫ s, G s ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin L)) (1 : Matrix (Fin L) (Fin L) ℝ)) =
      ∫ x : Fin L → ℝ, q08g_phi x * G (toLp 2 x) := by
  rw [multivariateGaussian_zero_one, ← map_pi_eq_stdGaussian,
    integral_map (by fun_prop) hG.aestronglyMeasurable]
  have h1 : Measure.pi (fun _ : Fin L => gaussianReal 0 1) =
      (volume : Measure (Fin L → ℝ)).withDensity (fun x => ENNReal.ofReal (q08g_phi x)) := by
    unfold q08g_phi
    rw [← q08g_pi_withDensity (ι := Fin L) (gaussianPDFReal 0 1) (measurable_gaussianPDFReal 0 1)
      (gaussianPDFReal_nonneg 0 1) (integrable_gaussianPDFReal 0 1)]
    congr 1
    funext _
    exact gaussianReal_of_var_ne_zero 0 one_ne_zero
  rw [h1, integral_withDensity_eq_integral_toReal_smul]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [ENNReal.toReal_ofReal (q08g_phi_pos x)]
  · exact ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ =>
      (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i))
  · exact Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top


theorem q08g_gaussian_integral (M : Matrix (Fin L) (Fin L) ℝ) (f : EuclideanSpace ℝ (Fin L) → ℝ)
    (hf : Measurable f) :
    ∫ s, f s ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin L)) M) =
      ∫ x : Fin L → ℝ, q08g_phi x * f (toLp 2 ((CFC.sqrt M) *ᵥ x)) := by
  unfold multivariateGaussian
  rw [integral_map (by fun_prop) hf.aestronglyMeasurable, ← multivariateGaussian_zero_one,
    q08g_stdGaussian_integral]
  · simp
  · exact hf.comp (by fun_prop)

theorem q08g_quad_identity (A R : Matrix (Fin L) (Fin L) ℝ) (β : ℝ) (hRt : Rᵀ = R)
    (hR : R * (1 + β • A) * R = 1) (x : Fin L → ℝ) :
    (R *ᵥ x) ⬝ᵥ (R *ᵥ x) + β * ((R *ᵥ x) ⬝ᵥ (A *ᵥ (R *ᵥ x))) = x ⬝ᵥ x := by
  have h1 : (R *ᵥ x) ⬝ᵥ ((1 + β • A) *ᵥ (R *ᵥ x)) = x ⬝ᵥ x := by
    rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose R x,
      Matrix.vecMul_vecMul, hRt, ← mul_assoc, hR, Matrix.vecMul_one]
  have h2 : (R *ᵥ x) ⬝ᵥ ((1 + β • A) *ᵥ (R *ᵥ x)) =
      (R *ᵥ x) ⬝ᵥ (R *ᵥ x) + β * ((R *ᵥ x) ⬝ᵥ (A *ᵥ (R *ᵥ x))) := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul,
      smul_eq_mul]
  rw [← h2, h1]


theorem q08g_phi_meas : Measurable (q08g_phi (L := L)) :=
  Finset.measurable_prod _ fun i _ => (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i)

theorem q08g_change (A M : Matrix (Fin L) (Fin L) ℝ) (hA : A.PosSemidef) (β : ℝ) (hβ : 0 ≤ β)
    (hM : M * (1 + β • A) = 1) (f : EuclideanSpace ℝ (Fin L) → ℝ) (hf : Measurable f) :
    ∫ x : Fin L → ℝ, q08g_phi x * f (toLp 2 ((CFC.sqrt M) *ᵥ x)) =
      |(CFC.sqrt M).det|⁻¹ * ∫ u : Fin L → ℝ,
        q08g_phi u * (Real.exp (-(β / 2) * (u ⬝ᵥ A *ᵥ u)) * f (toLp 2 u)) := by
  obtain ⟨hdet, hRt, hR⟩ := q08g_alg A M hA β hβ hM
  set R := CFC.sqrt M with hRdef
  set H : (Fin L → ℝ) → ℝ := fun u => q08g_phi u * (Real.exp (-(β / 2) * (u ⬝ᵥ A *ᵥ u)) * f (toLp 2 u))
    with hH
  have hHm : Measurable H := by
    refine q08g_phi_meas.mul (Measurable.mul ?_ (hf.comp (by fun_prop)))
    refine Real.measurable_exp.comp (measurable_const.mul ?_)
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  have key : ∀ x : Fin L → ℝ, q08g_phi x * f (toLp 2 (R *ᵥ x)) = H (R *ᵥ x) := by
    intro x
    simp only [hH]
    have hq := q08g_quad_identity A R β hRt hR x
    have hex : Real.exp (-(x ⬝ᵥ x) / 2) = Real.exp (-((R *ᵥ x) ⬝ᵥ (R *ᵥ x)) / 2) *
        Real.exp (-(β / 2) * ((R *ᵥ x) ⬝ᵥ (A *ᵥ (R *ᵥ x)))) := by
      rw [← Real.exp_add]
      congr 1
      linarith [hq]
    rw [q08g_phi_eq, q08g_phi_eq, hex]
    ring
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi hdet
  calc ∫ x : Fin L → ℝ, q08g_phi x * f (toLp 2 (R *ᵥ x)) = ∫ x : Fin L → ℝ, H (Matrix.toLin' R x) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simpa [Matrix.toLin'_apply] using key x
    _ = ∫ u, H u ∂(Measure.map (Matrix.toLin' R) volume) := by
        rw [integral_map (by fun_prop) hHm.aestronglyMeasurable]
    _ = _ := by
        rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul, abs_inv]


theorem q08g_tilt_aux (A M : Matrix (Fin L) (Fin L) ℝ) (hA : A.PosSemidef) (β : ℝ) (hβ : 0 ≤ β)
    (hM : M * (1 + β • A) = 1) (f : EuclideanSpace ℝ (Fin L) → ℝ) (hf : Measurable f) :
    ∫ s, f s * Real.exp (-(β / 2) * ∑ i, ∑ j, A i j * s i * s j)
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin L)) (1 : Matrix (Fin L) (Fin L) ℝ)) =
      |(CFC.sqrt M).det| *
        ∫ s, f s ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin L)) M) := by
  obtain ⟨hdet, -, -⟩ := q08g_alg A M hA β hβ hM
  have hq : ∀ x : Fin L → ℝ, ∑ i, ∑ j, A i j * (toLp 2 x : EuclideanSpace ℝ (Fin L)) i *
      (toLp 2 x : EuclideanSpace ℝ (Fin L)) j = x ⬝ᵥ A *ᵥ x := by
    intro x
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [mul_comm, mul_left_comm]
  have hGm : Measurable (fun s : EuclideanSpace ℝ (Fin L) =>
      f s * Real.exp (-(β / 2) * ∑ i, ∑ j, A i j * s i * s j)) := by
    refine hf.mul (Real.measurable_exp.comp (measurable_const.mul ?_))
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    have h1 : Measurable (fun s : EuclideanSpace ℝ (Fin L) => s i) := by fun_prop
    have h2 : Measurable (fun s : EuclideanSpace ℝ (Fin L) => s j) := by fun_prop
    exact (measurable_const.mul h1).mul h2
  rw [q08g_stdGaussian_integral _ hGm, q08g_gaussian_integral M f hf]
  have h := q08g_change A M hA β hβ hM f hf
  have h' : ∫ u : Fin L → ℝ, q08g_phi u * (Real.exp (-(β / 2) * (u ⬝ᵥ A *ᵥ u)) * f (toLp 2 u)) =
      |(CFC.sqrt M).det| * ∫ x : Fin L → ℝ, q08g_phi x * f (toLp 2 ((CFC.sqrt M) *ᵥ x)) := by
    rw [h, ← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.2 hdet), one_mul]
  rw [← h']
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hq]
  ring

theorem q08g_tilt {L : ℕ} (A M : Matrix (Fin L) (Fin L) ℝ) (hA : A.PosSemidef) (β : ℝ)
    (hβ : 0 ≤ β) (hM : M * (1 + β • A) = 1) (f : EuclideanSpace ℝ (Fin L) → ℝ)
    (hf : Measurable f) :
    ∫ s, f s * Real.exp (-(β / 2) * ∑ i, ∑ j, A i j * s i * s j)
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin L)) (1 : Matrix (Fin L) (Fin L) ℝ)) =
      (∫ s, Real.exp (-(β / 2) * ∑ i, ∑ j, A i j * s i * s j)
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin L)) (1 : Matrix (Fin L) (Fin L) ℝ))) *
        ∫ s, f s ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin L)) M) := by
  have h1 := q08g_tilt_aux A M hA β hβ hM f hf
  have h0 := q08g_tilt_aux A M hA β hβ hM (fun _ => 1) measurable_const
  simp only [one_mul, integral_const, probReal_univ, smul_eq_mul, mul_one] at h0
  rw [h1, h0]

end Main

end HRS.Q08

end
