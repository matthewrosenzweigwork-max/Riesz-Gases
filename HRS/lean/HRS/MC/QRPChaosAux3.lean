import HRS.MC.QRPChaosAux2

/-!
# Packet CHAOS-LP (aux 3): the rotation `(x, y) ↦ ((x+y)/√2, (x-y)/√2)` of two independent copies of a
centred Gaussian vector.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.QRPChaos

variable {ι : Type} [Fintype ι]

/-- The rotated coordinates `(z.1 + ε z.2)/√2`. -/
def qpcRot (ε : ℝ) (z : (ι → ℝ) × (ι → ℝ)) : ι → ℝ := fun i =>
  (Real.sqrt 2)⁻¹ * (z.1 i + ε * z.2 i)

lemma qpc_sqrt2_sq : ((Real.sqrt 2)⁻¹) ^ 2 = (1 / 2 : ℝ) := by
  rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num

section

variable (ν : Measure (ι → ℝ)) [IsProbabilityMeasure ν] [IsGaussian ν]

lemma qpc_pair_gauss :
    HasGaussianLaw (fun z : (ι → ℝ) × (ι → ℝ) => (z.1, z.2)) (ν.prod ν) := by
  have h1 : HasGaussianLaw (fun z : (ι → ℝ) × (ι → ℝ) => z.1) (ν.prod ν) :=
    (HasLaw.hasGaussianLaw (μ := ν) ⟨measurable_fst.aemeasurable, measurePreserving_fst.map_eq⟩)
  have h2 : HasGaussianLaw (fun z : (ι → ℝ) × (ι → ℝ) => z.2) (ν.prod ν) :=
    (HasLaw.hasGaussianLaw (μ := ν) ⟨measurable_snd.aemeasurable, measurePreserving_snd.map_eq⟩)
  exact IndepFun.hasGaussianLaw h1 h2 (indepFun_prod (X := id) (Y := id) measurable_id measurable_id)

lemma qpc_gl_lin {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω'} {X : Ω' → ι → ℝ}
    (hX : HasGaussianLaw X P) (w : ι → ℝ) : HasGaussianLaw (fun ω => ∑ i, w i * X ω i) P := by
  have := hX.map_fun (∑ i, w i • (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ))
  simpa using this

lemma qpc_rot_gauss (ε : ℝ) : HasGaussianLaw (qpcRot ε) (ν.prod ν) := by
  have := (qpc_pair_gauss ν).map_fun ((Real.sqrt 2)⁻¹ •
    (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ) + ε • ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)))
  refine this.congr (Filter.Eventually.of_forall fun z => ?_)
  funext i; simp [qpcRot]; ring

lemma qpc_rot_pair_gauss :
    HasGaussianLaw (fun z : (ι → ℝ) × (ι → ℝ) => (qpcRot 1 z, qpcRot (-1) z)) (ν.prod ν) := by
  have := (qpc_pair_gauss ν).map_fun (
    ((Real.sqrt 2)⁻¹ • (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ) +
      (1 : ℝ) • ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))).prod
    ((Real.sqrt 2)⁻¹ • (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ) +
      (-1 : ℝ) • ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))))
  refine this.congr (Filter.Eventually.of_forall fun z => ?_)
  refine Prod.ext ?_ ?_ <;> (funext i; simp [qpcRot]; ring)

omit [IsGaussian ν] in
lemma qpc_int_fst (f : (ι → ℝ) → ℝ) : ∫ z, f z.1 ∂(ν.prod ν) = ∫ x, f x ∂ν := by
  have := integral_prod_mul (μ := ν) (ν := ν) f (fun _ => (1 : ℝ))
  simpa using this

omit [IsGaussian ν] in
lemma qpc_int_snd (f : (ι → ℝ) → ℝ) : ∫ z, f z.2 ∂(ν.prod ν) = ∫ x, f x ∂ν := by
  have := integral_prod_mul (μ := ν) (ν := ν) (fun _ => (1 : ℝ)) f
  simpa using this

omit [IsProbabilityMeasure ν] in
lemma qpc_coord_gauss (i : ι) : HasGaussianLaw (fun x : ι → ℝ => x i) ν :=
  (IsGaussian.hasGaussianLaw_id (μ := ν)).map_fun (ContinuousLinearMap.proj i)

lemma qpc_coord1_gauss (i : ι) :
    HasGaussianLaw (fun z : (ι → ℝ) × (ι → ℝ) => z.1 i) (ν.prod ν) :=
  (qpc_pair_gauss ν).fst.map_fun (ContinuousLinearMap.proj i)

lemma qpc_coord2_gauss (i : ι) :
    HasGaussianLaw (fun z : (ι → ℝ) × (ι → ℝ) => z.2 i) (ν.prod ν) :=
  (qpc_pair_gauss ν).snd.map_fun (ContinuousLinearMap.proj i)

lemma qpc_rot_coord_gauss (ε : ℝ) (i : ι) :
    HasGaussianLaw (fun z : (ι → ℝ) × (ι → ℝ) => qpcRot ε z i) (ν.prod ν) :=
  (qpc_rot_gauss ν ε).map_fun (ContinuousLinearMap.proj i)

lemma qpc_rot_mean (h0 : ∀ i, ∫ x, x i ∂ν = 0) (ε : ℝ) (i : ι) :
    ∫ z, qpcRot ε z i ∂(ν.prod ν) = 0 := by
  have e : (fun z : (ι → ℝ) × (ι → ℝ) => qpcRot ε z i) =
      fun z => (Real.sqrt 2)⁻¹ * (z.1 i + ε * z.2 i) := rfl
  rw [e, integral_const_mul, integral_add (qpc_coord1_gauss ν i).integrable
    ((qpc_coord2_gauss ν i).integrable.const_mul ε), integral_const_mul,
    qpc_int_fst ν (fun x => x i), qpc_int_snd ν (fun x => x i), h0]
  simp

lemma qpc_rot_second (h0 : ∀ i, ∫ x, x i ∂ν = 0) {ε : ℝ} (hε : ε ^ 2 = 1) (a : ι → ℝ) :
    ∫ z, (∑ i, a i * qpcRot ε z i) ^ 2 ∂(ν.prod ν) = ∫ x, (∑ i, a i * x i) ^ 2 ∂ν := by
  set Y1 : (ι → ℝ) × (ι → ℝ) → ℝ := fun z => ∑ i, a i * z.1 i with hY1
  set Y2 : (ι → ℝ) × (ι → ℝ) → ℝ := fun z => ∑ i, a i * z.2 i with hY2
  have hg1 : HasGaussianLaw Y1 (ν.prod ν) := qpc_gl_lin (X := fun z : (ι → ℝ) × (ι → ℝ) => z.1)
    (qpc_pair_gauss ν).fst a
  have hg2 : HasGaussianLaw Y2 (ν.prod ν) := qpc_gl_lin (X := fun z : (ι → ℝ) × (ι → ℝ) => z.2)
    (qpc_pair_gauss ν).snd a
  have hc := qpc_sqrt2_sq
  have key : ∀ z : (ι → ℝ) × (ι → ℝ), (∑ i, a i * qpcRot ε z i) ^ 2 =
      (1 / 2) * (Y1 z) ^ 2 + (1 / 2) * (Y2 z) ^ 2 + ε * (Y1 z * Y2 z) := by
    intro z
    have e : ∑ i, a i * qpcRot ε z i = (Real.sqrt 2)⁻¹ * (Y1 z + ε * Y2 z) := by
      simp only [qpcRot, hY1, hY2, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [e]
    linear_combination (Y1 z ^ 2 + ε ^ 2 * Y2 z ^ 2 + 2 * ε * Y1 z * Y2 z) * hc +
      (1 / 2 * Y2 z ^ 2) * hε
  simp_rw [key]
  have i1 : Integrable (fun z => (Y1 z) ^ 2) (ν.prod ν) := hg1.memLp_two.integrable_sq
  have i2 : Integrable (fun z => (Y2 z) ^ 2) (ν.prod ν) := hg2.memLp_two.integrable_sq
  have i3 : Integrable (fun z => Y1 z * Y2 z) (ν.prod ν) := hg1.memLp_two.integrable_mul hg2.memLp_two
  have hf : Integrable (fun z => 1 / 2 * Y1 z ^ 2 + 1 / 2 * Y2 z ^ 2) (ν.prod ν) :=
    (i1.const_mul _).add (i2.const_mul _)
  rw [integral_add hf (i3.const_mul ε), integral_add (i1.const_mul _) (i2.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul]
  have m1 : ∫ z, (Y1 z) ^ 2 ∂(ν.prod ν) = ∫ x, (∑ i, a i * x i) ^ 2 ∂ν :=
    qpc_int_fst ν (fun x => (∑ i, a i * x i) ^ 2)
  have m2 : ∫ z, (Y2 z) ^ 2 ∂(ν.prod ν) = ∫ x, (∑ i, a i * x i) ^ 2 ∂ν :=
    qpc_int_snd ν (fun x => (∑ i, a i * x i) ^ 2)
  have m3 : ∫ z, Y1 z * Y2 z ∂(ν.prod ν) = 0 := by
    have := integral_prod_mul (μ := ν) (ν := ν) (fun x => ∑ i, a i * x i)
      (fun x => ∑ i, a i * x i)
    have hz : ∫ x, (∑ i, a i * x i) ∂ν = 0 := by
      rw [integral_finset_sum _ (fun i _ => ((qpc_coord_gauss ν i).integrable).const_mul _)]
      simp [integral_const_mul, h0]
    rw [hz] at this
    simpa [hY1, hY2] using this
  rw [m1, m2, m3]
  ring

lemma qpc_rot_indep (h0 : ∀ i, ∫ x, x i ∂ν = 0) :
    IndepFun (qpcRot (ι := ι) 1) (qpcRot (ι := ι) (-1)) (ν.prod ν) := by
  refine HasGaussianLaw.indepFun_of_covariance_eval
    (X := fun i z => qpcRot (ι := ι) 1 z i) (Y := fun j z => qpcRot (ι := ι) (-1) z j)
    (qpc_rot_pair_gauss ν) fun i j => ?_
  have hX := (qpc_rot_coord_gauss ν 1 i)
  have hY := (qpc_rot_coord_gauss ν (-1) j)
  rw [covariance_eq_sub hX.memLp_two hY.memLp_two]
  have hmx := qpc_rot_mean ν h0 1 i
  have hmy := qpc_rot_mean ν h0 (-1) j
  simp only [Pi.mul_apply] at *
  rw [hmx, hmy, mul_zero, sub_zero]
  have key : ∀ z : (ι → ℝ) × (ι → ℝ), qpcRot (ι := ι) 1 z i * qpcRot (ι := ι) (-1) z j =
      (1 / 2) * (z.1 i * z.1 j - z.1 i * z.2 j + z.2 i * z.1 j - z.2 i * z.2 j) := by
    intro z
    have hc := qpc_sqrt2_sq
    simp only [qpcRot]
    linear_combination ((z.1 i + z.2 i) * (z.1 j - z.2 j)) * hc
  have a11 : Integrable (fun z : (ι → ℝ) × (ι → ℝ) => z.1 i * z.1 j) (ν.prod ν) :=
    (qpc_coord1_gauss ν i).memLp_two.integrable_mul (qpc_coord1_gauss ν j).memLp_two
  have a12 : Integrable (fun z : (ι → ℝ) × (ι → ℝ) => z.1 i * z.2 j) (ν.prod ν) :=
    (qpc_coord1_gauss ν i).memLp_two.integrable_mul (qpc_coord2_gauss ν j).memLp_two
  have a21 : Integrable (fun z : (ι → ℝ) × (ι → ℝ) => z.2 i * z.1 j) (ν.prod ν) :=
    (qpc_coord2_gauss ν i).memLp_two.integrable_mul (qpc_coord1_gauss ν j).memLp_two
  have a22 : Integrable (fun z : (ι → ℝ) × (ι → ℝ) => z.2 i * z.2 j) (ν.prod ν) :=
    (qpc_coord2_gauss ν i).memLp_two.integrable_mul (qpc_coord2_gauss ν j).memLp_two
  simp_rw [key]
  have b1 : Integrable (fun z : (ι → ℝ) × (ι → ℝ) => z.1 i * z.1 j - z.1 i * z.2 j) (ν.prod ν) :=
    a11.sub a12
  have b2 : Integrable (fun z : (ι → ℝ) × (ι → ℝ) =>
      z.1 i * z.1 j - z.1 i * z.2 j + z.2 i * z.1 j) (ν.prod ν) := b1.add a21
  rw [integral_const_mul, integral_sub b2 a22, integral_add b1 a21, integral_sub a11 a12]
  have c11 := qpc_int_fst ν (fun x => x i * x j)
  have c22 := qpc_int_snd ν (fun x => x i * x j)
  have c12 : ∫ z : (ι → ℝ) × (ι → ℝ), z.1 i * z.2 j ∂(ν.prod ν) = 0 := by
    have := integral_prod_mul (μ := ν) (ν := ν) (fun x : ι → ℝ => x i) (fun x => x j)
    rw [h0 i, h0 j, zero_mul] at this
    exact this
  have c21 : ∫ z : (ι → ℝ) × (ι → ℝ), z.2 i * z.1 j ∂(ν.prod ν) = 0 := by
    have := integral_prod_mul (μ := ν) (ν := ν) (fun x : ι → ℝ => x j) (fun x => x i)
    rw [h0 i, h0 j, zero_mul] at this
    simpa [mul_comm] using this
  rw [c11, c22, c12, c21]
  ring

end

end HRS.MC.QRPChaos
