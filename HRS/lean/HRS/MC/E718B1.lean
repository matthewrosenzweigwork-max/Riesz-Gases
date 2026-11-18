import HRS.Prob.Gaussian

/-!
# Row 7.18 (packet e718b), file 1: second moments and a.e. linearity of an isonormal process

`IsIsonormal` is restated verbatim (the frozen definition lives in the frozen-statement file
`HRS.Prob.GaussianIso`, which proof modules must not import).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.E718B

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {Ω : Type*} [MeasurableSpace Ω]

/-- Verbatim copy of `HRS.IsIsonormal`. -/
def IsIsonormal (P : Measure Ω) (W : H → Ω → ℝ) : Prop :=
  ∀ (n : ℕ) (h : Fin n → H),
    HRS.law P (fun ω => (WithLp.toLp 2 fun i : Fin n => W (h i) ω : EuclideanSpace ℝ (Fin n))) =
      multivariateGaussian 0 (Matrix.of fun i j : Fin n => inner ℝ (h i) (h j))

variable {P : Measure Ω} [IsProbabilityMeasure P] {W : H → Ω → ℝ}

lemma gram_psd {n : ℕ} (h : Fin n → H) :
    (Matrix.of fun i j : Fin n => inner ℝ (h i) (h j)).PosSemidef :=
  Matrix.posSemidef_gram ℝ h

lemma IsIsonormal.aemeasurable_vec (hW : IsIsonormal P W) {n : ℕ} (h : Fin n → H) (hne : ∃ i, h i ≠ 0) :
    AEMeasurable (fun ω => (WithLp.toLp 2 fun i : Fin n => W (h i) ω : EuclideanSpace ℝ (Fin n))) P := by
  by_contra hc
  obtain ⟨i, hi⟩ := hne
  have h0 := hW n h
  unfold HRS.law at h0
  rw [Measure.map_of_not_aemeasurable_of_ne_zero hc (IsProbabilityMeasure.ne_zero P)] at h0
  have hv := variance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin n)))
    (gram_psd h) (i := i)
  rw [← h0, variance_dirac] at hv
  have : 0 < inner ℝ (h i) (h i) := real_inner_self_pos.2 hi
  simp at hv
  have := norm_pos_iff.2 hi
  nlinarith

/-- Second moment of a finite linear combination of values of the process. -/
lemma IsIsonormal.comb_moment (hW : IsIsonormal P W) {n : ℕ} (h : Fin n → H) (hne : ∃ i, h i ≠ 0)
    (c : Fin n → ℝ) :
    MemLp (fun ω => ∑ i, c i * W (h i) ω) 2 P ∧
      ∫ ω, (∑ i, c i * W (h i) ω) ^ 2 ∂P = ‖∑ i, c i • h i‖ ^ 2 := by
  set X : Ω → EuclideanSpace ℝ (Fin n) :=
    fun ω => (WithLp.toLp 2 fun i : Fin n => W (h i) ω : EuclideanSpace ℝ (Fin n)) with hX
  have hXm : AEMeasurable X P := hW.aemeasurable_vec h hne
  have hlaw : P.map X = multivariateGaussian 0 (Matrix.of fun i j : Fin n => inner ℝ (h i) (h j)) :=
    hW n h
  set γ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
    (Matrix.of fun i j : Fin n => inner ℝ (h i) (h j)) with hγ
  set c' : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 c with hc'
  have hcomb : (fun ω => ∑ i, c i * W (h i) ω) = (fun z : EuclideanSpace ℝ (Fin n) => inner ℝ c' z) ∘ X := by
    ext ω
    simp [hX, hc', PiLp.inner_apply, mul_comm]
  have hL : MemLp (fun z : EuclideanSpace ℝ (Fin n) => inner ℝ c' z) 2 γ :=
    IsGaussian.memLp_dual γ (innerSL ℝ c') 2 (by simp)
  constructor
  · rw [hcomb]
    rw [← hlaw] at hL
    exact (memLp_map_measure_iff hL.aestronglyMeasurable hXm).1 hL
  · have e1 : ∫ ω, (∑ i, c i * W (h i) ω) ^ 2 ∂P = ∫ z, (inner ℝ c' z) ^ 2 ∂γ := by
      rw [← hlaw, integral_map hXm (by fun_prop)]
      congr 1; ext ω
      have := congrFun hcomb ω
      simp only [Function.comp] at this
      rw [this]
    have hmem : MemLp id 2 γ := IsGaussian.memLp_two_id
    have e2 := covarianceBilin_apply hmem c' c'
    have hm : γ[id] = 0 := integral_id_multivariateGaussian
    rw [hm] at e2
    have e3 := covarianceBilin_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin n)))
      (gram_psd h) c' c'
    rw [← hγ] at e3
    simp only [sub_zero] at e2
    have e4 : ∫ z, (inner ℝ c' z) ^ 2 ∂γ = c'.ofLp ⬝ᵥ (Matrix.of fun i j : Fin n => inner ℝ (h i) (h j)).mulVec c'.ofLp := by
      rw [← e3, e2]; simp_rw [pow_two]
    rw [e1, e4]
    rw [← real_inner_self_eq_norm_sq]
    simp only [hc', sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, dotProduct,
      Matrix.mulVec, Matrix.of_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_comm (h i) (h j)]
    ring

/-- A.e. linearity of the process on a finite linear combination (of nonzero vectors). -/
lemma IsIsonormal.comb_ae (hW : IsIsonormal P W) {n : ℕ} (u : Fin n → H) (lam : Fin n → ℝ) (x : H)
    (hx : x = ∑ i, lam i • u i) (hx0 : x ≠ 0) :
    W x =ᵐ[P] fun ω => ∑ i, lam i * W (u i) ω := by
  set h : Fin (n + 1) → H := Fin.cons x u with hh
  set c : Fin (n + 1) → ℝ := Fin.cons 1 (fun i => - lam i) with hc
  obtain ⟨hmem, hint⟩ := hW.comb_moment h ⟨0, by simpa [hh] using hx0⟩ c
  have e1 : (fun ω => ∑ i, c i * W (h i) ω) = fun ω => W x ω - ∑ i, lam i * W (u i) ω := by
    ext ω
    simp [hh, hc, Fin.sum_univ_succ, Finset.sum_neg_distrib, neg_mul, sub_eq_add_neg]
  have e2 : ∑ i, c i • h i = 0 := by
    simp [hh, hc, Fin.sum_univ_succ, Finset.sum_neg_distrib, neg_smul, ← hx]
  rw [e1] at hmem
  have e1' := congrFun e1
  simp only [e1'] at hint
  rw [e2] at hint
  have hz : ∫ ω, (W x ω - ∑ i, lam i * W (u i) ω) ^ 2 ∂P = 0 := by simpa using hint
  have := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hmem.integrable_sq).1 hz
  filter_upwards [this] with ω hω
  have : W x ω - ∑ i, lam i * W (u i) ω = 0 := by simpa using hω
  linarith

end

end HRS.MC.E718B
