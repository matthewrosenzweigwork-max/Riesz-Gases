import HRS.Main.A8PAux9

/-!
# Packet A8P, part 10: bilinear forms of `q × q` matrices on `ℝ^q`, trace norms, Gaussian laws
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

variable {q : ℕ}

/-- The bilinear form `(x,y) ↦ ∑_{ab} Q_{ab} x_a y_b` on `ℝ^q`. -/
def a8pForm (Q : Matrix (Fin q) (Fin q) ℝ) : (ℝ^q) →L[ℝ] (ℝ^q) →L[ℝ] ℝ :=
  ∑ a, ∑ b, Q a b • ((innerSL ℝ (EuclideanSpace.single a (1 : ℝ))).smulRight
    (innerSL ℝ (EuclideanSpace.single b (1 : ℝ))))

theorem a8pForm_apply (Q : Matrix (Fin q) (Fin q) ℝ) (x y : ℝ^q) :
    a8pForm Q x y = ∑ a, ∑ b, Q a b * (x a * y b) := by
  unfold a8pForm
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, EuclideanSpace.inner_single_left,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp

theorem a8pForm_sub (Q Q' : Matrix (Fin q) (Fin q) ℝ) : a8pForm (Q - Q') = a8pForm Q - a8pForm Q' := by
  ext x y
  simp only [sub_apply, a8pForm_apply, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem a8pForm_symm {Q : Matrix (Fin q) (Fin q) ℝ} (hQ : Q.transpose = Q) (x y : ℝ^q) :
    a8pForm Q x y = a8pForm Q y x := by
  rw [a8pForm_apply, a8pForm_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  have := congrFun (congrFun hQ a) b
  simp only [Matrix.transpose_apply] at this
  rw [this]; ring


theorem a8p_bessel_coord {n : ℕ} {e : Fin n → ℝ^q} (he : Orthonormal ℝ e) (a : Fin q) :
    ∑ i, (e i a) ^ 2 ≤ 1 := by
  have h := he.sum_inner_products_le (x := EuclideanSpace.single a (1 : ℝ)) (s := Finset.univ)
  simp only [EuclideanSpace.inner_single_right, EuclideanSpace.norm_single, norm_one, one_pow,
    Real.norm_eq_abs, sq_abs] at h
  simpa using h

theorem a8p_sum_abs_mul_le {n : ℕ} {e f : Fin n → ℝ^q} (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f)
    (a b : Fin q) : ∑ i, |e i a| * |f i b| ≤ 1 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n)) (fun i => |e i a|) (fun i => |f i b|)
  simp only [sq_abs] at h
  have h1 := a8p_bessel_coord he a
  have h2 := a8p_bessel_coord hf b
  have h3 : (∑ i, |e i a| * |f i b|) ^ 2 ≤ 1 := by
    calc _ ≤ (∑ i, (e i a) ^ 2) * ∑ i, (f i b) ^ 2 := h
      _ ≤ 1 * 1 := mul_le_mul h1 h2 (Finset.sum_nonneg fun i _ => sq_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have h4 : 0 ≤ ∑ i, |e i a| * |f i b| := Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  nlinarith

theorem a8p_traceNormForm_le (Q : Matrix (Fin q) (Fin q) ℝ) :
    traceNormForm (a8pForm Q) ≤ ∑ a, ∑ b, |Q a b| := by
  haveI : Nonempty (OrthonormalPairs (ℝ^q)) :=
    ⟨⟨⟨0, fun i => i.elim0, fun i => i.elim0⟩,
      ⟨fun i => i.elim0, fun i j _ => i.elim0⟩, ⟨fun i => i.elim0, fun i j _ => i.elim0⟩⟩⟩
  refine ciSup_le fun p => ?_
  obtain ⟨⟨n, e, f⟩, he, hf⟩ := p
  simp only
  have hterm : ∀ i : Fin n, |a8pForm Q (e i) (f i)| ≤ ∑ a, ∑ b, |Q a b| * (|e i a| * |f i b|) := by
    intro i
    rw [a8pForm_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [abs_mul, abs_mul]
  refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [← Finset.mul_sum]
  calc |Q a b| * ∑ i, |e i a| * |f i b| ≤ |Q a b| * 1 :=
        mul_le_mul_of_nonneg_left (a8p_sum_abs_mul_le he hf a b) (abs_nonneg _)
    _ = |Q a b| := mul_one _


theorem a8pForm_self_nonneg {Q : Matrix (Fin q) (Fin q) ℝ} (hQ : Q.PosSemidef) (x : ℝ^q) :
    0 ≤ a8pForm Q x x := by
  rw [a8pForm_apply]
  have h := (Matrix.posSemidef_iff_dotProduct_mulVec.1 hQ).2 (fun a => x a)
  simp only [star_trivial, dotProduct, Matrix.mulVec] at h
  have : ∑ a, ∑ b, Q a b * (x a * x b) = ∑ i, x i * ∑ j, Q i j * x j := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [this]
  exact h

theorem a8p_isTraceClass {Q : Matrix (Fin q) (Fin q) ℝ} (hQ : Q.PosSemidef) :
    IsTraceClassCov (a8pForm Q) := by
  have hT : Q.transpose = Q := by
    have := hQ.1.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  refine ⟨a8pForm_symm hT, a8pForm_self_nonneg hQ, ⟨Fin q, (EuclideanSpace.basisFun (Fin q) ℝ).toHilbertBasis,
    Summable.of_finite⟩⟩

theorem a8p_entry_meas {T : ℝ} {Sb : ℝ → Matrix (Fin q) (Fin q) ℝ} (hsb : IsDetCovMatrix T Sb)
    (a b : Fin q) : Measurable fun σ => Sb σ a b :=
  (measurable_pi_apply b).comp ((measurable_pi_apply a).comp hsb.meas)

theorem a8p_form_meas {T : ℝ} {Sb : ℝ → Matrix (Fin q) (Fin q) ℝ} (hsb : IsDetCovMatrix T Sb)
    (x y : ℝ^q) : Measurable fun σ => a8pForm (Sb σ) x y := by
  simp only [a8pForm_apply]
  exact Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ =>
    (a8p_entry_meas hsb a b).mul_const _

theorem a8p_isDetCovDensity {T : ℝ} {Sb : ℝ → Matrix (Fin q) (Fin q) ℝ} (hsb : IsDetCovMatrix T Sb) :
    IsDetCovDensity T (fun σ => a8pForm (Sb σ)) := by
  have hentI : ∀ a b, IntegrableOn (fun σ => Sb σ a b) (Set.Icc 0 T) := fun a b =>
    LindebergAux.sb_entry_integrableOn hsb.meas hsb.int hsb.psd a b
  refine ⟨fun x y => a8p_form_meas hsb x y, fun σ hσ => a8p_isTraceClass (hsb.psd σ hσ), ?_⟩
  have hm : Measurable fun σ => traceNormForm (a8pForm (Sb σ)) :=
    measurable_traceNormForm (H := ℝ^q) (fun σ => a8pForm (Sb σ)) (fun x y => a8p_form_meas hsb x y)
  have hbd : IntegrableOn (fun σ => ∑ a, ∑ b, |Sb σ a b|) (Set.Icc 0 T) :=
    integrable_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ => (hentI a b).abs
  refine Integrable.mono' hbd hm.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ _ => ?_)
  rw [Real.norm_of_nonneg (traceNormForm_nonneg _)]
  exact a8p_traceNormForm_le (Sb σ)

theorem a8p_gauss {T : ℝ} {Sb : ℝ → Matrix (Fin q) (Fin q) ℝ} (hsb : IsDetCovMatrix T Sb) :
    IsGaussianWithIntegratedCov T (fun σ => a8pForm (Sb σ)) (multivariateGaussian 0 (integratedCov T Sb)) := by
  have hentI : ∀ a b, IntegrableOn (fun σ => Sb σ a b) (Set.Icc 0 T) := fun a b =>
    LindebergAux.sb_entry_integrableOn hsb.meas hsb.int hsb.psd a b
  have hpsd := integratedCov_psd hsb
  refine ⟨inferInstance, ⟨inferInstance, fun L => ?_⟩, fun x y => ?_⟩
  · have h := ContinuousLinearMap.integral_comp_comm L
      (μ := multivariateGaussian (0 : ℝ^q) (integratedCov T Sb)) (φ := id) IsGaussian.integrable_id
    simpa using h
  · rw [covarianceBilin_multivariateGaussian hpsd]
    simp only [a8pForm_apply]
    rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ fun b _ => ((hentI a b).mul_const _))]
    simp only [dotProduct, Matrix.mulVec, integratedCov, Matrix.of_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finset_sum _ (fun b _ => ((hentI a b).mul_const _))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_mul_const]; ring

end HRS.Main.A8P
