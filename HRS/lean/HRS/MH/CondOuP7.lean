import HRS.ME.FamVC
import HRS.ME.RetPathLaw
import HRS.Main.HeadlineEquilibrium
import HRS.Sections.Q38bAux4
import HRS.MH.CondOuDefs

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

namespace HRS.MH.CondOuPackets

open HRS HRS.Main HRS.LZ

variable {d : ℕ}

/-- The pair covariance `v [[1,e],[e,1]]` is positive semidefinite for `0 < v`, `|e| ≤ 1`. -/
lemma p_cp7_posSemidef {v e : ℝ} (hv : 0 < v) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    (!![v, v * e; v * e, v] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 1), mul_nonneg hv.le (mul_nonneg (sub_nonneg.2 he1) (sq_nonneg (x 0 + x 1))),
      mul_nonneg hv.le (mul_nonneg he0 (sq_nonneg (x 0 + x 1))), mul_nonneg hv.le (mul_nonneg (sub_nonneg.2 he1) (sq_nonneg (x 0 - x 1))),
      mul_nonneg hv.le (mul_nonneg he0 (sq_nonneg (x 0 - x 1)))]


/-- The pair Gaussian is the linear image of two iid standard Gaussians. -/
lemma p_cp7_pair_law {v e : ℝ} (hv : 0 < v) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) !![v, v * e; v * e, v] =
      ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (fun p : ℝ × ℝ =>
        (WithLp.toLp 2 ![Real.sqrt v * p.1, e * Real.sqrt v * p.1 + Real.sqrt (v * (1 - e ^ 2)) * p.2] :
          EuclideanSpace ℝ (Fin 2))) := by
  have hS := p_cp7_posSemidef hv he0 he1
  have hmeas : Measurable (fun p : ℝ × ℝ =>
        (WithLp.toLp 2 ![Real.sqrt v * p.1, e * Real.sqrt v * p.1 + Real.sqrt (v * (1 - e ^ 2)) * p.2] :
          EuclideanSpace ℝ (Fin 2))) := by fun_prop
  have : IsProbabilityMeasure (((gaussianReal 0 1).prod (gaussianReal 0 1)).map (fun p : ℝ × ℝ =>
        (WithLp.toLp 2 ![Real.sqrt v * p.1, e * Real.sqrt v * p.1 + Real.sqrt (v * (1 - e ^ 2)) * p.2] :
          EuclideanSpace ℝ (Fin 2)))) := inferInstance
  refine Measure.ext_of_charFun ?_
  funext x
  rw [charFun_multivariateGaussian hS]
  unfold charFun
  rw [integral_map hmeas.aemeasurable (by fun_prop)]
  have hsv : Real.sqrt v * Real.sqrt v = v := Real.mul_self_sqrt hv.le
  have hc : Real.sqrt (v * (1 - e ^ 2)) * Real.sqrt (v * (1 - e ^ 2)) = v * (1 - e ^ 2) :=
    Real.mul_self_sqrt (mul_nonneg hv.le (by nlinarith))
  have h1 : ∀ p : ℝ × ℝ, Complex.exp (inner ℝ (WithLp.toLp 2 ![Real.sqrt v * p.1, e * Real.sqrt v * p.1 +
        Real.sqrt (v * (1 - e ^ 2)) * p.2] : EuclideanSpace ℝ (Fin 2)) x * Complex.I) =
      Complex.exp (((x 0 * Real.sqrt v + x 1 * (e * Real.sqrt v) : ℝ) * p.1 : ℝ) * Complex.I) *
      Complex.exp (((x 1 * Real.sqrt (v * (1 - e ^ 2)) : ℝ) * p.2 : ℝ) * Complex.I) := by
    intro p
    rw [← Complex.exp_add]
    congr 1
    simp [PiLp.inner_apply, Fin.sum_univ_two]
    push_cast
    ring
  simp_rw [h1]
  rw [integral_prod_mul (fun a : ℝ => Complex.exp (((x 0 * Real.sqrt v + x 1 * (e * Real.sqrt v) : ℝ) * a : ℝ) * Complex.I))
    (fun a : ℝ => Complex.exp (((x 1 * Real.sqrt (v * (1 - e ^ 2)) : ℝ) * a : ℝ) * Complex.I))]
  have h2 := fun u : ℝ => charFun_gaussianReal (μ := 0) (v := 1) u
  simp only [charFun_apply_real] at h2
  have h3 : ∀ u : ℝ, ∫ y : ℝ, Complex.exp (((u * y : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1 =
      Complex.exp (-((u : ℂ) ^ 2 / 2)) := by
    intro u
    have := h2 u
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub, NNReal.coe_one, Complex.ofReal_one,
      one_mul] at this
    simp only [Complex.ofReal_mul]
    rw [this]
  rw [h3, h3, ← Complex.exp_add]
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
  congr 1
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  push_cast
  have hs : (Real.sqrt v : ℂ) * Real.sqrt v = v := by exact_mod_cast hsv
  have hc' : (Real.sqrt (v * (1 - e ^ 2)) : ℂ) * Real.sqrt (v * (1 - e ^ 2)) = v * (1 - e ^ 2) := by exact_mod_cast hc
  linear_combination ((1:ℂ)/2) * (((x 0 : ℂ) + x 1 * e)^2 * hs + (x 1 : ℂ)^2 * hc')


/-- Symmetry of the standard Gaussian: `∫ F |a| = ∫ 2·1_{a>0} F a`. -/
lemma p_cp7_sym (F : ℝ → ℝ) (hF : Measurable F) (C : ℝ) (hC : ∀ a, |F a| ≤ C) :
    ∫ a, F |a| ∂(gaussianReal 0 1) =
      ∫ a, Set.indicator {a : ℝ | 0 < a} (fun a => 2 * F a) a ∂(gaussianReal 0 1) := by
  set μ : Measure ℝ := gaussianReal 0 1 with hμ
  set G : ℝ → ℝ := fun a => Set.indicator {a : ℝ | 0 < a} F a with hG
  have hGm : Measurable G := hF.indicator (measurableSet_lt measurable_const measurable_id)
  have hGb : ∀ a, |G a| ≤ C := by
    intro a; simp only [hG, Set.indicator]; split_ifs
    · exact hC a
    · simpa using (abs_nonneg (F a)).trans (hC a)
  have hGi : Integrable G μ := Integrable.of_bound hGm.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun a => by simpa [Real.norm_eq_abs] using hGb a)
  have hGni : Integrable (fun a => G (-a)) μ := Integrable.of_bound (hGm.comp measurable_neg).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun a => by simpa [Real.norm_eq_abs] using hGb (-a))
  have hneg : ∫ a, G (-a) ∂μ = ∫ a, G a ∂μ := by
    have h := integral_map (μ := μ) (φ := fun a : ℝ => -a) (f := G) measurable_neg.aemeasurable hGm.aestronglyMeasurable
    rw [hμ, gaussianReal_map_neg, neg_zero] at h
    exact h.symm
  have h0 : ∀ᵐ a ∂μ, a ∉ ({0} : Set ℝ) := by
    refine (measure_eq_zero_iff_ae_notMem).1 ?_
    exact gaussianReal_absolutelyContinuous 0 one_ne_zero (by simp)
  have hae : ∀ᵐ a ∂μ, F |a| = G a + G (-a) := by
    filter_upwards [h0] with a ha
    have ha' : a ≠ 0 := by simpa using ha
    rcases lt_or_gt_of_ne ha' with h | h
    · simp [hG, Set.indicator, abs_of_neg h, h, not_lt.2 h.le]
    · simp [hG, Set.indicator, abs_of_pos h, h, not_lt.2 h.le]
  rw [integral_congr_ae hae, integral_add hGi hGni, hneg]
  have : ∀ a, Set.indicator {a : ℝ | 0 < a} (fun a => 2 * F a) a = 2 * G a := by
    intro a; simp only [hG, Set.indicator]; split_ifs <;> simp
  simp_rw [this]
  rw [integral_const_mul]; ring


lemma p_cp7_integral_abs {v e : ℝ} (hv : 0 < v) (he0 : 0 ≤ e) (he1 : e ≤ 1) (f : ℝ →ᵇ ℝ) :
    ∫ x, Set.indicator {x : EuclideanSpace ℝ (Fin 2) | 0 < x 0} (fun x => 2 * f (x 1)) x
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) !![v, v * e; v * e, v]) =
      ∫ y, f y ∂(Measure.conv ((gaussianReal 0 1).map fun z : ℝ => e * Real.sqrt v * |z|)
        (gaussianLaw (v * (1 - e ^ 2)))) := by
  set μ : Measure ℝ := gaussianReal 0 1 with hμ
  set b : ℝ := e * Real.sqrt v with hb
  set c : ℝ := Real.sqrt (v * (1 - e ^ 2)) with hc
  have hv1 : 0 ≤ v * (1 - e ^ 2) := mul_nonneg hv.le (by nlinarith)
  set h : ℝ → ℝ := fun a => ∫ y, f (b * a + c * y) ∂μ with hh
  have hhm : Measurable h := by
    have : StronglyMeasurable (fun a => ∫ y, (fun q : ℝ × ℝ => f (b * q.1 + c * q.2)) (a, y) ∂μ) :=
      (f.continuous.comp (by fun_prop : Continuous fun q : ℝ × ℝ => b * q.1 + c * q.2)).stronglyMeasurable.integral_prod_right'
    exact this.measurable
  have hhb : ∀ a, |h a| ≤ ‖f‖ := by
    intro a
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun y => f (b * a + c * y)) (C := ‖f‖)
      (Filter.Eventually.of_forall fun y => f.norm_coe_le_norm _)
    simpa [Real.norm_eq_abs, hh] using this
  -- left side
  have hmeas : Measurable (fun p : ℝ × ℝ =>
        (WithLp.toLp 2 ![Real.sqrt v * p.1, e * Real.sqrt v * p.1 + Real.sqrt (v * (1 - e ^ 2)) * p.2] :
          EuclideanSpace ℝ (Fin 2))) := by fun_prop
  have hind : Measurable (fun x : EuclideanSpace ℝ (Fin 2) =>
      Set.indicator {x : EuclideanSpace ℝ (Fin 2) | 0 < x 0} (fun x => 2 * f (x 1)) x) :=
    Measurable.indicator (by fun_prop) (measurableSet_lt measurable_const (by fun_prop))
  rw [p_cp7_pair_law hv he0 he1, integral_map hmeas.aemeasurable hind.aestronglyMeasurable]
  have hpt : ∀ p : ℝ × ℝ, Set.indicator {x : EuclideanSpace ℝ (Fin 2) | 0 < x 0} (fun x => 2 * f (x 1))
      (WithLp.toLp 2 ![Real.sqrt v * p.1, e * Real.sqrt v * p.1 + Real.sqrt (v * (1 - e ^ 2)) * p.2] :
          EuclideanSpace ℝ (Fin 2)) =
      Set.indicator {q : ℝ × ℝ | 0 < q.1} (fun q => 2 * f (b * q.1 + c * q.2)) p := by
    intro p
    have : (0 < Real.sqrt v * p.1) ↔ 0 < p.1 := by
      constructor
      · intro h'; exact pos_of_mul_pos_right h' (Real.sqrt_pos.2 hv).le
      · intro h'; exact mul_pos (Real.sqrt_pos.2 hv) h'
    by_cases h' : 0 < p.1
    · have h'' := this.2 h'
      simp [Set.indicator, h', h'', hb, hc]
    · have h'' : ¬ 0 < Real.sqrt v * p.1 := fun x => h' (this.1 x)
      simp [Set.indicator, h', h'']
  simp_rw [hpt]
  have hint : Integrable (fun p : ℝ × ℝ =>
      Set.indicator {q : ℝ × ℝ | 0 < q.1} (fun q => 2 * f (b * q.1 + c * q.2)) p) (μ.prod μ) := by
    refine Integrable.of_bound (C := 2 * ‖f‖) ?_ ?_
    · exact (Measurable.indicator (by fun_prop) (measurableSet_lt measurable_const (by fun_prop))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun p => ?_
      simp only [Set.indicator]; split_ifs
      · rw [Real.norm_eq_abs, abs_mul]; simp only [abs_two]
        have := f.norm_coe_le_norm (b * p.1 + c * p.2)
        rw [Real.norm_eq_abs] at this
        linarith
      · simp
  rw [integral_prod _ hint]
  have hin : ∀ a : ℝ, ∫ y, Set.indicator {q : ℝ × ℝ | 0 < q.1} (fun q => 2 * f (b * q.1 + c * q.2)) (a, y) ∂μ =
      Set.indicator {a : ℝ | 0 < a} (fun a => 2 * h a) a := by
    intro a
    by_cases ha : 0 < a
    · simp only [Set.indicator, Set.mem_setOf_eq, ha, if_true]
      rw [integral_const_mul]
    · simp [Set.indicator, ha]
  simp_rw [hin]
  rw [← p_cp7_sym h hhm ‖f‖ hhb]
  -- right side
  have hν : gaussianLaw (v * (1 - e ^ 2)) = μ.map (fun z : ℝ => c * z) := by
    rw [hμ, gaussianReal_map_const_mul]
    unfold gaussianLaw
    congr 1
    · simp
    · apply NNReal.eq
      simp [Real.coe_toNNReal _ hv1, hc, Real.sq_sqrt hv1]
  have hγp : IsProbabilityMeasure (gaussianLaw (v * (1 - e ^ 2))) := by
    unfold gaussianLaw; infer_instance
  have hcp : IsProbabilityMeasure (Measure.conv ((gaussianReal 0 1).map fun z : ℝ => e * Real.sqrt v * |z|)
        (gaussianLaw (v * (1 - e ^ 2)))) := by
    unfold Measure.conv; infer_instance
  have hfi : Integrable f (Measure.conv ((gaussianReal 0 1).map fun z : ℝ => e * Real.sqrt v * |z|)
        (gaussianLaw (v * (1 - e ^ 2)))) := f.integrable _
  have hK : StronglyMeasurable (fun x : ℝ => ∫ y, f (x + y) ∂(gaussianLaw (v * (1 - e ^ 2)))) :=
    (f.continuous.comp (by fun_prop : Continuous fun q : ℝ × ℝ => q.1 + q.2)).stronglyMeasurable.integral_prod_right'
  rw [integral_conv hfi, integral_map (by fun_prop) hK.aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [hh]
  rw [hν, integral_map (by fun_prop) (by exact (f.continuous.comp (by fun_prop)).aestronglyMeasurable)]


lemma p_cp7_transientRate_nonneg (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : Lattice d) : 0 ≤ PDE.transientRate d s β k := by
  unfold PDE.transientRate
  have := q42_rieszCoeff_nonneg hd hs0 hsd k
  have : 0 ≤ β⁻¹ := (inv_pos.2 hβ).le
  positivity

lemma p_cp7_params (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : Lattice d) {t : ℝ} (ht : 0 ≤ t) :
    0 < (1 + β * rieszCoeff d s k)⁻¹ ∧ 0 ≤ Real.exp (-PDE.transientRate d s β k * t) ∧
      Real.exp (-PDE.transientRate d s β k * t) ≤ 1 := by
  refine ⟨inv_pos.2 (q42_one_add_pos hd hs0 hsd hβ k), (Real.exp_pos _).le, ?_⟩
  rw [Real.exp_le_one_iff]
  have := p_cp7_transientRate_nonneg hd hs0 hsd hβ k
  nlinarith [mul_nonneg this ht]

theorem condou_gauss_pair_integral (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : Lattice d) (t : ℝ) (ht : 0 ≤ t) (f : ℝ →ᵇ ℝ) :
    ∫ x, Set.indicator {x : EuclideanSpace ℝ (Fin 2) | 0 < x 0} (fun x => 2 * f (x 1)) x
        ∂(multivariateGaussian 0 (condouCov d s β k t)) =
      ∫ y, f y ∂(halfNormalMixtureLaw d s β k t) := by
  obtain ⟨hv, he0, he1⟩ := p_cp7_params hd hs0 hsd hβ k ht
  have key := p_cp7_integral_abs hv he0 he1 f
  have h2 : Real.exp (-2 * PDE.transientRate d s β k * t) = Real.exp (-PDE.transientRate d s β k * t) ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  unfold condouCov halfNormalMixtureLaw
  rw [h2]
  exact key

lemma p_cp7_nullset {v e : ℝ} (hv : 0 < v) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) !![v, v * e; v * e, v]
      {x : EuclideanSpace ℝ (Fin 2) | x 0 = 0} = 0 := by
  have hS := p_cp7_posSemidef hv he0 he1
  have hmp := measurePreserving_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin 2))) (i := 0) hS
  have h1 : {x : EuclideanSpace ℝ (Fin 2) | x 0 = 0} = (fun x : EuclideanSpace ℝ (Fin 2) => x 0) ⁻¹' {0} := rfl
  rw [h1, hmp.measure_preimage (measurableSet_singleton 0).nullMeasurableSet]
  have hne : ((!![v, v * e; v * e, v] : Matrix (Fin 2) (Fin 2) ℝ) 0 0).toNNReal ≠ 0 := by
    simpa using hv
  exact gaussianReal_absolutelyContinuous _ hne (by simp)

theorem condou_gauss_pair_nullset (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : Lattice d) (t : ℝ) (ht : 0 ≤ t) :
    multivariateGaussian 0 (condouCov d s β k t) {x : EuclideanSpace ℝ (Fin 2) | x 0 = 0} = 0 := by
  obtain ⟨hv, he0, he1⟩ := p_cp7_params hd hs0 hsd hβ k ht
  exact p_cp7_nullset hv he0 he1

end HRS.MH.CondOuPackets
