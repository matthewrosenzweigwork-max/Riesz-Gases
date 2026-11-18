import HRS.Commutator.Torus.TLOWVAux3

/-!
# T-LOWV helpers, part 4: densities, the low-frequency part `a = P_{≤4}σ`, comparison of the pairing with a
density and with the iterated integral
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s : ℝ}

/-- `tenSint` against a density. -/
theorem tlowv_tenSint_ofDensity (a : Torus d → ℝ) (g : Torus d → ℂ) (ha : Measurable a)
    (hag : Integrable (fun x => ((a x : ℝ) : ℂ) * g x)) :
    tenSint (SMT.ofDensity a) g = ∫ x, ((a x : ℝ) : ℂ) * g x := by
  have hm1 : Measurable fun x => ENNReal.ofReal (a x) := ha.ennreal_ofReal
  have hm2 : Measurable fun x => ENNReal.ofReal (-a x) := ha.neg.ennreal_ofReal
  have ht1 : ∀ᵐ x ∂(volume : Measure (Torus d)), ENNReal.ofReal (a x) < ⊤ :=
    ae_of_all _ fun x => ENNReal.ofReal_lt_top
  have ht2 : ∀ᵐ x ∂(volume : Measure (Torus d)), ENNReal.ofReal (-a x) < ⊤ :=
    ae_of_all _ fun x => ENNReal.ofReal_lt_top
  have hI1 : Integrable (fun x => (ENNReal.ofReal (a x)).toReal • g x) := by
    have : (fun x => (ENNReal.ofReal (a x)).toReal • g x) =
        {x | 0 < a x}.indicator (fun x => ((a x : ℝ) : ℂ) * g x) := by
      funext x
      by_cases h : 0 < a x
      · rw [Set.indicator_of_mem (show x ∈ {x | 0 < a x} from h), ENNReal.toReal_ofReal',
          max_eq_left h.le, Complex.real_smul]
      · rw [Set.indicator_of_notMem (show x ∉ {x | 0 < a x} from h), ENNReal.toReal_ofReal',
          max_eq_right (not_lt.1 h), zero_smul]
    rw [this]
    exact hag.indicator (measurableSet_lt measurable_const ha)
  have hI2 : Integrable (fun x => (ENNReal.ofReal (-a x)).toReal • g x) := by
    have : (fun x => (ENNReal.ofReal (-a x)).toReal • g x) =
        {x | a x < 0}.indicator (fun x => -(((a x : ℝ) : ℂ) * g x)) := by
      funext x
      by_cases h : a x < 0
      · rw [Set.indicator_of_mem (show x ∈ {x | a x < 0} from h), ENNReal.toReal_ofReal',
          max_eq_left (by linarith), Complex.real_smul]
        push_cast; ring
      · rw [Set.indicator_of_notMem (show x ∉ {x | a x < 0} from h), ENNReal.toReal_ofReal',
          max_eq_right (by linarith [not_lt.1 h]), zero_smul]
    rw [this]
    exact (hag.neg).indicator (measurableSet_lt ha measurable_const)
  unfold tenSint SMT.ofDensity
  rw [integral_withDensity_eq_integral_toReal_smul hm1 ht1 g,
    integral_withDensity_eq_integral_toReal_smul hm2 ht2 g, ← integral_sub hI1 hI2]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [ENNReal.toReal_ofReal', Complex.real_smul]
  rw [← sub_mul]
  congr 1
  rw [← Complex.ofReal_sub, max_zero_sub_max_neg_zero_eq_self]

lemma tlowv_ofDensity_finite (a : Torus d → ℝ) (ha : Measurable a) {B : ℝ} (hB : ∀ x, |a x| ≤ B) :
    (SMT.ofDensity a).IsFinite := by
  have hint : Integrable a := ten_integrable_of_bdd (μ := volume) ha B (fun x => by
    rw [Real.norm_eq_abs]; exact hB x)
  refine ⟨?_, ?_⟩
  · exact isFiniteMeasure_withDensity_ofReal hint.2
  · exact isFiniteMeasure_withDensity_ofReal hint.neg.2

lemma tlowv_ofDensity_coef (a : Torus d → ℝ) (ha : Measurable a) {B : ℝ} (hB : ∀ x, |a x| ≤ B)
    (j : Lattice d) : (SMT.ofDensity a).coef j = Torus.fcoef a j := by
  have hint : Integrable (fun x => ((a x : ℝ) : ℂ) * Torus.mode (-j) x) := by
    refine Integrable.of_bound ?_ B (ae_of_all _ fun x => ?_)
    · exact (Complex.continuous_ofReal.measurable.comp ha).aestronglyMeasurable.mul
        (Torus.continuous_mode _).aestronglyMeasurable
    · rw [norm_mul, Torus.norm_mode, mul_one, Complex.norm_real, Real.norm_eq_abs]; exact hB x
  have := tlowv_tenSint_ofDensity a (fun x => Torus.mode (-j) x) ha hint
  unfold tenSint at this
  unfold SMT.coef
  rw [this]
  unfold Torus.fcoef
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  ring

lemma tlowv_coef_zero (σ : SMT d) : σ.coef 0 = ((σ.mass : ℝ) : ℂ) := by
  unfold SMT.coef SMT.mass SMT.int
  simp only [neg_zero, Torus.mode_zero, integral_const, smul_eq_mul]
  push_cast
  simp [integral_complex_ofReal]

/-- The low-frequency density `a = P_{≤4}σ` at scale `η`: a smooth real trigonometric polynomial with
coefficients `χ(ηk/4) σ̂(k)`. -/
lemma tlowv_density (σ : SMT d) (hσ : σ.IsFinite) {η : ℝ} (hη : 0 < η) :
    ∃ a : Torus d → ℝ, Continuous a ∧ Torus.IsSmooth a ∧
      (∀ k, Torus.fcoef a k = ((tkrChi (η / 4) k : ℝ) : ℂ) * σ.coef k) := by
  have hη4 : 0 < η / 4 := by positivity
  set c : Lattice d → ℂ := fun k => ((tkrChi (η / 4) k : ℝ) : ℂ) * σ.coef k with hc
  have hT : HRS.PDE.IsTrigPoly ⌈2 / (η / 4)⌉₊ c :=
    tkr_isTrigPoly hη4 (fun k hk => by
      intro h0; apply hk; simp [hc, h0])
  have hr : HRS.PDE.IsRealCoeff c := by
    intro k
    simp only [hc]
    rw [ten_coef_neg, map_mul, Complex.conj_ofReal]
    congr 2
    unfold tkrChi
    rw [ten_toEuc_neg, smul_neg, Whole.cmxFB_chi_neg]
  obtain ⟨a, ha, -, hco⟩ := tsamp_real_trig hr hT
  refine ⟨a, ha, ?_, hco⟩
  refine tprod_smooth_of_box ha ⌈2 / (η / 4)⌉₊ (fun k hk => ?_)
  rw [hco]
  by_contra hne
  exact hk (hT k hne)

/-- Comparison of the pairing with a density and the iterated integral, for bounded continuous kernels. -/
theorem tlowv_pair2_density {F : Torus d → Euc d} (hFc : Continuous F) {v : Torus d → Euc d}
    {L : ℝ} (hL : 0 ≤ L) (hv : IsLipschitzVF L v) (hvc : Continuous v) {a : Torus d → ℝ}
    (hac : Continuous a) :
    CcommT F v (SMT.ofDensity a) = CcommFunT F v a := by
  obtain ⟨BF, hBF⟩ := ten_bound_of_continuous (continuous_norm.comp hFc)
  obtain ⟨Ba, hBa⟩ := ten_bound_of_continuous hac
  have ham : Measurable a := hac.measurable
  have hKm := tlowv_commKernel_meas hFc.measurable hvc
  have hBF' : ∀ z, ‖F z‖ ≤ BF := fun z => by simpa using hBF z
  have hκb : ∀ x y, |commKernel F v x y| ≤ L * (d * BF) := by
    intro x y
    refine (tlowv_commKernel_abs hL hv F x y).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hL
    unfold tlowvW
    exact mul_le_mul (KernelGrad.tdist_le_card _) (hBF' _) (norm_nonneg _) (Nat.cast_nonneg d)
  have hBa' : ∀ x, |a x| ≤ Ba := fun x => by simpa using hBa x
  have hκx : ∀ x : Torus d, Measurable fun y => commKernel F v x y := fun x =>
    hKm.comp (measurable_prodMk_left)
  have hinner : ∀ x : Torus d, (SMT.ofDensity a).int (fun y => commKernel F v x y) =
      ∫ y, a y * commKernel F v x y := by
    intro x
    refine ten_int_ofDensity a _ ham ?_
    exact ten_integrable_of_bdd (μ := volume) (ham.mul (hκx x)) (Ba * (L * (d * BF))) (fun y => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hBa' y) (hκb x y) (abs_nonneg _) ((abs_nonneg _).trans (hBa' y)))
  unfold CcommT SMT.pair2
  simp_rw [hinner]
  have hsm : StronglyMeasurable (fun p : Torus d × Torus d => a p.2 * commKernel F v p.1 p.2) :=
    ((ham.comp measurable_snd).mul hKm).stronglyMeasurable
  have hgm : Measurable fun x : Torus d => ∫ y, a y * commKernel F v x y :=
    (hsm.integral_prod_right' (ν := volume)).measurable
  rw [ten_int_ofDensity a _ ham]
  · unfold CcommFunT
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show a x * ∫ y, a y * commKernel F v x y = ∫ y, commKernel F v x y * a x * a y
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    ring
  · refine ten_integrable_of_bdd (μ := volume) (ham.mul hgm) (Ba * (Ba * (L * (d * BF)))) (fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul (hBa' x) ?_ (abs_nonneg _) ((abs_nonneg _).trans (hBa' x))
    have h1 : ‖∫ y, a y * commKernel F v x y‖ ≤ Ba * (L * (d * BF)) * volume.real Set.univ :=
      norm_integral_le_of_norm_le_const (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hBa' y) (hκb x y) (abs_nonneg _) ((abs_nonneg _).trans (hBa' y)))
    simpa using h1

end HRS.Commutator.TorusNote
