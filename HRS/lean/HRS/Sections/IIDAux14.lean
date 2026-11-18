import HRS.Sections.IIDAux13

/-!
# IID helper chain, part 14: mixture bookkeeping (clipping of `b`, the shift identity, convexity and
translation for `smoothDist`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.IID

section Book

open HRS.InitialDataAux

variable {d : ℕ} {m : ℝ}

lemma withDensityReal_congr {f g : Torus d → ℝ} (h : f =ᵐ[volume] g) :
    withDensityReal f = withDensityReal g := by
  unfold withDensityReal
  refine withDensity_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

lemma ofFun_congr {f g : Torus d → ℝ} (h : f =ᵐ[volume] g) :
    NegSobolev.ofFun m f = NegSobolev.ofFun m g := by
  have : Torus.funRealCoeff f = Torus.funRealCoeff g := by
    funext k
    unfold Torus.funRealCoeff
    refine integral_congr_ae ?_
    filter_upwards [h] with x hx
    rw [hx]
  unfold NegSobolev.ofFun
  rw [this]

lemma memℓp_funRealCoeff (hm : (d : ℝ) < 2 * m) {f : Torus d → ℝ} (hf : Integrable f) :
    Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * Torus.funRealCoeff f k) 2 := by
  refine NegSobolev.memℓp_of_bounded hm _ ⟨Real.sqrt 2 * ∫ x, |f x|, fun k => ?_⟩
  unfold Torus.funRealCoeff
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ x, |Torus.realMode k x * f x| ≤ ∫ x, Real.sqrt 2 * |f x| := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
          (hf.abs.const_mul _) (Filter.Eventually.of_forall fun x => ?_)
        beta_reduce
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (Torus.abs_realMode_le k x) (abs_nonneg _)
    _ = _ := integral_const_mul _ _

lemma coord_ofFun (hm : (d : ℝ) < 2 * m) {f : Torus d → ℝ} (hf : Integrable f) (k : NonzeroLattice d) :
    NegSobolev.coord (NegSobolev.ofFun m f) k = Lattice.jp k.1 ^ (-m) * Torus.funRealCoeff f k :=
  NegSobolev.coord_ofSeq_of_mem _ (memℓp_funRealCoeff hm hf) k

lemma ofFun_neg (hm : (d : ℝ) < 2 * m) {f : Torus d → ℝ} (hf : Integrable f) :
    NegSobolev.ofFun m (fun x => -f x) = -NegSobolev.ofFun m f := by
  refine lp.ext (funext fun k => ?_)
  show NegSobolev.coord (NegSobolev.ofFun m fun x => -f x) k = NegSobolev.coord (-NegSobolev.ofFun m f) k
  have hf' : Integrable (fun x => -f x) := hf.neg
  rw [coord_ofFun hm hf', show NegSobolev.coord (-NegSobolev.ofFun m f) k =
    -NegSobolev.coord (NegSobolev.ofFun m f) k from rfl, coord_ofFun hm hf]
  unfold Torus.funRealCoeff
  simp only [mul_neg, integral_neg]

lemma sqrtN_ofMeasureDiff (hm : (d : ℝ) < 2 * m) {q ρ : Torus d → ℝ} (hq : IsProbDensity q)
    (hρ : IsProbDensity ρ) {f : Torus d → ℝ} (hf : Integrable f) {c0 : ℝ}
    (h : ∀ x, c0 * (q x - ρ x) = f x) :
    c0 • NegSobolev.ofMeasureDiff m (withDensityReal q) (withDensityReal ρ) = NegSobolev.ofFun m f := by
  haveI := isProb_withDensityReal hq
  haveI := isProb_withDensityReal hρ
  refine lp.ext (funext fun k => ?_)
  show NegSobolev.coord (c0 • NegSobolev.ofMeasureDiff m (withDensityReal q) (withDensityReal ρ)) k =
    NegSobolev.coord (NegSobolev.ofFun m f) k
  rw [coord_ofFun hm hf, coord_smul', coord_ofMeasureDiff hm]
  unfold Torus.measureRealCoeff Torus.funRealCoeff
  rw [integral_withDensityReal_eq q hq.measurable hq.nonneg, integral_withDensityReal_eq ρ hρ.measurable hρ.nonneg]
  have iq : Integrable (fun x => q x * Torus.realMode k x) :=
    integrable_mul_bdd (integrable_of_pd hq) (Torus.continuous_realMode k).measurable
      (fun x => Torus.abs_realMode_le k x)
  have iρ : Integrable (fun x => ρ x * Torus.realMode k x) :=
    integrable_mul_bdd (integrable_of_pd hρ) (Torus.continuous_realMode k).measurable
      (fun x => Torus.abs_realMode_le k x)
  have : ∫ x, Torus.realMode k x * f x = c0 * ((∫ x, q x * Torus.realMode k x) - ∫ x, ρ x * Torus.realMode k x) := by
    rw [← integral_sub iq iρ, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [← h x]; ring
  rw [this]; ring

lemma fld_shift (hm : (d : ℝ) < 2 * m) {N : ℕ} (hN : 1 ≤ N) {q ρ : Torus d → ℝ}
    (hq : IsProbDensity q) (hρ : IsProbDensity ρ) (X : Config d N) :
    fld m N (withDensityReal ρ) X = fld m N (withDensityReal q) X +
      Real.sqrt N • NegSobolev.ofMeasureDiff m (withDensityReal q) (withDensityReal ρ) := by
  haveI := isProb_withDensityReal hq
  haveI := isProb_withDensityReal hρ
  haveI := empirical_isProbabilityMeasure (by omega : 0 < N) X
  unfold fld
  rw [NegSobolev.ofMeasureDiff_add hm (empirical X) (withDensityReal q) (withDensityReal ρ), smul_add]


lemma integral_mix {P₁ P₂ : Measure (NegSobolev d m)} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {Φ : NegSobolev d m → ℝ} (hΦ : Continuous Φ) {C : ℝ} (hC : ∀ z, |Φ z| ≤ C) :
    ∫ z, Φ z ∂((2 : ℝ≥0∞)⁻¹ • P₁ + (2 : ℝ≥0∞)⁻¹ • P₂) =
      (1 / 2) * ∫ z, Φ z ∂P₁ + (1 / 2) * ∫ z, Φ z ∂P₂ := by
  have hi : ∀ (P : Measure (NegSobolev d m)) [IsProbabilityMeasure P], Integrable Φ P := fun P _ =>
    Integrable.of_bound hΦ.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hC z)
  rw [integral_add_measure ((hi P₁).smul_measure (by simp)) ((hi P₂).smul_measure (by simp)),
    integral_smul_measure, integral_smul_measure]
  simp

lemma smoothDist_mix_le {P₁ P₂ Q₁ Q₂ : Measure (NegSobolev d m)} [IsProbabilityMeasure P₁]
    [IsProbabilityMeasure P₂] [IsProbabilityMeasure Q₁] [IsProbabilityMeasure Q₂] :
    smoothDist 2 ((2 : ℝ≥0∞)⁻¹ • P₁ + (2 : ℝ≥0∞)⁻¹ • P₂) ((2 : ℝ≥0∞)⁻¹ • Q₁ + (2 : ℝ≥0∞)⁻¹ • Q₂) ≤
      (1 / 2) * smoothDist 2 P₁ Q₁ + (1 / 2) * smoothDist 2 P₂ Q₂ := by
  have : Nonempty (CbUnitBall (NegSobolev d m) 2) := ⟨⟨0, zero_mem_cbUnitBall 2⟩⟩
  have h1 := smoothDist_nonneg 2 P₁ Q₁
  have h2 := smoothDist_nonneg 2 P₂ Q₂
  refine Real.iSup_le (fun Φ => ?_) (by positivity)
  have hΦ : Φ.1 ∈ CbUnitBall (NegSobolev d m) 2 := Φ.2
  have hc : Continuous Φ.1 := hΦ.1.continuous
  have hb : ∀ z, |Φ.1 z| ≤ 1 := fun z => abs_apply_le_of_mem hΦ z
  rw [integral_mix hc hb, integral_mix hc hb]
  have a1 := abs_integral_sub_le_smoothDist hΦ P₁ Q₁
  have a2 := abs_integral_sub_le_smoothDist hΦ P₂ Q₂
  calc _ = |(1 / 2) * (∫ z, Φ.1 z ∂P₁ - ∫ z, Φ.1 z ∂Q₁) + (1 / 2) * (∫ z, Φ.1 z ∂P₂ - ∫ z, Φ.1 z ∂Q₂)| := by
        congr 1; ring
    _ ≤ |(1 / 2) * (∫ z, Φ.1 z ∂P₁ - ∫ z, Φ.1 z ∂Q₁)| + |(1 / 2) * (∫ z, Φ.1 z ∂P₂ - ∫ z, Φ.1 z ∂Q₂)| :=
        abs_add_le _ _
    _ ≤ _ := by
        rw [abs_mul, abs_mul]
        norm_num
        linarith

lemma smoothDist_translate_le {P Q : Measure (NegSobolev d m)} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (s : NegSobolev d m) :
    smoothDist 2 (P.map fun x => x + s) (Q.map fun x => x + s) ≤ smoothDist 2 P Q := by
  have : Nonempty (CbUnitBall (NegSobolev d m) 2) := ⟨⟨0, zero_mem_cbUnitBall 2⟩⟩
  refine Real.iSup_le (fun Φ => ?_) (smoothDist_nonneg 2 P Q)
  have hΦ : Φ.1 ∈ CbUnitBall (NegSobolev d m) 2 := Φ.2
  have hc : Continuous Φ.1 := hΦ.1.continuous
  rw [integral_map (measurable_add_const s).aemeasurable hc.aestronglyMeasurable,
    integral_map (measurable_add_const s).aemeasurable hc.aestronglyMeasurable]
  exact abs_integral_sub_le_smoothDist (cbUnitBall_translate hΦ s) P Q

end Book

end HRS.IID
