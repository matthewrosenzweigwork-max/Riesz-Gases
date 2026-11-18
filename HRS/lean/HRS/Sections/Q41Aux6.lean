import Mathlib
import HRS.Sections.Q41Aux1

/-!
# Packet Q41, helper 6: limits of Gaussian vectors and Gaussian fourth moments
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal Matrix RealInnerProductSpace

namespace HRS.Q41

/-- An a.s. limit of centred Gaussian vectors with covariances converging entrywise is the
centred Gaussian vector with the limit covariance. -/
lemma q41_gauss_limit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (V : ℕ → Ω → EuclideanSpace ℝ ι) (Vi : Ω → EuclideanSpace ℝ ι)
    (hVm : ∀ n, AEMeasurable (V n) P) (hVi : AEMeasurable Vi P)
    (Sn : ℕ → Matrix ι ι ℝ) (S : Matrix ι ι ℝ)
    (hlaw : ∀ n, P.map (V n) = multivariateGaussian 0 (Sn n))
    (hpsd : ∀ n, (Sn n).PosSemidef)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => V n ω) atTop (𝓝 (Vi ω)))
    (hS : ∀ a b, Tendsto (fun n => Sn n a b) atTop (𝓝 (S a b))) :
    P.map Vi = multivariateGaussian 0 S := by
  classical
  -- `S` is positive semidefinite
  have hSpsd : S.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · refine Matrix.IsHermitian.ext fun a b => ?_
      have h1 := hS b a
      have h2 := hS a b
      have h3 : ∀ n, Sn n b a = Sn n a b := fun n => by
        have := (hpsd n).1
        simpa using Matrix.IsHermitian.apply this a b
      simp only [h3] at h1
      simpa using tendsto_nhds_unique h1 h2
    · have hx : Tendsto (fun n => star x ⬝ᵥ (Sn n *ᵥ x)) atTop (𝓝 (star x ⬝ᵥ (S *ᵥ x))) := by
        simp only [dotProduct, Matrix.mulVec, star_trivial]
        refine tendsto_finsetSum _ fun a _ => ?_
        refine Tendsto.const_mul _ (tendsto_finsetSum _ fun b _ => ?_)
        exact (hS a b).mul_const _
      exact ge_of_tendsto hx (Eventually.of_forall fun n => (hpsd n).dotProduct_mulVec_nonneg x)
  haveI : IsProbabilityMeasure (P.map Vi) := (Measure.isProbabilityMeasure_map_iff hVi).2 inferInstance
  refine Measure.ext_of_charFun ?_
  funext t
  rw [charFun_multivariateGaussian hSpsd]
  -- the limit of characteristic functions
  have hcont : Continuous fun v : EuclideanSpace ℝ ι =>
      Complex.exp (↑⟪v, t⟫ * Complex.I) := by fun_prop
  have e1 : ∀ n, charFun (P.map (V n)) t = ∫ ω, Complex.exp (↑⟪V n ω, t⟫ * Complex.I) ∂P := by
    intro n
    rw [charFun_apply, integral_map (hVm n) hcont.aestronglyMeasurable]
  have e2 : charFun (P.map Vi) t = ∫ ω, Complex.exp (↑⟪Vi ω, t⟫ * Complex.I) ∂P := by
    rw [charFun_apply, integral_map hVi hcont.aestronglyMeasurable]
  have h1 : Tendsto (fun n => charFun (P.map (V n)) t) atTop (𝓝 (charFun (P.map Vi) t)) := by
    simp only [e1, e2]
    refine tendsto_integral_of_dominated_convergence (fun _ => 1) (fun n => ?_) (integrable_const _)
      (fun n => ?_) ?_
    · exact (hcont.comp_aestronglyMeasurable (hVm n).aestronglyMeasurable)
    · refine Eventually.of_forall fun ω => ?_
      rw [Complex.norm_exp_ofReal_mul_I]
    · filter_upwards [hlim] with ω hω
      exact (hcont.tendsto _).comp hω
  have h2 : Tendsto (fun n => charFun (P.map (V n)) t) atTop
      (𝓝 (Complex.exp (↑⟪t, (0 : EuclideanSpace ℝ ι)⟫ * Complex.I - ↑(t ⬝ᵥ S *ᵥ t) / 2))) := by
    simp_rw [hlaw, charFun_multivariateGaussian (hpsd _)]
    refine (Complex.continuous_exp.tendsto _).comp ?_
    have h3 : Tendsto (fun n => t ⬝ᵥ (Sn n *ᵥ t)) atTop (𝓝 (t ⬝ᵥ (S *ᵥ t))) := by
      simp only [dotProduct, Matrix.mulVec]
      refine tendsto_finsetSum _ fun a _ => ?_
      refine Tendsto.const_mul _ (tendsto_finsetSum _ fun b _ => ?_)
      exact (hS a b).mul_const _
    have h4 := ((Complex.continuous_ofReal.tendsto _).comp h3).div_const 2
    exact (tendsto_const_nhds (x := (↑⟪t, (0 : EuclideanSpace ℝ ι)⟫ * Complex.I : ℂ))).sub h4
  exact tendsto_nhds_unique h1 h2

lemma q41_pow4_le_exp (z : ℝ) : z ^ 4 ≤ 24 * (Real.exp z + Real.exp (-z)) := by
  have h1 : |z| ^ 4 / (Nat.factorial 4 : ℝ) ≤ Real.exp |z| := Real.pow_div_factorial_le_exp |z| (abs_nonneg z) 4
  have h2 : Real.exp |z| ≤ Real.exp z + Real.exp (-z) := by
    rcases abs_cases z with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; linarith [Real.exp_pos (-z)]
    · rw [h]; linarith [Real.exp_pos z]
  have h3 : |z| ^ 4 = z ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
  rw [h3] at h1
  simp [Nat.factorial] at h1
  linarith

lemma q41_std_fourth_lintegral :
    ∫⁻ x, ENNReal.ofReal (x ^ 4) ∂(gaussianReal 0 1) ≤ ENNReal.ofReal (48 * Real.exp (1 / 2)) := by
  have hmgf : ∀ t : ℝ, ∫ x, Real.exp (t * x) ∂(gaussianReal 0 1) = Real.exp (t ^ 2 / 2) := by
    intro t
    have := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) t
    simpa [mgf] using this
  have hint : ∀ t : ℝ, Integrable (fun x => Real.exp (t * x)) (gaussianReal 0 1) :=
    fun t => integrable_exp_mul_gaussianReal t
  calc ∫⁻ x, ENNReal.ofReal (x ^ 4) ∂(gaussianReal 0 1)
      ≤ ∫⁻ x, ENNReal.ofReal (24 * (Real.exp (1 * x) + Real.exp ((-1) * x))) ∂(gaussianReal 0 1) := by
        refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
        have := q41_pow4_le_exp x
        simpa using this
    _ = ENNReal.ofReal (∫ x, 24 * (Real.exp (1 * x) + Real.exp ((-1) * x)) ∂(gaussianReal 0 1)) := by
        rw [ofReal_integral_eq_lintegral_ofReal]
        · exact ((hint 1).add (hint (-1))).const_mul 24
        · exact Filter.Eventually.of_forall fun x => by positivity
    _ = ENNReal.ofReal (48 * Real.exp (1 / 2)) := by
        rw [integral_const_mul, integral_add (hint 1) (hint (-1)), hmgf, hmgf]
        congr 1
        norm_num
        ring

lemma q41_gauss_fourth_lintegral (v : ℝ≥0) :
    ∫⁻ x, ENNReal.ofReal (x ^ 4) ∂(gaussianReal 0 v) ≤
      ENNReal.ofReal (48 * Real.exp (1 / 2) * (v : ℝ) ^ 2) := by
  rw [q41_gauss_scale v, lintegral_map (by fun_prop) (by fun_prop)]
  have : ∀ z : ℝ, ENNReal.ofReal ((Real.sqrt v * z) ^ 4) = ENNReal.ofReal ((v : ℝ) ^ 2) * ENNReal.ofReal (z ^ 4) := by
    intro z
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have : (Real.sqrt v) ^ 2 = v := Real.sq_sqrt v.2
    calc (Real.sqrt v * z) ^ 4 = ((Real.sqrt v) ^ 2) ^ 2 * z ^ 4 := by ring
      _ = _ := by rw [this]
  simp_rw [this]
  rw [lintegral_const_mul _ (by fun_prop)]
  calc ENNReal.ofReal ((v : ℝ) ^ 2) * ∫⁻ z, ENNReal.ofReal (z ^ 4) ∂(gaussianReal 0 1)
      ≤ ENNReal.ofReal ((v : ℝ) ^ 2) * ENNReal.ofReal (48 * Real.exp (1 / 2)) :=
        mul_le_mul_right q41_std_fourth_lintegral _
    _ = ENNReal.ofReal (48 * Real.exp (1 / 2) * (v : ℝ) ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

lemma q41_lintegral_cs {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f g : Ω → ℝ≥0∞)
    (hf : AEMeasurable f P) (hg : AEMeasurable g P) :
    ∫⁻ ω, f ω * g ω ∂P ≤
      (∫⁻ ω, f ω ^ 2 ∂P) ^ (1 / 2 : ℝ) * (∫⁻ ω, g ω ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq hf hg
  simpa [ENNReal.rpow_two] using h

/-- Fourth-moment bound for weighted sums of squares of centred Gaussians. -/
lemma q41_weighted_sq_moment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {ι : Type*} [Countable ι] (g : ι → Ω → ℝ) (w : ι → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hg : ∀ k, Measurable (g k)) (v : ι → ℝ≥0)
    (hlaw : ∀ k, P.map (g k) = gaussianReal 0 (v k)) :
    ∫⁻ ω, (∑' k, ENNReal.ofReal (w k * g k ω ^ 2)) ^ 2 ∂P ≤
      ENNReal.ofReal (48 * Real.exp (1 / 2)) * (∑' k, ENNReal.ofReal (w k * (v k : ℝ))) ^ 2 := by
  set a : ι → Ω → ℝ≥0∞ := fun k ω => ENNReal.ofReal (w k * g k ω ^ 2) with ha
  have ham : ∀ k, Measurable (a k) := fun k => by
    simp only [ha]; exact ENNReal.measurable_ofReal.comp ((hg k).pow_const 2 |>.const_mul _)
  -- second moments of the terms
  have hs : ∀ k, (∫⁻ ω, a k ω ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt (48 * Real.exp (1 / 2)) * (w k * (v k : ℝ))) := by
    intro k
    have h1 : ∫⁻ ω, a k ω ^ 2 ∂P = ENNReal.ofReal (w k ^ 2) *
        ∫⁻ x, ENNReal.ofReal (x ^ 4) ∂(gaussianReal 0 (v k)) := by
      rw [← hlaw k, lintegral_map (by fun_prop) (hg k)]
      rw [← lintegral_const_mul _ (by fun_prop)]
      refine lintegral_congr fun ω => ?_
      simp only [ha]
      rw [← ENNReal.ofReal_pow (by have := hw k; positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1; ring
    have h2 : ∫⁻ ω, a k ω ^ 2 ∂P ≤ ENNReal.ofReal (w k ^ 2 * (48 * Real.exp (1 / 2) * (v k : ℝ) ^ 2)) := by
      rw [h1, ENNReal.ofReal_mul (by positivity)]
      gcongr
      exact q41_gauss_fourth_lintegral (v k)
    calc (∫⁻ ω, a k ω ^ 2 ∂P) ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal (w k ^ 2 * (48 * Real.exp (1 / 2) * (v k : ℝ) ^ 2))) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow h2 (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt (w k ^ 2 * (48 * Real.exp (1 / 2) * (v k : ℝ) ^ 2))) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by have := hw k; positivity) (by norm_num),
            Real.sqrt_eq_rpow]
      _ = ENNReal.ofReal (Real.sqrt (48 * Real.exp (1 / 2)) * (w k * (v k : ℝ))) := by
          congr 1
          rw [show w k ^ 2 * (48 * Real.exp (1 / 2) * (v k : ℝ) ^ 2) =
              (w k * (v k : ℝ)) ^ 2 * (48 * Real.exp (1 / 2)) by ring,
            Real.sqrt_mul (by positivity), Real.sqrt_sq (by have := hw k; positivity)]
          ring
  -- expand the square of the series
  have hexp : ∀ ω, (∑' k, ENNReal.ofReal (w k * g k ω ^ 2)) ^ 2 = ∑' k, ∑' l, a k ω * a l ω := by
    intro ω
    rw [sq, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun k => ?_
    rw [← ENNReal.tsum_mul_left]
  simp_rw [hexp]
  rw [lintegral_tsum (f := fun k ω => ∑' l, a k ω * a l ω) (fun k => (AEMeasurable.ennreal_tsum fun l => ((ham k).mul (ham l)).aemeasurable))]
  have hkl : ∀ k, ∫⁻ ω, ∑' l, a k ω * a l ω ∂P ≤
      (∫⁻ ω, a k ω ^ 2 ∂P) ^ (1 / 2 : ℝ) * ∑' l, (∫⁻ ω, a l ω ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
    intro k
    rw [lintegral_tsum (f := fun l ω => a k ω * a l ω) (fun l => ((ham k).mul (ham l)).aemeasurable), ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun l => q41_lintegral_cs P (a k) (a l) (ham k).aemeasurable
      (ham l).aemeasurable
  calc ∑' k, ∫⁻ ω, ∑' l, a k ω * a l ω ∂P
      ≤ ∑' k, (∫⁻ ω, a k ω ^ 2 ∂P) ^ (1 / 2 : ℝ) * ∑' l, (∫⁻ ω, a l ω ^ 2 ∂P) ^ (1 / 2 : ℝ) :=
        ENNReal.tsum_le_tsum hkl
    _ = (∑' k, (∫⁻ ω, a k ω ^ 2 ∂P) ^ (1 / 2 : ℝ)) ^ 2 := by
        rw [ENNReal.tsum_mul_right, sq]
    _ ≤ (∑' k, ENNReal.ofReal (Real.sqrt (48 * Real.exp (1 / 2)) * (w k * (v k : ℝ)))) ^ 2 := by
        gcongr with k
        exact hs k
    _ = ENNReal.ofReal (48 * Real.exp (1 / 2)) * (∑' k, ENNReal.ofReal (w k * (v k : ℝ))) ^ 2 := by
        have : ∀ k, ENNReal.ofReal (Real.sqrt (48 * Real.exp (1 / 2)) * (w k * (v k : ℝ))) =
            ENNReal.ofReal (Real.sqrt (48 * Real.exp (1 / 2))) * ENNReal.ofReal (w k * (v k : ℝ)) :=
          fun k => ENNReal.ofReal_mul (Real.sqrt_nonneg _)
        simp_rw [this]
        rw [ENNReal.tsum_mul_left, mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
          Real.sq_sqrt (by positivity)]

end HRS.Q41
