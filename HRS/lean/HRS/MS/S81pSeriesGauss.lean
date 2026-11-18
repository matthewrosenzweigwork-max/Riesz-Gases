import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# S8.1 (worker S81P): series of independent Gaussians

Namespace `HRS.Whole.S81P`, prefix `s81p_`.

`s81p_series_gaussian`: let `Z_l` be independent centered real Gaussians with variances `σ_l²` and `c : Fin p → ℕ → ℝ`; if the
(pointwise, deterministic) series `V_a = Σ_l c_{a,l} Z_l` converge, with `Σ_l c_{a,l}² σ_l² < ∞`, then the vector `V` is centered
Gaussian with covariance matrix `Σ_l c_{a,l} c_{b,l} σ_l²`.  Used for the initial and old Gaussian blocks of the burn-in coupling
(spectral Gaussian `ℓ²` vectors pushed through the return map).  Proof: finite partial sums are Gaussian (induction with
`gaussianReal_add_gaussianReal_of_indepFun`), pass to the limit in the characteristic function by dominated convergence.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Whole.S81P

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Finite partial sums of independent Gaussians are Gaussian. -/
theorem s81p_partial_gauss (P : Measure Ω) [IsProbabilityMeasure P] (Zc : ℕ → Ω → ℝ)
    (hZm : ∀ l, Measurable (Zc l)) (σ2 : ℕ → ℝ≥0) (hind : iIndepFun Zc P)
    (hlaw : ∀ l, HasLaw (Zc l) (gaussianReal 0 (σ2 l)) P) (lam : ℕ → ℝ) (n : ℕ) :
    P.map (fun ω => ∑ l ∈ Finset.range n, lam l * Zc l ω) =
      gaussianReal 0 (∑ l ∈ Finset.range n, (lam l ^ 2).toNNReal * σ2 l) := by
  have hind' : iIndepFun (fun l ω => lam l * Zc l ω) P :=
    hind.comp (fun l x => lam l * x) (fun l => measurable_const.mul measurable_id)
  have hmeas : ∀ l, Measurable (fun ω => lam l * Zc l ω) := fun l => measurable_const.mul (hZm l)
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    have : (fun _ : Ω => (0 : ℝ)) = fun _ => 0 := rfl
    rw [Measure.map_const]
    simp [gaussianReal_zero_var]
  | succ n ih =>
    have hsplit : (fun ω => ∑ l ∈ Finset.range (n + 1), lam l * Zc l ω) =
        (fun ω => ∑ l ∈ Finset.range n, lam l * Zc l ω) + fun ω => lam n * Zc n ω := by
      funext ω
      simp [Finset.sum_range_succ]
    rw [hsplit]
    have hI : IndepFun (∑ l ∈ Finset.range n, fun ω => lam l * Zc l ω) (fun ω => lam n * Zc n ω) P :=
      hind'.indepFun_finsetSum_of_notMem₀ (fun l => (hmeas l).aemeasurable)
        (Finset.notMem_range_self (n := n))
    have e : (∑ l ∈ Finset.range n, fun ω => lam l * Zc l ω) =
        fun ω => ∑ l ∈ Finset.range n, lam l * Zc l ω := by
      funext ω; simp
    rw [e] at hI
    have h1 : HasLaw (fun ω => ∑ l ∈ Finset.range n, lam l * Zc l ω)
        (gaussianReal 0 (∑ l ∈ Finset.range n, (lam l ^ 2).toNNReal * σ2 l)) P :=
      ⟨(Finset.measurable_sum _ fun l _ => hmeas l).aemeasurable, ih⟩
    have h2 : HasLaw (fun ω => lam n * Zc n ω) (gaussianReal (lam n * 0)
        (NNReal.mk (lam n ^ 2) (sq_nonneg _) * σ2 n)) P := gaussianReal_const_mul (hlaw n) (lam n)
    rw [mul_zero] at h2
    rw [gaussianReal_add_gaussianReal_of_indepFun hI h1 h2, zero_add, Finset.sum_range_succ]
    congr 2
    ext
    simp [Real.coe_toNNReal _ (sq_nonneg (lam n))]

/-- The covariance matrix `Σ_l c_{a,l} c_{b,l} σ_l²`. -/
def s81p_seriesCov {p : ℕ} (c : Fin p → ℕ → ℝ) (σ2 : ℕ → ℝ≥0) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun a b => ∑' l, c a l * c b l * (σ2 l : ℝ)

theorem s81p_series_summable {p : ℕ} {c : Fin p → ℕ → ℝ} {σ2 : ℕ → ℝ≥0}
    (hc : ∀ a, Summable fun l => c a l ^ 2 * (σ2 l : ℝ)) (a b : Fin p) :
    Summable fun l => c a l * c b l * (σ2 l : ℝ) := by
  refine Summable.of_norm_bounded (((hc a).add (hc b)).mul_left (1 / 2 : ℝ)) fun l => ?_
  have h0 : (0 : ℝ) ≤ σ2 l := (σ2 l).2
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
  have : |c a l * c b l| ≤ (1 / 2) * (c a l ^ 2 + c b l ^ 2) := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (c a l + c b l), sq_nonneg (c a l - c b l)]
  nlinarith

theorem s81p_seriesCov_quad {p : ℕ} {c : Fin p → ℕ → ℝ} {σ2 : ℕ → ℝ≥0}
    (hc : ∀ a, Summable fun l => c a l ^ 2 * (σ2 l : ℝ)) (x : Fin p → ℝ) :
    HasSum (fun l => (σ2 l : ℝ) * (∑ a, x a * c a l) ^ 2)
      (x ⬝ᵥ (s81p_seriesCov c σ2).mulVec x) := by
  have h : ∀ a b, HasSum (fun l => c a l * c b l * (σ2 l : ℝ)) (s81p_seriesCov c σ2 a b) :=
    fun a b => (s81p_series_summable hc a b).hasSum
  have h2 : HasSum (fun l => ∑ a, ∑ b, x a * x b * (c a l * c b l * (σ2 l : ℝ)))
      (∑ a, ∑ b, x a * x b * s81p_seriesCov c σ2 a b) :=
    hasSum_sum fun a _ => hasSum_sum fun b _ => (h a b).mul_left (x a * x b)
  have e1 : (fun l => ∑ a, ∑ b, x a * x b * (c a l * c b l * (σ2 l : ℝ))) =
      fun l => (σ2 l : ℝ) * (∑ a, x a * c a l) ^ 2 := by
    funext l
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have e2 : x ⬝ᵥ (s81p_seriesCov c σ2).mulVec x = ∑ a, ∑ b, x a * x b * s81p_seriesCov c σ2 a b := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [e1] at h2
  rw [e2]
  exact h2

theorem s81p_seriesCov_psd {p : ℕ} {c : Fin p → ℕ → ℝ} {σ2 : ℕ → ℝ≥0}
    (hc : ∀ a, Summable fun l => c a l ^ 2 * (σ2 l : ℝ)) : (s81p_seriesCov c σ2).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext a b
    simp only [Matrix.conjTranspose_apply, star_trivial, s81p_seriesCov, Matrix.of_apply]
    refine tsum_congr fun l => ?_
    ring
  · simp only [star_trivial]
    exact (s81p_seriesCov_quad hc x).nonneg fun l => mul_nonneg (σ2 l).2 (sq_nonneg _)

/-- **Series of independent Gaussians.** -/
theorem s81p_series_gaussian {p : ℕ} (P : Measure Ω) [IsProbabilityMeasure P] (Zc : ℕ → Ω → ℝ)
    (hZm : ∀ l, Measurable (Zc l)) (σ2 : ℕ → ℝ≥0) (hind : iIndepFun Zc P)
    (hlaw : ∀ l, HasLaw (Zc l) (gaussianReal 0 (σ2 l)) P) (c : Fin p → ℕ → ℝ)
    (hc : ∀ a, Summable fun l => c a l ^ 2 * (σ2 l : ℝ))
    (V : Ω → EuclideanSpace ℝ (Fin p)) (hVm : Measurable V)
    (hV : ∀ᵐ ω ∂P, ∀ a, HasSum (fun l => c a l * Zc l ω) (V ω a)) :
    P.map V = multivariateGaussian 0 (s81p_seriesCov c σ2) := by
  have hpsd := s81p_seriesCov_psd hc
  refine Measure.ext_of_charFun ?_
  funext x
  -- the scalar series `⟪V, x⟫ = Σ_l λ_l Z_l`
  set lam : ℕ → ℝ := fun l => ∑ a, x a * c a l with hlam
  have hT : ∀ᵐ ω ∂P, HasSum (fun l => lam l * Zc l ω) (∑ a, x a * V ω a) := by
    filter_upwards [hV] with ω hVω
    have h := hasSum_sum (s := (Finset.univ : Finset (Fin p))) fun a _ => (hVω a).mul_left (x a)
    convert h using 1
    funext l
    rw [hlam]
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  have hinner : ∀ ω, inner ℝ x (V ω) = ∑ a, x a * V ω a := by
    intro ω
    simp [PiLp.inner_apply, mul_comm]
  have hcf : charFun (P.map V) x = ∫ ω, Complex.exp (((∑ a, x a * V ω a : ℝ) : ℂ) * Complex.I) ∂P := by
    rw [charFun_apply, integral_map hVm.aemeasurable (by fun_prop)]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    beta_reduce
    rw [real_inner_comm, hinner ω]
  have hq := s81p_seriesCov_quad hc x
  -- partial sums
  set Tn : ℕ → Ω → ℝ := fun n ω => ∑ l ∈ Finset.range n, lam l * Zc l ω with hTn
  have hTnm : ∀ n, Measurable (Tn n) := fun n =>
    Finset.measurable_sum _ fun l _ => measurable_const.mul (hZm l)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => Tn n ω) atTop (𝓝 (∑ a, x a * V ω a)) := by
    filter_upwards [hT] with ω hω using hω.tendsto_sum_nat
  have hint : Tendsto (fun n => ∫ ω, Complex.exp ((Tn n ω : ℂ) * Complex.I) ∂P) atTop
      (𝓝 (∫ ω, Complex.exp (((∑ a, x a * V ω a : ℝ) : ℂ) * Complex.I) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) (fun n => ?_)
      (integrable_const _) (fun n => Eventually.of_forall fun ω => ?_)
      (hlim.mono fun ω hω => ?_)
    · exact (by fun_prop : Measurable fun ω => Complex.exp ((Tn n ω : ℂ) * Complex.I)).aestronglyMeasurable
    · rw [Complex.norm_exp_ofReal_mul_I]
    · exact (Complex.continuous_exp.tendsto _).comp
        (((Complex.continuous_ofReal.tendsto _).comp hω).mul_const Complex.I)
  have hval : ∀ n, ∫ ω, Complex.exp ((Tn n ω : ℂ) * Complex.I) ∂P =
      Complex.exp (-(((∑ l ∈ Finset.range n, (σ2 l : ℝ) * lam l ^ 2 : ℝ) : ℂ) / 2)) := by
    intro n
    have h1 := s81p_partial_gauss P Zc hZm σ2 hind hlaw lam n
    have h2 : ∫ ω, Complex.exp ((Tn n ω : ℂ) * Complex.I) ∂P =
        charFun (P.map (Tn n)) 1 := by
      rw [charFun_apply, integral_map (hTnm n).aemeasurable (by fun_prop)]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp [mul_comm]
    have key : ((∑ l ∈ Finset.range n, (lam l ^ 2).toNNReal * σ2 l : ℝ≥0) : ℝ) =
        ∑ l ∈ Finset.range n, (σ2 l : ℝ) * lam l ^ 2 := by
      push_cast
      exact Finset.sum_congr rfl fun l _ => by rw [Real.coe_toNNReal _ (sq_nonneg _)]; ring
    rw [h2, show P.map (Tn n) = _ from h1, charFun_gaussianReal, key]
    push_cast
    ring_nf
  have hq' : Tendsto (fun n => Complex.exp (-(((∑ l ∈ Finset.range n, (σ2 l : ℝ) * lam l ^ 2 : ℝ) : ℂ) / 2)))
      atTop (𝓝 (Complex.exp (-(((x ⬝ᵥ (s81p_seriesCov c σ2).mulVec x : ℝ) : ℂ) / 2)))) := by
    refine (Complex.continuous_exp.tendsto _).comp ?_
    refine Tendsto.neg (Tendsto.div_const ((Complex.continuous_ofReal.tendsto _).comp ?_) _)
    exact hq.tendsto_sum_nat
  have hlimit : ∫ ω, Complex.exp (((∑ a, x a * V ω a : ℝ) : ℂ) * Complex.I) ∂P =
      Complex.exp (-(((x ⬝ᵥ (s81p_seriesCov c σ2).mulVec x : ℝ) : ℂ) / 2)) := by
    refine tendsto_nhds_unique hint ?_
    simpa only [hval] using hq'
  rw [hcf, hlimit, charFun_multivariateGaussian hpsd]
  simp

end HRS.Whole.S81P
