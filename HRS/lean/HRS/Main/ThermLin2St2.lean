import HRS.Main.ThermLin2St1

/-!
# THERMLIN2, packet St, part 2: the vector `(eval ξ ψ_a)_a` of a centered Gaussian `ξ` and sums of independent Gaussian vectors
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Complex
open scoped ENNReal NNReal BigOperators Matrix RealInnerProductSpace

namespace HRS.ThermLin.Plan2

open HRS HRS.GF HRS.Uniform HRS.Uniform.Q54c HRS.Uniform.Q07c HRS.T25P

variable {d : ℕ}

/-- The covariance matrix of a centered Gaussian on test functions is positive semidefinite and the vector
`(eval ξ ψ_a)_a` has the Gaussian characteristic function. -/
theorem tl2St_xi_charFun {m : ℝ} (C : (Torus d → ℝ) → (Torus d → ℝ) → ℝ)
    (γ : Measure (NegSobolev d m)) (hγ : IsCenteredGaussianWithCov m γ C)
    {p : ℕ} (ψ : Fin p → Torus d → ℝ) (hψ : ∀ a, Torus.IsSmooth (ψ a))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Ω → NegSobolev d m) (hξ : Measurable ξ) (hlaw : P.map ξ = γ) :
    (Matrix.of fun a b => C (ψ a) (ψ b)).PosSemidef ∧
    ∀ t : EuclideanSpace ℝ (Fin p),
      charFun (P.map (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (ξ ω) (ψ a) :
        EuclideanSpace ℝ (Fin p)))) t =
      Complex.exp (-((t ⬝ᵥ (Matrix.of fun a b => C (ψ a) (ψ b)) *ᵥ t : ℝ) : ℂ) / 2) := by
  have hG : IsGaussian γ := hγ.1.1
  have hmem : ∀ a, MemSobolev m (ψ a) := fun a => HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (hψ a) m
  set ℓ : Fin p → NegSobolev d m →L[ℝ] ℝ := fun a => gfb4_ell m (ψ a) with hℓ
  have hℓapp : ∀ a x, ℓ a x = NegSobolev.eval x (ψ a) := fun a x => gfb4_ell_apply (hmem a) x
  have hℓ2 : ∀ a, MemLp (ℓ a) 2 γ := fun a => IsGaussian.memLp_dual γ (ℓ a) 2 (by simp)
  have hcov : ∀ a b, ∫ x, ℓ a x * ℓ b x ∂γ = C (ψ a) (ψ b) := by
    intro a b
    simp_rw [hℓapp]
    exact hγ.2 _ _ (hψ a) (hψ b)
  set S : Matrix (Fin p) (Fin p) ℝ := Matrix.of fun a b => C (ψ a) (ψ b) with hS
  -- the quadratic form
  have hquad : ∀ t : EuclideanSpace ℝ (Fin p),
      ∫ x, (∑ a, t a * ℓ a x) ^ 2 ∂γ = t ⬝ᵥ S *ᵥ t := by
    intro t
    have hi : ∀ a b, Integrable (fun x => t a * ℓ a x * (t b * ℓ b x)) γ := fun a b =>
      (((hℓ2 a).const_mul (t a)).integrable_mul ((hℓ2 b).const_mul (t b)))
    simp only [sq, Finset.sum_mul_sum]
    rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => hi a b)]
    simp only [dotProduct, Matrix.mulVec, hS, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ (fun b _ => hi a b)]
    refine Finset.sum_congr rfl fun b _ => ?_
    have : ∀ x, t a * ℓ a x * (t b * ℓ b x) = (t a * t b) * (ℓ a x * ℓ b x) := fun x => by ring
    simp_rw [this]
    rw [integral_const_mul, hcov a b]
    ring
  constructor
  · rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x => ?_⟩
    · ext a b
      simp only [Matrix.conjTranspose_apply, hS, Matrix.of_apply, star_trivial]
      rw [← hcov, ← hcov]
      simp_rw [mul_comm (ℓ a _)]
    · have := hquad (WithLp.toLp 2 x)
      have h0 : 0 ≤ ∫ y, (∑ a, (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin p)) a * ℓ a y) ^ 2 ∂γ :=
        integral_nonneg fun y => sq_nonneg _
      rw [this] at h0
      simpa using h0
  · intro t
    set Lt : NegSobolev d m →L[ℝ] ℝ := ∑ a, t a • ℓ a with hLt
    have hLtapp : ∀ x, Lt x = ∑ a, t a * ℓ a x := by
      intro x
      simp [hLt]
    have h1 : charFun (P.map (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (ξ ω) (ψ a) :
        EuclideanSpace ℝ (Fin p)))) t = ∫ x, Complex.exp (Lt x * Complex.I) ∂γ := by
      have hAm : Measurable (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (ξ ω) (ψ a) :
          EuclideanSpace ℝ (Fin p))) :=
        measurable_toLp_eval fun a => (continuous_eval_const (hmem a)).measurable.comp hξ
      rw [charFun_apply, integral_map hAm.aemeasurable
        (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin p) =>
          Complex.exp (inner ℝ y t * Complex.I)).aestronglyMeasurable,
        ← hlaw, integral_map hξ.aemeasurable
        (by fun_prop : Continuous fun y : NegSobolev d m =>
          Complex.exp ((Lt y : ℝ) * Complex.I)).aestronglyMeasurable]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only [hLtapp, hℓapp, PiLp.inner_apply, WithLp.ofLp_toLp]
      congr 2
    rw [h1, ← charFunDual_apply, IsGaussian.charFunDual_eq]
    have hmean : ∫ x, Lt x ∂γ = 0 := hγ.1.2 Lt
    have hvar : Var[Lt; γ] = t ⬝ᵥ S *ᵥ t := by
      rw [variance_eq_integral Lt.continuous.measurable.aemeasurable, hmean]
      simp_rw [sub_zero, hLtapp]
      exact hquad t
    rw [integral_complex_ofReal, hmean, hvar]
    simp [neg_div]

/-- The sum of two independent centered Gaussian vectors. -/
theorem tl2St_law_add {p : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X A : Ω → EuclideanSpace ℝ (Fin p)) (hX : Measurable X) (hA : Measurable A) (hind : IndepFun X A P)
    {B Sg : Matrix (Fin p) (Fin p) ℝ} (hB : B.PosSemidef) (hSg : Sg.PosSemidef)
    (hXlaw : P.map X = multivariateGaussian 0 B)
    (hAchar : ∀ t : EuclideanSpace ℝ (Fin p),
      charFun (P.map A) t = Complex.exp (-((t ⬝ᵥ Sg *ᵥ t : ℝ) : ℂ) / 2)) :
    P.map (fun ω => X ω + A ω) = multivariateGaussian 0 (B + Sg) := by
  refine eq_multivariateGaussian P (hX.add hA) (hB.add hSg) (fun t => ?_)
  have h1 := congrFun (hind.charFun_map_fun_add_eq_mul hX.aemeasurable hA.aemeasurable) t
  have hfun : (fun ω => X ω + A ω) = X + A := rfl
  rw [hfun] at h1
  rw [h1, Pi.mul_apply, hXlaw, hAchar t, charFun_multivariateGaussian hB]
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub, neg_div]
  rw [← Complex.exp_add]
  congr 1
  rw [Matrix.add_mulVec, dotProduct_add]
  push_cast
  ring

end HRS.ThermLin.Plan2
