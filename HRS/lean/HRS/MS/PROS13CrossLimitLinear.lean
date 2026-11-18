import HRS.MS.PROS13CrossActualAdd

/-!
# Generic S13: additive, approximation-independent quadratic Gaussian limit

The limit predicate captures exactly the Gaussian-side witness and original
finite-rank approximation statements of R26-T3.S13, without introducing
nonatomicity or assuming a nonempty orthonormal family. All random variables
are defined on one fixed ProductGaussian probability space.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

/-- The actual Gaussian quadratic random variable is the L² limit of its
finite-rank half-Wick polynomials; `h` is a product-L² kernel. -/
def HasActualProductQuadraticLimit
    (I : ProductGaussian μ) (h : Euc d → Euc d → ℝ)
    (Q : I.Ω → ℝ) : Prop :=
    MemLp Q 2 I.P ∧
    ∃ (r : ℕ → ℕ)
      (c : (j : ℕ) → Fin (r j) → Fin (r j) → ℝ)
      (u : (j : ℕ) → Fin (r j) → Euc d → ℝ),
      (∀ j, IsR2FiniteRankData (c j) (u j)) ∧
      Tendsto (fun j => eLpNorm
        (fun z : Euc d × Euc d =>
          r2FiniteRankKernel (c j) (u j) z.1 z.2 - h z.1 z.2)
        2 (μ.prod μ)) atTop (𝓝 0) ∧
      Tendsto (fun j : ℕ => ∫ ω : I.Ω,
        (((1 / 2 : ℝ) * ∑ a : Fin (r j), ∑ b : Fin (r j), c j a b *
            (I.η (u j a) ω * I.η (u j b) ω -
              ∫ ζ, I.η (u j a) ζ * I.η (u j b) ζ ∂I.P)) -
           Q ω) ^ 2 ∂I.P) atTop (𝓝 0)

theorem pro_s13_actual_product_quadratic_exists
    (I : ProductGaussian μ) (h : Euc d → Euc d → ℝ)
    (hh : MemLp (fun z : Euc d × Euc d => h z.1 z.2) 2 (μ.prod μ))
    (hs : ∀ x y, h x y = h y x) :
    ∃ Q : I.Ω → ℝ, HasActualProductQuadraticLimit I h Q := by
  obtain ⟨r, c, u, Q, hd, hK, hQ, hlim⟩ :=
    pro_s13_generic_actual_quadratic_L2_witness I h hh hs
  exact ⟨Q, hQ, r, c, u, hd, hK, hlim⟩

theorem pro_s13_actual_product_quadratic_unique
    (I : ProductGaussian μ) (h : Euc d → Euc d → ℝ)
    (hh : MemLp (fun z : Euc d × Euc d => h z.1 z.2) 2 (μ.prod μ))
    (Q Q' : I.Ω → ℝ)
    (hQ : HasActualProductQuadraticLimit I h Q)
    (hQ' : HasActualProductQuadraticLimit I h Q') :
    Q =ᵐ[I.P] Q' := by
  obtain ⟨hm, r, c, u, hd, hK, hlim⟩ := hQ
  obtain ⟨hm', s, c', v, hd', hK', hlim'⟩ := hQ'
  exact pro_s13_generic_actual_quadratic_unique
    I h hh r s c u c' v hd hd' Q Q' hm hm' hK hK' hlim hlim'

theorem pro_s13_actual_product_quadratic_add
    (I : ProductGaussian μ)
    (h h' : Euc d → Euc d → ℝ)
    (hh : MemLp (fun z : Euc d × Euc d => h z.1 z.2) 2 (μ.prod μ))
    (hh' : MemLp (fun z : Euc d × Euc d => h' z.1 z.2) 2 (μ.prod μ))
    (Q Q' : I.Ω → ℝ)
    (hQ : HasActualProductQuadraticLimit I h Q)
    (hQ' : HasActualProductQuadraticLimit I h' Q') :
    HasActualProductQuadraticLimit I
      (fun x y => h x y + h' x y) (fun ω => Q ω + Q' ω) := by
  obtain ⟨hm, r, c, u, hd, hK, hlim⟩ := hQ
  obtain ⟨hm', s, c', v, hd', hK', hlim'⟩ := hQ'
  obtain ⟨C, w, hC, hCkernel, hCgaussian⟩ :=
    pro_s13_actual_quadratic_additive_approximation
      I h h' hh hh' r s c u c' v hd hd' Q Q' hm hm'
        hK hK' hlim hlim'
  exact ⟨hm.add hm', fun j => r j + s j, C, w,
    hC, hCkernel, hCgaussian⟩

end HRS.MS.R26T3
