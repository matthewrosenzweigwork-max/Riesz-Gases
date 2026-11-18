import HRS.MS.PROS15dProjectionP21

/-!
# S15d: convert the physical S14a complete spectral family to a Hilbert basis

An arbitrary countable orthonormal family of centered measurable L²
representatives satisfying the exact S14a completeness condition yields a
Hilbert basis of the centered L² space. No smoothness or coefficient
decay is added to the S14a assumptions. This supplies the basis input
for the Gaussian first-chaos projection theorem.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.MS.R26T3
open HRS.Whole.Q34

theorem s15d_complete_physical_family_hilbert_basis
    {d : ℕ} {μ : Measure (HRS.Euc d)}
    [IsProbabilityMeasure μ]
    (e : ℕ → HRS.Euc d → ℝ)
    (he : ∀ j, HRS.Whole.MemL2Zero μ (e j))
    (hon : ∀ i j, ∫ x, e i x * e j x ∂μ =
      if i = j then 1 else 0)
    (hfull : ∀ f : HRS.Euc d → ℝ,
      HRS.Whole.MemL2Zero μ f →
      (∀ j, ∫ x, f x * e j x ∂μ = 0) → f =ᵐ[μ] 0) :
    ∃ b : HilbertBasis ℕ ℝ (s21h2_V μ),
      ∀ j, ((b j : s21h2_V μ) : Lp ℝ 2 μ) =
        (he j).1.toLp (e j) := by
  classical
  let v : ℕ → s21h2_V μ := fun j =>
    ⟨(he j).1.toLp (e j), by
      rw [s21h2_mem_V, inner_one2]
      rw [integral_congr_ae (he j).1.coeFn_toLp]
      exact (he j).2⟩
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    change inner ℝ ((he i).1.toLp (e i))
      ((he j).1.toLp (e j)) = _
    rw [s21h2_L2_inner]
    exact hon i j
  have hsp : (Submodule.span ℝ (Set.range v))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hvx : ∀ j, inner ℝ (v j) x = 0 := by
      intro j
      exact (Submodule.mem_orthogonal _ _).1 hx _
        (Submodule.subset_span ⟨j, rfl⟩)
    have hxm : HRS.Whole.MemL2Zero μ ((x : s21h2_V μ) : Lp ℝ 2 μ) := by
      refine ⟨Lp.memLp _, ?_⟩
      exact s21h2_mean_zero (s21h2_mem_V.1 x.prop)
    have horth : ∀ j, ∫ y,
        (((x : s21h2_V μ) : Lp ℝ 2 μ) y) * e j y ∂μ = 0 := by
      intro j
      have hi : inner ℝ (v j) x =
          ∫ y, e j y *
            (((x : s21h2_V μ) : Lp ℝ 2 μ) y) ∂μ := by
        change inner ℝ ((he j).1.toLp (e j))
          ((x : s21h2_V μ) : Lp ℝ 2 μ) = _
        simpa only [Lp.toLp_coeFn] using
          (s21h2_L2_inner (he j).1
            (Lp.memLp ((x : s21h2_V μ) : Lp ℝ 2 μ)))
      calc
        (∫ y, (((x : s21h2_V μ) : Lp ℝ 2 μ) y) * e j y ∂μ) =
          ∫ y, e j y *
            (((x : s21h2_V μ) : Lp ℝ 2 μ) y) ∂μ := by
              apply integral_congr_ae
              exact ae_of_all _ fun y => mul_comm _ _
        _ = 0 := hi.symm.trans (hvx j)
    have hz := hfull _ hxm horth
    apply Subtype.ext
    apply Lp.ext
    exact hz.trans (Lp.coeFn_zero ℝ 2 μ).symm
  let b : HilbertBasis ℕ ℝ (s21h2_V μ) :=
    HilbertBasis.mkOfOrthogonalEqBot hv hsp
  refine ⟨b, fun j => ?_⟩
  change ((b j : s21h2_V μ) : Lp ℝ 2 μ) =
    (he j).1.toLp (e j)
  simp only [b, HilbertBasis.coe_mkOfOrthogonalEqBot]
  rfl

#print axioms s15d_complete_physical_family_hilbert_basis
end HRS.MS.R26T3
