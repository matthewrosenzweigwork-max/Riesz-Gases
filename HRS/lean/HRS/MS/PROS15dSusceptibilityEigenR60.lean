import HRS.MS.PROS15dEigenResolventR60
import HRS.MS.S21H2_S14aD5

/-!
# S15d: the frozen susceptibilityCov diagonalizes on a physical eigenfamily

This is an exact responseInverse/susceptibilityCov calculation on the original
spatial L² representatives, not on an abstract Gaussian substitute.

The explicit eigenfunction hypothesis must still be connected to the
physical S14a spectral family before it closes frozen S15d.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory
open HRS.Whole HRS.Whole.Q34 HRS.MS.S111X2
open scoped RealInnerProductSpace
namespace HRS.MS.R26T3

theorem s15d_susceptibility_on_physical_eigenfunctions
    {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    {g : HRS.Euc d → ℝ}
    {K : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ} {Mg : ℝ}
    (hK : KRep g μ K Mg) {θ : ℝ} (hθ : 0 ≤ θ)
    (lam : ℕ → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (e : ℕ → HRS.Euc d → ℝ)
    (he : ∀ j, HRS.Whole.MemL2Zero μ (e j))
    (hon : ∀ i j, ∫ x, e i x * e j x ∂μ =
      if i = j then 1 else 0)
    (heig : ∀ j, K (s111x2_cl (he j).1) =
      lam j • s111x2_cl (he j).1)
    (i j : ℕ) :
    HRS.Whole.susceptibilityCov g μ θ (e i) (e j) =
      if i = j then (1 + θ * lam j)⁻¹ else 0 := by
  have hRep : ∀ k, ((s111x2_cl (he k).1 : Lp ℝ 2 μ) : HRS.Euc d → ℝ) =ᵐ[μ] e k := by
    intro k
    have h := (s111x2_cl_ae (he k).1).symm
    have hz : HRS.Whole.pair μ (e k) = 0 := (he k).2
    have hp : HRS.Whole.projMean μ (e k) = e k := by
      funext x
      simp [HRS.Whole.projMean, hz]
    simpa only [hp] using h
  have hOrth : ∀ a b,
      inner ℝ (s111x2_cl (he a).1) (s111x2_cl (he b).1) =
        if a = b then 1 else 0 := by
    intro a b
    rw [lp_inner]
    calc
      (∫ x, (s111x2_cl (he a).1 : Lp ℝ 2 μ) x *
        (s111x2_cl (he b).1 : Lp ℝ 2 μ) x ∂μ) =
          ∫ x, e a x * e b x ∂μ := by
            apply integral_congr_ae
            filter_upwards [hRep a, hRep b] with x hxa hxb
            rw [hxa, hxb]
      _ = _ := hon a b
  rw [s111x2_susc_eq hK hθ (he i).1 (he j).1]
  exact s15d_positive_resolvent_eigenfamily_covariance
    hK.posOp hθ lam hlam (fun k => s111x2_cl (he k).1)
    heig hOrth i j

#print axioms s15d_susceptibility_on_physical_eigenfunctions

end HRS.MS.R26T3
