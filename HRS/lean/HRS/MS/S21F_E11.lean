import HRS.MS.S81G_Couple

/-!
# S21F, packet R26-T3.E11: pathwise cutoff identification without a filtration premise on `X`

This is `s81g_ident` (S81G, merged) with the diffusion coefficient written `D.invβ`; the deterministic body
of `sb1_ident` uses `IsWholeFilteredSolution` only for the two noise fields supplied here by `IsBrownianFiltration`
and the coordinate identification.  No adaptedness or progressive measurability of `X` is used.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal
open HRS HRS.Whole

namespace HRS.MS.R26T3

theorem r26t3_cutoff_identification {d N : ℕ} (D : WholeDyn d) (hM : D.M = -1)
    {B S : ℝ} (hV : HRS.MS.MfeConf.Sb1Pot D.V B) (hS : 0 < S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X₀ : Ω → EucConfig d N}
    {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : IsWholeStrongSolution P D S X₀ W X) (hW' : IsBrownianFiltration P ℱ W')
    (hcoord : ∀ᵐ ζ ∂P, ∀ t i j, W' t ζ (i,j) = W t ζ i j)
    {gM : ℕ → Euc d → ℝ}
    (hgM : ∀ M : ℕ, HRS.MP.SelfSimP4.IsP4Kernel d D.s (1 / ((M : ℝ) + 1)) (gM M))
    {Ys : ℕ → ℝ → Ω → EucConfig d N}
    (hYs : ∀ M : ℕ, IsAdditiveSDESolution P (HRS.MP.SelfSimP4Impl.p4r_shiftFil ℱ) W'
      (fun _ => HRS.MS.MfeConf.sb1DriftM D (gM M) N)
      (HRS.MP.SelfSimP4Impl.p4r_sigma d N D.invβ) (X 0) (fun _ => ⊤) (Ys M)) :
    ∀ᵐ ζ ∂P, ∀ᶠ M : ℕ in atTop, ∀ t : ℝ≥0, (t : ℝ) ≤ S → Ys M t ζ = X t ζ :=
  HRS.MS.S81G.s81g_ident D hM hV hS hX hW' hcoord hgM hYs

end HRS.MS.R26T3
