import HRS.MS.GenPathAux15

/-!
# S5.6: Itô integrals depend only on the integrand at times `r ≥ 0`

The `K`-valued noise integrand `empiricalNoiseIntegrand` involves `propagatorW C r t φ`, a `Classical.choose` which is
arbitrary for `r < 0`; it is therefore not (provably) progressively measurable on `ℝ`.  `itoIntegral` (a `Classical.choose`
of `IsItoIntegral`, whose `approx` clause only sees the integrand on `[0,t]`) depends only on the integrand at times
`r ≥ 0` (`s56_isItoIntegral_congr`, `s56_itoIntegral_congr`); `IsHilbertItoIntegral` is phrased through `itoIntegral`
of the coordinate integrands, so a martingale constructed for the truncated integrand `1_{r ≥ 0}Φ` is a martingale for the
frozen integrand (hypothesis `hM` of `orbit_maximal_identification`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Fintype ι]

theorem s56_isItoIntegral_congr (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ι → ℝ)
    {Φ Φ' : ℝ → Ω → ι → ℝ} (h : ∀ r, 0 ≤ r → Φ r = Φ' r) :
    IsItoIntegral P ℱ W Φ = IsItoIntegral P ℱ W Φ' := by
  have hsq : ∀ (Ψ : ℝ → Ω → ι → ℝ) (t : ℝ),
      sqIntegralOn P (fun s ω => Ψ s ω - Φ s ω) t = sqIntegralOn P (fun s ω => Ψ s ω - Φ' s ω) t := by
    intro Ψ t
    unfold sqIntegralOn
    refine lintegral_congr fun ω => ?_
    refine setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    have := h s hs.1
    simp only [this]
  funext M
  apply propext
  constructor
  · rintro ⟨c, a, z, ap⟩
    exact ⟨c, a, z, fun t ht Ψ hΨ => ap t ht Ψ (by simpa only [hsq] using hΨ)⟩
  · rintro ⟨c, a, z, ap⟩
    exact ⟨c, a, z, fun t ht Ψ hΨ => ap t ht Ψ (by simpa only [hsq] using hΨ)⟩

theorem s56_itoIntegral_congr (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ι → ℝ)
    {Φ Φ' : ℝ → Ω → ι → ℝ} (h : ∀ r, 0 ≤ r → Φ r = Φ' r) :
    itoIntegral P ℱ W Φ = itoIntegral P ℱ W Φ' := by
  unfold itoIntegral
  rw [s56_isItoIntegral_congr P ℱ W h]

end HRS.MS.GenPath
