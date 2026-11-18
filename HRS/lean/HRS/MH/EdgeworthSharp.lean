import HRS.Main.HeadlineEdgeworth

/-!
# Sharpness of the root-`N` rate: proof of `HRS.Main.edgeworth_sharpness`

The first Edgeworth correction `c = (1/6) E⟨D³Φ(Z), 𝒦_{a,T}⟩` is bounded by
`√N · d_5(ζ_N, Z) + ε_N` for every `N ≥ 2` (Theorem 2.13 applied to the test function `Φ`
and the bound `|∫Φ d(P - Q)| ≤ d_5(P, Q)` on the `C_b^5` unit ball), and `ε_N → 0`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.EdgeworthSharpP

open HRS HRS.Main

theorem edgeworth_sharpness_proof : type_of% @HRS.Main.edgeworth_sharpness := by
  intro d S β₀ m T hE hT K ε hK a ha ν hν Ω' _ P' _ Z₀ Z hZ Φ hΦ Ω _ P _ X₀ W X hflow hfilt hinit
  -- the first correction, as a real number
  set c : ℝ := (1 / 6) * ∫ ω, ((K a : projTensor (PathSpace d m T) 3) :
      TensorDual (PathSpace d m T) 3) (iteratedFDeriv ℝ 3 Φ (windowPath m T a Z ω)) ∂P' with hc
  -- a triangle-type inequality
  have key : ∀ (x c e : ℝ), |x - c| ≤ e → |c| - e ≤ |x| := by
    intro x c e h
    have h' := abs_sub_abs_le_abs_sub c x
    rw [abs_sub_comm c x] at h'
    linarith
  have hbound : ∀ N : ℕ, 2 ≤ N →
      |c| - ε N ≤ Real.sqrt N * smoothDist 5 (law (P N) (windowZeta m T a (P N) (X N)))
        (law P' (windowPath m T a Z)) := by
    intro N hN
    have h1 := hK.expansion a ha N hN (P N) (X₀ N) (W N) (X N) (hflow N hN) (hfilt N hN)
      (hinit N hN) ν hν P' Z₀ Z hZ Φ hΦ
    have h2 : |∫ z, Φ z ∂(law (P N) (windowZeta m T a (P N) (X N))) -
        ∫ z, Φ z ∂(law P' (windowPath m T a Z))| ≤
        smoothDist 5 (law (P N) (windowZeta m T a (P N) (X N))) (law P' (windowPath m T a Z)) :=
      abs_integral_sub_le_smoothDist hΦ _ _
    have hsq : (0 : ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg _
    have hx := key _ _ _ h1
    rw [abs_mul (Real.sqrt N), abs_of_nonneg hsq, ← hc] at hx
    have hm := mul_le_mul_of_nonneg_left h2 hsq
    linarith
  have hlim : Tendsto (fun N : ℕ => ENNReal.ofReal (|c| - ε N)) atTop (𝓝 (ENNReal.ofReal |c|)) := by
    apply ENNReal.tendsto_ofReal
    have h0 := (tendsto_const_nhds (x := |c|)).sub hK.eps_tendsto
    rw [sub_zero] at h0
    exact h0
  rw [← hlim.liminf_eq]
  exact liminf_le_liminf (Filter.eventually_atTop.2 ⟨2, fun N hN => ENNReal.ofReal_le_ofReal (hbound N hN)⟩)

end HRS.MH.EdgeworthSharpP
