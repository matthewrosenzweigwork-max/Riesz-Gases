import HRS.Energy.StaticLimitEnergy
import HRS.Energy.Modulated

/-!
# The feature map `O:eq:feature` and the bounded-diagonal identity `O:eq:bounded-diagonal`

Statements only (every theorem ends in `sorry` except the two coordinate bounds that make `featureMap` well defined);
relocated from `HRS/SA/Drafts/SAD2.lean` after the independent review recorded in `docs/ISSUES.md` and subsequent approval.
Row `M:prose:L5521-5558` (TeX L5521-5538).

The printed real feature map (one frequency of each pair `{k,-k}`, cos/sin coordinates with weight `√(2 ĝ(k))`) and the
printed identity `N F_N^g(X_N,μ) = ½‖N^{-1/2} ∑ Z(x_i)‖² - ½ g(0)`, `Z = Ψ - μ(Ψ)`.  `HRS.StaticLimitAux.energy_identity`
already proves the identity for the redundant full-lattice feature space; the declarations below state the printed form.
Any other choice of one representative from each pair gives an isometric map.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS

variable {d : ℕ}

section FeatureMap

/-- The index set of the printed feature map `O:eq:feature`: one cos coordinate and one sin
coordinate for every frequency `k` of the (lexicographically) positive half-lattice, i.e. one
element of each pair `{k,-k}` of nonzero frequencies ("Choose one element from each pair"). -/
abbrev HalfIdx (d : ℕ) : Type := {k : Lattice d // Lattice.IsPosHalf k} ⊕ {k : Lattice d // Lattice.IsPosHalf k}

/-- Coordinate functions of the printed feature map
`Ψ(x) = (√(2 ĝ(k)) cos(2π k·x), √(2 ĝ(k)) sin(2π k·x))_k`, `ĝ = a`. -/
def featCoord (a : Lattice d → ℝ) : HalfIdx d → Torus d → ℝ
  | Sum.inl k, x => Real.sqrt (2 * a k.1) * Torus.cosMode k.1 x
  | Sum.inr k, x => Real.sqrt (2 * a k.1) * Torus.sinMode k.1 x

/-- The dominating summable weights `2 ĝ(k)`. -/
def featWeight (a : Lattice d → ℝ) : HalfIdx d → ℝ
  | Sum.inl k => 2 * a k.1
  | Sum.inr k => 2 * a k.1

theorem summable_featWeight {a : Lattice d → ℝ} (has : Summable a) :
    Summable (featWeight a) := by
  have h : Summable fun k : {k : Lattice d // Lattice.IsPosHalf k} => 2 * a k.1 :=
    (has.comp_injective Subtype.val_injective).mul_left 2
  exact Summable.sum (f := featWeight a) h h

theorem featCoord_sq_le {a : Lattice d → ℝ} (ha0 : ∀ k, 0 ≤ a k) (i : HalfIdx d) (x : Torus d) :
    featCoord a i x ^ 2 ≤ featWeight a i := by
  rcases i with k | k
  · simp only [featCoord, featWeight, mul_pow]
    rw [Real.sq_sqrt (by have := ha0 k.1; linarith)]
    have h := Torus.norm_cosMode_le k.1 x
    rw [Real.norm_eq_abs] at h
    have : Torus.cosMode k.1 x ^ 2 ≤ 1 := by
      have := sq_le_one_iff_abs_le_one _ |>.mpr h
      exact this
    have h2 := ha0 k.1
    nlinarith
  · simp only [featCoord, featWeight, mul_pow]
    rw [Real.sq_sqrt (by have := ha0 k.1; linarith)]
    have h := Torus.norm_sinMode_le k.1 x
    rw [Real.norm_eq_abs] at h
    have : Torus.sinMode k.1 x ^ 2 ≤ 1 := by
      have := sq_le_one_iff_abs_le_one _ |>.mpr h
      exact this
    have h2 := ha0 k.1
    nlinarith

/-- The real separable Hilbert space `ℓ²` of the feature coordinates. -/
abbrev FeatHilbert (d : ℕ) : Type := lp (fun _ : HalfIdx d => ℝ) 2

/-- The feature map `Ψ : 𝕋^d → ℓ²` of `O:eq:feature`, for a nonnegative summable symbol
`ĝ = a` (`a ≥ 0`, `∑ a < ∞` are exactly what makes the coordinates square-summable). -/
def featureMap {a : Lattice d → ℝ} (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) (x : Torus d) :
    FeatHilbert d :=
  StaticLimitAux.mkLp (fun i => featCoord a i x) (featWeight a) (summable_featWeight has)
    (fun i => featCoord_sq_le ha0 i x)

/-- A spectral symbol in the sense of `O:eq:negative-symbol`: nonnegative, summable, even
(`ĝ(-k) = ĝ(k)`, so that `g` is real and even) and with vanishing zero mode `ĝ(0) = 0`. -/
structure IsSpectralSymbol (a : Lattice d → ℝ) : Prop where
  nonneg : ∀ k, 0 ≤ a k
  summable : Summable a
  even : ∀ k, a (-k) = a k
  zero : a 0 = 0

/-- The negative-exponent symbol `O:eq:negative-symbol` is a spectral symbol (`s < 0`, `c > 0`). -/
theorem isSpectralSymbol_negSpectralCoeff (d : ℕ) {s c : ℝ} (hs : s < 0) (hc : 0 < c) :
    IsSpectralSymbol (negSpectralCoeff d s c) := by
  exact ⟨fun k => negSpectralCoeff_nonneg d s hc.le k,
    summable_negSpectralCoeff d hs c,
    negSpectralCoeff_neg d s c,
    by simp [negSpectralCoeff]⟩

/-- **`O:eq:feature`, first sentence** (M L5529-5532): `⟨Ψ(x),Ψ(y)⟩ = g(x-y)` where
`g = ∑_k ĝ(k) cos(2π k·x)` (`StaticLimitAux.specKernel`). -/
theorem featureMap_inner {a : Lattice d → ℝ} (hsym : IsSpectralSymbol a) (x y : Torus d) :
    inner ℝ (featureMap hsym.nonneg hsym.summable x) (featureMap hsym.nonneg hsym.summable y) =
      StaticLimitAux.specKernel a (x - y) := by
  sorry

/-- **`O:eq:feature`, second claim** (M L5532): `‖Ψ(x)‖² = g(0)`. -/
theorem featureMap_norm_sq {a : Lattice d → ℝ} (hsym : IsSpectralSymbol a) (x : Torus d) :
    ‖featureMap hsym.nonneg hsym.summable x‖ ^ 2 = StaticLimitAux.specKernel a 0 := by
  sorry

/-- **`O:eq:feature`, third claim** (M L5532-5533): `Ψ` is continuous. -/
theorem continuous_featureMap {a : Lattice d → ℝ} (hsym : IsSpectralSymbol a) :
    Continuous (featureMap hsym.nonneg hsym.summable) := by
  sorry

/-- **`O:eq:feature`, "bounded"** (M L5532-5533): `sup_x ‖Ψ(x)‖ < ∞`. -/
theorem bounded_featureMap {a : Lattice d → ℝ} (hsym : IsSpectralSymbol a) :
    ∃ B : ℝ, ∀ x : Torus d, ‖featureMap hsym.nonneg hsym.summable x‖ ≤ B := by
  sorry

/-- `Ψ` is Bochner integrable against every probability measure, so that
`μ(Ψ) = ∫ Ψ dμ` in `Z = Ψ - μ(Ψ)` is not a junk value. -/
theorem integrable_featureMap {a : Lattice d → ℝ} (hsym : IsSpectralSymbol a)
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    Integrable (featureMap hsym.nonneg hsym.summable) μ := by
  sorry

/-- **`O:eq:bounded-diagonal`, abstract form** (M L5534-5538).  Let `Ψ : 𝕋^d → H` be a continuous
map into a real Hilbert space with `⟨Ψ(x),Ψ(y)⟩ = g(x-y)` for all `x,y`.  Then for every
probability measure `μ`, every `N ≥ 1` and every configuration `X_N`,
`N F_N^g(X_N,μ) = ½‖N^{-1/2} ∑_i (Ψ(x_i) - μ(Ψ))‖² - ½ g(0)`.
The deleted diagonal in `F_N^g` is the original particle diagonal (`modulatedEnergy` sums over
`j ≠ i`).  `N ≥ 1` is necessary: at `N = 0` the left side is `0` and the right side is
`-½ g(0)`. -/
theorem energy_identity_of_feature {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (g : Torus d → ℝ) (Ψ : Torus d → H) (hΨ : Continuous Ψ)
    (hg : ∀ x y : Torus d, inner ℝ (Ψ x) (Ψ y) = g (x - y))
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {N : ℕ} (hN : 1 ≤ N) (X : Config d N) :
    (N : ℝ) * modulatedEnergyKernel g X μ =
      (1 / 2) * ‖(Real.sqrt N)⁻¹ • ∑ i, (Ψ (X i) - ∫ y, Ψ y ∂μ)‖ ^ 2 - (1 / 2) * g 0 := by
  sorry

/-- **`O:eq:bounded-diagonal`, concrete form** (M L5534-5538): the printed identity for the
printed feature map `Ψ` of `O:eq:feature`, with `g = specKernel ĝ` and `Z = Ψ - μ(Ψ)`. -/
theorem energy_identity_featureMap {a : Lattice d → ℝ} (hsym : IsSpectralSymbol a)
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {N : ℕ} (hN : 1 ≤ N) (X : Config d N) :
    (N : ℝ) * modulatedEnergyKernel (StaticLimitAux.specKernel a) X μ =
      (1 / 2) * ‖(Real.sqrt N)⁻¹ •
          ∑ i, (featureMap hsym.nonneg hsym.summable (X i) -
                  ∫ y, featureMap hsym.nonneg hsym.summable y ∂μ)‖ ^ 2
        - (1 / 2) * StaticLimitAux.specKernel a 0 := by
  sorry

/-- The same identity for the bounded kernel of `O:sec:negative`
(`g = negSpectralKernel d s c`, `s < 0`, `c > 0`; `O:eq:negative-symbol`). -/
theorem energy_identity_negSpectral {s c : ℝ} (hs : s < 0) (hc : 0 < c)
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {N : ℕ} (hN : 1 ≤ N) (X : Config d N) :
    (N : ℝ) * modulatedEnergyKernel (negSpectralKernel d s c) X μ =
      (1 / 2) * ‖(Real.sqrt N)⁻¹ •
          ∑ i, (featureMap (isSpectralSymbol_negSpectralCoeff d hs hc).nonneg
                  (isSpectralSymbol_negSpectralCoeff d hs hc).summable (X i) -
                ∫ y, featureMap (isSpectralSymbol_negSpectralCoeff d hs hc).nonneg
                  (isSpectralSymbol_negSpectralCoeff d hs hc).summable y ∂μ)‖ ^ 2
        - (1 / 2) * negSpectralKernel d s c 0 := by
  sorry

end FeatureMap

end HRS
