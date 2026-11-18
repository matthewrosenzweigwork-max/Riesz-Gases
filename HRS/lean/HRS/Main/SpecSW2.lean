import HRS.PDE.EnergyR2Q
import HRS.Energy.WeakReference

/-!
# Statements SPECSW2: torus gradient clause of Lemma C.6, pinned/cavity clause of Lemma 5.6

Both statements are `sorry`-proved specifications (packet SPECSW2); the sources are

* Lemma C.6 `M:B:lem:sqrt-lipschitz` (TeX L12311-12313), gradient clause on the torus;
* Lemma 5.6 `M:N:lem:weak` (TeX L6156-6172), the sentence "These bounds also hold after one pin and
  for the cavity law retaining pair coefficient `τβ/N` and one-body field `τβ q*μ`", which the
  existing `HRS.weak_reference_estimates` (HRS/Energy/WeakReference.lean) omits.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.Main.SpecSW2

/-! ## Lemma C.6, gradient-norm clause on the torus -/

section Sqrt

variable {d : ℕ}

/-- **Lemma C.6 `M:B:lem:sqrt-lipschitz`, gradient clause on `𝕋^d`** (TeX L12311-12313: "If
`0 ≤ a ∈ C^{1,1}(𝕋^d)`, then `√a` is Lipschitz with `‖∇√a‖_{L^∞} ≤ √(‖∇^{⊗2}a‖_{L^∞}/2)`").

The Lipschitz clause is `HRS.PDE.R2Aux.sqrt_isLipschitz` (torus) and `HRS.sqrt_lipschitz` (Euclidean);
this theorem states the remaining claim `‖∇√a‖_{L^∞} ≤ √(L/2)`.  The hypotheses are exactly those of
`sqrt_isLipschitz`: `L` is a real number with `0 ≤ L`, `a ≥ 0` everywhere, and `IsC11 L a` (`a ∈ C¹`
with `∇a` `L`-Lipschitz on the lift, i.e. `‖∇^{⊗2}a‖_{L^∞} ≤ L`; the source quantity `‖∇^{⊗2}a‖_∞` is
the smallest such `L`, so quantifying over all admissible `L` is equivalent and no hypothesis is
added).  `L` and `a` are quantified before the conclusion, `0 ≤ L` is the only range restriction (it
is forced for `IsC11 L a` to be meaningful through `Real.toNNReal`, and is needed for `√(L/2)`).

Representation of `∇√a`.  `√a` is only Lipschitz, not differentiable at the zeros of `a`, so the
gradient is the almost-everywhere gradient of the periodic lift `f = lift √a` on `ℝ^d` (Rademacher),
which for Lipschitz `f` coincides with the weak gradient.  The conclusion has three conjuncts:
(i) at *every* point where `f` is differentiable, `‖∇f(x)‖ ≤ √(L/2)` (operator norm of `fderiv`, equal
to the Euclidean norm of the gradient); (ii) `f` is differentiable almost everywhere; (iii) the
essential supremum of `‖fderiv f‖` w.r.t. Lebesgue measure on `ℝ^d` is `≤ √(L/2)`, i.e. the
`L^∞` bound of the source (the lift is periodic, so a.e. on `ℝ^d` is a.e. on `𝕋^d`).

Junk-value check.  `fderiv` is `0` where `f` is not differentiable, so (iii) alone could hold
vacuously on the non-differentiability set; conjunct (ii) shows that set is null, hence (iii) is the
genuine `L^∞` norm of the a.e. gradient, and (i) is stated only under `DifferentiableAt`.  No division
(`L / 2` has a numeral denominator), `Real.sqrt` is applied to the nonnegative `a x` and `L / 2`
(`L = 0` gives `a` constant and the bound `0`, which is correct), no measure map, no Bochner or lower
integral, no `limUnder`, `d : ℕ` arbitrary (`d = 0` is trivial and true), `Type` levels are
irrelevant. `eLpNormEssSup` is in `ℝ≥0∞` and the comparison uses `ENNReal.ofReal` of a nonnegative
real. -/
theorem torus_sqrt_gradient_le {a : Torus d → ℝ} {L : ℝ} (hL : 0 ≤ L) (ha : ∀ x, 0 ≤ a x)
    (hC11 : PDE.IsC11 L a) :
    (∀ x : Euc d, DifferentiableAt ℝ (Torus.lift fun y => Real.sqrt (a y)) x →
        ‖fderiv ℝ (Torus.lift fun y => Real.sqrt (a y)) x‖ ≤ Real.sqrt (L / 2)) ∧
    (∀ᵐ x : Euc d ∂volume, DifferentiableAt ℝ (Torus.lift fun y => Real.sqrt (a y)) x) ∧
    eLpNormEssSup (fun x => fderiv ℝ (Torus.lift fun y => Real.sqrt (a y)) x) volume
      ≤ ENNReal.ofReal (Real.sqrt (L / 2)) := by
  sorry

end Sqrt

/-! ## Lemma 5.6, pinned and cavity clause -/

section Weak

variable {d : ℕ}

/-- Unnormalised density, with respect to `μ^{⊗n}`, of the free coordinates of
`ℝ_{N,τ}` with `N = n + 1` after pinning coordinate `p` at the value `y`: the weight
`pairWeight q (n+1) b μ` of the full ensemble (`b = τβ`, so `pairWeight = exp(-τβ N F_N^q)`)
evaluated at the configuration obtained by inserting `y` at position `p` into the free
configuration `Z`.  Its normalised version is the conditional law of the other `n` coordinates given
the pin, and by `N:eq:weak-spec` (TeX L6177-6180) it equals, up to a constant factor, the specification
with one-body field `τβ q*μ - (τβ/N) q(·,y)` and pair coefficient `τβ/N`. -/
def pinnedWeight (q : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (b : ℝ) (n : ℕ)
    (p : Fin (n + 1)) (y : Torus d) (Z : Config d n) : ℝ≥0∞ :=
  pairWeight q (n + 1) b μ (Fin.insertNth (α := fun _ => Torus d) p y Z)

/-- Unnormalised density, with respect to `μ^{⊗n}`, of the **cavity law** (TeX L6202-6204,
"deleting one particle, while retaining the same denominator `N` in the interaction", and L6206-6209):
`n` coordinates, pair coefficient `b/N` and one-body field `b · (q*μ)`, i.e.
`exp(b ∑ᵢ ∫ q(Zᵢ,y) μ(dy) - (b/N) ∑_{i<j} q(Zᵢ,Zⱼ))` (the pair sum is written `½ ∑_{i≠j}`, as in
`pairWeight`).  Here `N` is a separate parameter (in the theorem `N = n + 1`), `b = τβ`.
`∫ q(z,y) μ(dy)` is a Bochner integral; under the row bound of the theorem it is the honest integral of
a nonnegative integrable function. -/
def cavityWeight (q : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (b : ℝ) (N : ℕ) {n : ℕ}
    (Z : Config d n) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (b * ∑ i, ∫ y, q (Z i) y ∂μ
    - (b / N) * ((1 / 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, q (Z i) (Z j))))

/-- The two Dobrushin-type conclusions of Lemma 5.6 for a weight `W` on `n` coordinates:
the one-coordinate conditional laws `siteKernel μ W i x` are bounded by `C μ`, and there are
interdependence coefficients `c i j ∈ [0, κ]` with row and column sums `< 1/2` such that changing the
`j`-th coordinate of the conditioning configuration changes the `i`-th conditional law, evaluated on any
measurable set, by at most `c i j` (for `i ≠ j`; the diagonal coefficients are not constrained and may
be taken `0`).  `κ` will be `C τ β a / N`. -/
def WeakConditionalBounds (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {n : ℕ}
    (W : Config d n → ℝ≥0∞) (C κ : ℝ) : Prop :=
  (∀ (i : Fin n) (x : Config d n), External.siteKernel μ W i x ≤ ENNReal.ofReal C • μ) ∧
  ∃ c : Fin n → Fin n → ℝ, (∀ i j, 0 ≤ c i j ∧ c i j ≤ κ) ∧
    (∀ i, ∑ j, c i j < 1 / 2) ∧ (∀ j, ∑ i, c i j < 1 / 2) ∧
    ∀ i j : Fin n, i ≠ j → ∀ x y : Config d n, (∀ k, k ≠ j → x k = y k) →
      ∀ S : Set (Torus d), MeasurableSet S →
        |(External.siteKernel μ W i x).real S - (External.siteKernel μ W i y).real S| ≤ c i j

/-- **Lemma 5.6 `M:N:lem:weak`, the pinned and cavity clause** (TeX L6156-6172: "These bounds also hold
after one pin and for the cavity law retaining pair coefficient `τβ/N` and one-body field `τβ q*μ`";
the proof, TeX L6174-6269, states at L6204 that "these conclusions are uniform in the pin").  "These bounds" are
the first two sentences of the lemma: the one-coordinate conditional densities are bounded by `Cμ`, the
interdependence coefficients are at most `C τ β a / N`, and the row and column sums are below `1/2`.
The other clauses (`N:eq:weak-marginal`, `N:eq:weak-pi`) concern the unpinned law only and are in
`HRS.weak_reference_estimates`.

Parameters.  Everything before `∃ a₀ C` and the hypotheses on `ρ, q, a` are verbatim those of
`HRS.weak_reference_estimates`; `a₀` and `C` are chosen after `(d, s, c_*, β_±, c₀, Λ, A)` and before
`ρ, q, a, N, β, τ`, and in particular before the pin position `p` and pin value `y`, which are
quantified last (uniformity in the pin).  Because every conclusion is monotone in `C` (the row/column
sums are `< 1/2` for a witness `c` independent of `C`) and in `a₀`, the constants of this theorem and of
`weak_reference_estimates` can be combined by taking the maximum of the `C`'s and the minimum of the
`a₀`'s.  `N = n + 1` with `n ≥ 1` (that is, `2 ≤ N` as in `weak_reference_estimates`); the pinned ensemble
has `n = N - 1` free coordinates and the pin is inserted at any position `p : Fin N` (`pinnedWeight`,
whose normalised law is the conditional law of the other coordinates, derived from `pairWeight` itself,
not from a transcribed formula); the cavity ensemble has the same `n = N - 1` free coordinates, the pair
coefficient `τβ/N` with the original denominator `N = n + 1`, and the one-body field `τβ q*μ`
(`cavityWeight`).  The coefficient bound is `C τ β a / (n+1)` and the conditional density bound is `C μ`,
exactly as in the unpinned statement; the "row and column sums below `1/2`" are stated as a witness
matrix `c` of coefficients (`WeakConditionalBounds`) instead of the proxy `C τ β a < 1/2` used in the
unpinned Lean statement.

Junk-value check.  `1/2` and `a / (n+1)` have nonzero denominators (`n ≥ 1`).  `siteKernel μ W i` is a
`Kernel.withDensity`, which is `0` for a non-measurable density; here the density is
`z ↦ W (update x i z) * (∫⁻ W (update x i ·) dμ)⁻¹`, and `W` is measurable (`q` measurable, and the
row integral `x ↦ ∫ q(x,y) dμ(y)` of a measurable nonnegative kernel is measurable), the normaliser is
positive (the weights are `ofReal exp > 0`) and finite (the exponent is bounded above, using `q ≥ 0`
and the row bound), so the kernel is the true conditional law, not a junk value.  The row integral in
`cavityWeight` is a Bochner integral of a nonnegative function with `∫⁻ ofReal q ≤ ofReal a < ∞`
(hypothesis `hrow`), hence integrable.  No `Measure.map` of a non-measurable map occurs (the
bounds are about the kernels, not marginals), no lower integral, no `limUnder`.  `τ = 0` is allowed:
all weights are then constant, every kernel equals `μ`, and the bounds hold with `c = 0`.
`β ∈ [βm, βp]` with `βm > 0` (so `β > 0`).  `Type` universe: all spaces are `Torus d`.
`IsProbabilityMeasure (withDensityReal ρ)` is a hypothesis (as in the unpinned statement), which
makes `siteKernel` available. -/
theorem weak_reference_pinned_cavity (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (cstar : ℝ) (hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + cstar)
    (βm βp : ℝ) (hβm : 0 < βm) (c₀ : ℝ) (hc₀ : 0 < c₀) (Λ : ℕ → ℝ) (A : ℝ) :
    ∃ a₀ C : ℝ, 0 < a₀ ∧
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → ∀ [IsProbabilityMeasure (withDensityReal ρ)],
        Torus.IsSmooth ρ → (∀ x, c₀ ≤ ρ x) →
        (∀ k : ℕ, Torus.cbNorm k ρ ≤ Λ k) →
      ∀ q : Torus d → Torus d → ℝ, Measurable (Function.uncurry q) → (∀ x y, q x y = q y x) →
        (∀ x y, 0 ≤ q x y) → (∀ x y, q x y ≤ A * (periodicRiesz d s (x - y) + cstar)) →
      ∀ a : ℝ, 0 ≤ a → a < a₀ →
        (∀ x, ∫⁻ y, ENNReal.ofReal (q x y) ∂(withDensityReal ρ) ≤ ENNReal.ofReal a) →
      ∀ n : ℕ, 1 ≤ n → ∀ β ∈ Set.Icc βm βp, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        (∀ (p : Fin (n + 1)) (y : Torus d),
          WeakConditionalBounds (withDensityReal ρ)
            (pinnedWeight q (withDensityReal ρ) (τ * β) n p y) C (C * τ * β * a / ((n + 1 : ℕ) : ℝ))) ∧
        WeakConditionalBounds (withDensityReal ρ)
          (cavityWeight q (withDensityReal ρ) (τ * β) (n + 1) (n := n)) C
          (C * τ * β * a / ((n + 1 : ℕ) : ℝ)) := by
  sorry

end Weak

end HRS.Main.SpecSW2
