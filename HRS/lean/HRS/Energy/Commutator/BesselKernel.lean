import HRS.Energy.Commutator.Basic

/-!
# Route H (sub-Coulomb `0 ≤ s < d-2`), packets H1-H2: Bessel truncation of the periodic Riesz kernel

Source: `[HCRS]` Lemma 2.1, Lemma 2.2, Lemma 2.5 (Bessel potentials), Prop. 2.9 (all with the scaling
function `φ = G_a`, `Ĝ_a(ξ) = ⟨2πξ⟩^{-a}`), `a = d+1` (the exponent of the norm `‖·‖_*`:
`2d/(a-2) = 2d/(d-1)`, `a/2 = (d+1)/2`).

The wavelet-type (Mellin) representation `g = c ∫_0^∞ t^{d-s} φ_t dt/t` becomes, on the torus, an
identity between *Fourier coefficients*: `φ_t` has the torus symbol `besselSym d t k =
⟨2π t k⟩^{-(d+1)}` (periodisation of `t^{-d}G_a(·/t)`, Poisson), and
`∫_0^∞ t^{d-s-1} ⟨2πtk⟩^{-a} dt = (2π|k|)^{s-d} B` with `B = besselNorm d s` (substitution
`u = 2π|k|t`).  Truncating `t ≥ η` gives the positive-definite kernel `g_η`
(`truncCoeff ≥ 0`, summable because `a > d`: `truncCoeff ≲ η^{-s-1}|k|^{-(d+1)}`), bounded by
`g_η(0) ≲ η^{-s}` (`s > 0`) resp. `-log η + O(1)` (`s = 0`, **coefficient exactly 1**, from
`periodicRiesz_local_singularity`/`periodicLog_local_singularity`), and `f_η = g - g_η` is the
near-field remainder.

**Torus differences with `[HCRS]`** (the paper says "mutatis mutandis"):
1. *Zero mode.*  Euclidean `f_η^{ℝ^d} = c∫_0^η t^{d-s}φ_t dt/t ≥ 0` has `∫ f_η^{ℝ^d} = c' η^{d-s} ≠ 0`,
   while `ĝ(0) = ĝ_η(0) = 0` on the torus, so `f_η^{𝕋} = ∑_m f_η^{ℝ^d}(·+m) - c' η^{d-s}` is *not*
   nonnegative: `f_η ≥ -C η^{d-s}` (`fEta_ge`).  All near-field estimates acquire an additive
   `O(η^{d-s})`, which is exactly the allowed error `Λ λ^{d-s}` (`η = θ_* λ`).
2. *Periodisation.*  `φ_t^{per} = ∑_m φ_t(·+m)` converges for every `t > 0` (exponential decay of
   `G_a`); estimates for `|x| ≤ 1/2` are those of `ℝ^d` plus smooth bounded corrections.
3. *Normalisation* of `rieszConst`: `g(x) = |x|^{-s} + smooth` (`s > 0`), `-log|x| + smooth` (`s = 0`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator

variable {d : ℕ} {s : ℝ}

/-- The Bessel exponent `a = d + 1`. -/
def besselA (d : ℕ) : ℝ := (d : ℝ) + 1

/-- The torus symbol `⟨2πtk⟩^{-a}` of the scaled Bessel potential `φ_t`. -/
def besselSym (d : ℕ) (t : ℝ) (k : Lattice d) : ℝ :=
  (1 + 4 * Real.pi ^ 2 * t ^ 2 * Lattice.enorm k ^ 2) ^ (-besselA d / 2)

/-- `B = ∫_0^∞ u^{d-s-1} (1 + u²)^{-a/2} du`. -/
def besselNorm (d : ℕ) (s : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), u ^ ((d : ℝ) - s - 1) * (1 + u ^ 2) ^ (-besselA d / 2)

/-- Fourier coefficient of the truncated kernel `g_η = (c/B) ∫_η^∞ t^{d-s} φ_t dt/t`
(`0` at `k = 0`). -/
def truncCoeff (d : ℕ) (s η : ℝ) (k : Lattice d) : ℝ :=
  if k = 0 then 0
  else rieszConst d s / besselNorm d s * ∫ t in Ioi η, t ^ ((d : ℝ) - s - 1) * besselSym d t k

/-- The truncated (bounded, positive-definite) kernel `g_η`. -/
def gEta (d : ℕ) (s η : ℝ) (x : Torus d) : ℝ := ∑' k : Lattice d, truncCoeff d s η k * Torus.cosMode k x

/-- The near-field remainder `f_η = g - g_η` (for `x ≠ 0`). -/
def fEta (d : ℕ) (s η : ℝ) (x : Torus d) : ℝ := periodicRiesz d s x - gEta d s η x

/-- **H1.1.**  `B > 0` and the Mellin identity `ĝ(k) = (c/B) ∫_0^∞ t^{d-s-1} ⟨2πtk⟩^{-a} dt`
(`k ≠ 0`; `u = 2π|k|t`, convergence at `∞` since `a > d - s`, at `0` since `s < d`). -/
theorem besselNorm_pos (hs0 : 0 ≤ s) (hsd : s < d) : 0 < besselNorm d s := by
  sorry

theorem rieszCoeff_eq_bessel (hs0 : 0 ≤ s) (hsd : s < d) (k : Lattice d) (hk : k ≠ 0) :
    rieszCoeff d s k =
      rieszConst d s / besselNorm d s * ∫ t in Ioi (0 : ℝ), t ^ ((d : ℝ) - s - 1) * besselSym d t k := by
  sorry

/-- **H1.2 (positive definiteness and decay).**  `0 ≤ ĝ_η(k) ≤ ĝ(k)` and
`ĝ_η(k) ≤ C η^{-s-1} |k|^{-(d+1)}` for `k ≠ 0`, `0 < η ≤ 1`; hence the series `g_η` converges
absolutely and uniformly (`a > d`) and `g_η ≥ 0` in the sense of positive definiteness. -/
theorem truncCoeff_bounds (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ k : Lattice d,
      0 ≤ truncCoeff d s η k ∧ truncCoeff d s η k ≤ rieszCoeff d s k ∧
      (k ≠ 0 → truncCoeff d s η k ≤ C * η ^ (-s - 1) * Lattice.enorm k ^ (-((d : ℝ) + 1))) := by
  sorry

theorem summable_truncCoeff (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {η : ℝ} (hη : 0 < η) :
    Summable fun k : Lattice d => truncCoeff d s η k := by
  sorry

/-- **H2.1 (value at the origin; `[HCRS] Lemma 2.2 (1)`).**  `s > 0`: `g_η(0) ≍ η^{-s}`;
`s = 0`: `g_η(0) = -log η + O(1)` *with coefficient exactly one*, which is the origin of the
coefficient `1/(2dN)` of `log(NΛ)` in `o_N`. -/
theorem gEta_zero_pos (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ η : ℝ, 0 < η → η ≤ 1 →
      C₁ * η ^ (-s) ≤ gEta d s η 0 ∧ gEta d s η 0 ≤ C₂ * η ^ (-s) := by
  sorry

theorem gEta_zero_log (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 4 → |gEta d 0 η 0 + Real.log η| ≤ C := by
  sorry

/-- **H2.2 (near-field remainder is bounded below; torus replacement of `f_η ≥ 0`).** -/
theorem fEta_ge (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 4 → ∀ x : Torus d, x ≠ 0 →
      -(C * η ^ ((d : ℝ) - s)) ≤ fEta d s η x := by
  sorry

/-- **H2.3 (`|x||∇f_η| ≲ f_{2η}`; `[HCRS] Lemma 2.2 (6)` with `c = 1/2`, using
`|x||∇G_a(x)| ≲ G_a(x/2)`, Lemma 2.5 (2.29)).**  The two constants are *independent*: on the torus
`f_{2η} = (periodised ℝ^d profile) - c η^{d-s}` is negative away from `0` (e.g. `d=3, s=0, x = e_1/2`), so a
single `C(f_{2η} + η^{d-s})` would be false; the true statement is `|x||∇f_η| ≲ C·f^{per}_{2η}`
with `f^{per}_{2η} = f_{2η} + m_{2η}`, `m_{2η} ≍ η^{d-s}`, i.e. `C f_{2η} + C m η^{d-s}`.  `g_η` is smooth off the origin (symbol of order
`-a`), so `∇f_η` makes sense there. -/
theorem gEta_smoothOffZero (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {η : ℝ} (hη : 0 < η) :
    KernelGrad.IsSmoothOffZero (gEta d s η) := by
  sorry

theorem fEta_grad_comparison (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C C' : ℝ, 0 ≤ C ∧ 0 ≤ C' ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 8 → ∀ x : Torus d, x ≠ 0 →
      KernelGrad.tdist x 0 * ‖Torus.grad (fEta d s η) x‖ ≤
        C * fEta d s (2 * η) x + C' * η ^ ((d : ℝ) - s) := by
  sorry

/-- **H2.4 (convolution bounds, `[HCRS] Lemma 2.10` with `p = ∞`).**  For `ρ ≤ Λ`:
`|f_η * ρ| ≤ C Λ η^{d-s}` and `(|x||∇f_η|) * ρ ≤ C Λ η^{d-s}`, uniformly in the point. -/
theorem fEta_conv_bound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 8 → ∀ (ρ : Torus d → ℝ) (Λ : ℝ), IsProbDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ x : Torus d,
        |∫ y, fEta d s η (x - y) ∂(withDensityReal ρ)| ≤ C * Λ * η ^ ((d : ℝ) - s) ∧
        ∫ y, KernelGrad.tdist x y * ‖Torus.grad (fEta d s η) (x - y)‖ ∂(withDensityReal ρ) ≤
          C * Λ * η ^ ((d : ℝ) - s) := by
  sorry

end HRS.Commutator
