import HRS.Energy.Coercivity
import HRS.Whole.Basic

/-!
# Appendix D: smooth scale truncation of the interaction (Fefferman-de la Llave representation)

Statements only (`sorry` proofs); packet SPEC-D, part D.  Source: `HRS_periodic_main_20261008T010000Z.tex`
(M), Appendix D `B:app:fdl`, L12340-12479:

* Lemma D.1 `M:B:lem:fdl-rep` (L12362-12378): `fdl_rep`;
* Definition D.2 `M:B:def:fdl-truncation` (L12396-12401): `fdlWE`, `fdlWT`, `fdlTruncE`, `fdlTruncT`;
* Lemma D.3 `M:B:lem:fdl-kernel` (L12403-12427): `fdl_kernel_euclid`, `fdl_kernel_torus`;
* Lemma D.4 `M:B:lem:fdl-compare` (L12435-12442): `fdl_compare`, `fdl_compare_reverse_false`;
* Lemma D.5 `M:B:lem:fdl-ito` (L12452-12457): `fdl_ito`;

* Remark D.7 `M:B:rem:fdl-scope` (L12477-12479): `fdl_scope`.

## Representation decisions (to be checked by the orchestrator)

* **The profile `ψ`** (L12360) is fixed but arbitrary: `IsFDLProfile ψ` (radial, `C^∞`, `≥ 0`,
  `supp ψ ⊂ B(0,1/2)`, `ψ > 0` on `B(0,1/4)`), `φ = ψ * ψ` (`fdlPhi`, convolution), `φ_t = t^{-d} φ(·/t)`
  (`fdlPhiScale`).  "Constants `C = C(d,s,j,φ)`" are `∃ C` after `ψ`, `s`, `b`, `j`, before the scale `λ`
  and the point.
* **The constant `b_{d,s}`** is not given a closed form: `IsFDLConst ψ s b` says that `b > 0` makes the
  representations of Lemma D.1 hold (Euclidean and torus).  Lemma D.1 asserts `∃ b, IsFDLConst ψ s b`
  ("there is `b_{d,s} > 0`"); `b` is then unique (it is determined by the normalisation
  `g = |x|^{-s}` resp. `-log|x|`), and the later statements take it as a hypothesis `hb`.
* **Two settings.**  The M-manuscript works on `𝔻 = 𝕋^d` (statements D.2-D.6 on the torus, as the rest of
  `Energy/Coercivity.lean`); Lemma D.1 and the real-space part of Lemma D.3 are also stated on `ℝ^d`
  because the TeX says "on `ℝ^d`" explicitly (Euclidean `g` is `HRS.Whole.rieszKernel`).  NOT stated:
  the Euclidean Fourier items of D.3(iii) (they need distributional Fourier transforms of the
  non-integrable `g` on `ℝ^d`) and `ℝ^d` versions of D.4-D.6.
* **Periodization** `fdlPer f x = ∑_{n ∈ ℤ^d} f(rep x + n)` (a finite sum for compactly supported `f`, so no
  `tsum` junk); `w_λ` on the torus periodizes the short-scale kernels `φ_t` *without* subtracting their
  average (L12376-12377): `fdlWT`.
* **Values at the origin.**  `w_λ(0) = +∞`, which Lean's Bochner integral turns into the junk `0`; every
  statement about `w_λ` excludes `z = 0`.  `g_λ(0)` is defined by continuous extension
  (`limUnder` over the punctured neighbourhood in `fdlTruncE`, `fdlTruncT`); Lemma D.3(ii) asserts the
  smoothness of `g_λ` (so the extension exists), and the bounds at `0` refer to this value.
* **Definition D.2** says `λ ∈ (0,1)`; the formulas make sense for every `λ > 0` and are defined so
  (needed for `η ≤ 2Kλ` in Lemma D.4).  See SUSPECTED ISSUE in `fdl_compare`.
* **The correction `o_N`.**  Lemma D.4 says "after enlarging `C_0` in `H:eq:energy-completion`".  We use the
  exact correction of Proposition 3.34, `oNΛ d s C₀ Λ N` (`o_N(Λ)`, `B:eq:hrs-coercivity-exact-correction`),
  as `Energy/Coercivity.lean` does, with `C₀` chosen *before* `Λ` (depending only on `d, s, φ`); this implies
  the energy-completion form (`Λ`-dependent `C₀`).  `oNΛ` is monotone in `C₀`, so "enlarging" is automatic.
* `F_N = rieszEnergy d s`, `F_{N,η} = fdlEnergy` (modulated energy with the kernel `g_η`).
  "Admissible `μ` with `‖μ‖_∞ ≤ Λ`" is a probability density `ρ` with `ρ ≤ Λ` pointwise
  (`Λ ≥ 1` is then automatic; kept as in `commutator_estimate`), `λ = (NΛ)^{-1/d} = smearScale d N Λ`.
* The off-diagonal pairing `∬_{𝔻²∖△} k d(μ_N - μ)^{⊗2}` is `offDiagPairing` (`Energy/Coercivity.lean`).
* `K = 16` (L12430: "We fix `K := 16` hereafter").
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d : ℕ}

/-! ### The profile, `φ = ψ * ψ`, the scaled kernels -/

/-- The profile of L12360: `ψ ∈ C_c^∞(B(0,1/2); [0,∞))` radial with `ψ > 0` on `B(0,1/4)`. -/
structure IsFDLProfile (ψ : Euc d → ℝ) : Prop where
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ
  nonneg : ∀ x, 0 ≤ ψ x
  support : tsupport ψ ⊆ Metric.ball (0 : Euc d) (1 / 2)
  radial : ∀ x y : Euc d, ‖x‖ = ‖y‖ → ψ x = ψ y
  pos : ∀ x : Euc d, ‖x‖ < 1 / 4 → 0 < ψ x

/-- `φ := ψ * ψ` (convolution on `ℝ^d`; L12360). -/
def fdlPhi (ψ : Euc d → ℝ) : Euc d → ℝ :=
  convolution ψ ψ (ContinuousLinearMap.mul ℝ ℝ) volume

/-- `φ_t := t^{-d} φ(·/t)` (L12360). -/
def fdlPhiScale (ψ : Euc d → ℝ) (t : ℝ) (x : Euc d) : ℝ := (t ^ d)⁻¹ * fdlPhi ψ (t⁻¹ • x)

/-- The Fourier transform `ψ̂(ξ) = ∫ ψ(x) e^{-2πi ξ·x} dx`; real because `ψ` is radial (even), so it is the
cosine transform `∫ ψ(x) cos(2π ξ·x) dx`.  Then `φ̂ = ψ̂²` (L12360). -/
def fdlPsiHat (ψ : Euc d → ℝ) (ξ : Euc d) : ℝ :=
  ∫ x, ψ x * Real.cos (2 * Real.pi * inner ℝ ξ x)

/-- Periodization `P f (x) = ∑_{n ∈ ℤ^d} f(x + n)` of a function on `ℝ^d` to the torus
(`P φ_t` of L12369; a finite sum for compactly supported `f`). -/
def fdlPer (f : Euc d → ℝ) (x : Torus d) : ℝ :=
  ∑' n : Lattice d, f (Torus.rep x + Lattice.toEuc n)

/-! ### Definition D.2: the smooth truncation -/

/-- Definition D.2 (`M:B:def:fdl-truncation`, TeX M L12396-12401), short-scale kernel on `ℝ^d`:
`w_λ = b ∫_0^λ t^{d-s} φ_t dt/t ≥ 0`.  At `x = 0` the integral diverges and is the Lean junk `0`. -/
def fdlWE (ψ : Euc d → ℝ) (s b lam : ℝ) (x : Euc d) : ℝ :=
  b * ∫ t in Set.Ioc (0 : ℝ) lam, t ^ ((d : ℝ) - s) * fdlPhiScale ψ t x / t

/-- Definition D.2, short-scale kernel on `𝕋^d`: the integrand `t^{d-s} φ_t` is periodized *without*
subtracting its average (L12376-12377). -/
def fdlWT (ψ : Euc d → ℝ) (s b lam : ℝ) (x : Torus d) : ℝ :=
  b * ∫ t in Set.Ioc (0 : ℝ) lam, t ^ ((d : ℝ) - s) * fdlPer (fdlPhiScale ψ t) x / t

/-- Definition D.2, the truncated kernel `g_λ := g - w_λ` on `ℝ^d` (`g = rieszKernel`), with the value
at `0` given by continuous extension (junk if the limit does not exist; Lemma D.3 asserts smoothness). -/
def fdlTruncE (ψ : Euc d → ℝ) (s b lam : ℝ) (z : Euc d) : ℝ :=
  if z = 0 then
    limUnder (𝓝[≠] (0 : Euc d)) (fun z' => Whole.rieszKernel d s z' - fdlWE ψ s b lam z')
  else Whole.rieszKernel d s z - fdlWE ψ s b lam z

/-- Definition D.2, the truncated kernel `g_λ := g - w_λ` on `𝕋^d` (`g = periodicRiesz d s`), with the
value at `0` given by continuous extension. -/
def fdlTruncT (ψ : Euc d → ℝ) (s b lam : ℝ) (x : Torus d) : ℝ :=
  if x = 0 then
    limUnder (𝓝[≠] (0 : Torus d)) (fun x' => periodicRiesz d s x' - fdlWT ψ s b lam x')
  else periodicRiesz d s x - fdlWT ψ s b lam x

/-- `F_{N,η}(X_N, μ)`: the modulated energy built from `g_η` (Lemma D.4). -/
def fdlEnergy (ψ : Euc d → ℝ) (s b η : ℝ) {N : ℕ} (X : Config d N) (μ : Measure (Torus d)) : ℝ :=
  modulatedEnergyKernel (fdlTruncT ψ s b η) X μ

/-- The small-scale pair sum `N⁻² ∑_{i≠j} w_η(x_i - x_j)` (Lemma D.4(ii)). -/
def fdlPairW (ψ : Euc d → ℝ) (s b η : ℝ) {N : ℕ} (X : Config d N) : ℝ :=
  (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, fdlWT ψ s b η (X i - X j)

/-- The numerical constant `K = 16` fixed in the proof of Lemma D.3 (L12430). -/
def fdlK : ℝ := 16

/-- The Fourier coefficient `ĝ_λ(k) = b ∫_λ^∞ t^{d-s} ψ̂(tk)² dt/t` (Lemma D.3(iii)). -/
def fdlGhat (ψ : Euc d → ℝ) (s b lam : ℝ) (k : Lattice d) : ℝ :=
  b * ∫ t in Set.Ioi lam, t ^ ((d : ℝ) - s) * fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 / t

/-- The Fourier coefficient `ŵ_λ(k) = b ∫_0^λ t^{d-s} ψ̂(tk)² dt/t` (Lemma D.3(iii)). -/
def fdlWhat (ψ : Euc d → ℝ) (s b lam : ℝ) (k : Lattice d) : ℝ :=
  b * ∫ t in Set.Ioc (0 : ℝ) lam, t ^ ((d : ℝ) - s) * fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 / t

/-! ### Lemma D.1: the smooth scale representation -/

/-- `b` is a constant `b_{d,s}` for which Lemma D.1 holds: `b > 0` and
* (`0 < s < d`) `g(x) = b ∫_0^∞ t^{d-s} φ_t(x) dt/t` for `x ≠ 0` on `ℝ^d` (absolutely convergent);
* (`s = 0`) `g(x) = b lim_{R→∞} (∫_0^R t^d φ_t(x) dt/t - c_φ log R) + C_d`, `c_φ = φ(0)`, with `C_d`
  independent of `x`;
* (torus) `g(x) = b ∫_0^∞ t^{d-s} (Pφ_t(x) - ∫_{ℝ^d} φ) dt/t` for `x ≠ 0`, pointwise.
Here `g = Whole.rieszKernel` on `ℝ^d` and `g = periodicRiesz d s` on `𝕋^d` (L12363-12373). -/
def IsFDLConst (ψ : Euc d → ℝ) (s b : ℝ) : Prop :=
  0 < b ∧
  (0 < s → ∀ x : Euc d, x ≠ 0 →
    IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - s) * fdlPhiScale ψ t x / t) (Set.Ioi 0) ∧
    Whole.rieszKernel d s x =
      b * ∫ t in Set.Ioi (0 : ℝ), t ^ ((d : ℝ) - s) * fdlPhiScale ψ t x / t) ∧
  (s = 0 → ∃ C : ℝ, ∀ x : Euc d, x ≠ 0 →
    (∀ R : ℝ, 0 < R →
      IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - s) * fdlPhiScale ψ t x / t) (Set.Ioc 0 R)) ∧
    Tendsto (fun R : ℝ =>
        (∫ t in Set.Ioc (0 : ℝ) R, t ^ ((d : ℝ) - s) * fdlPhiScale ψ t x / t)
          - fdlPhi ψ 0 * Real.log R) atTop
      (𝓝 ((Whole.rieszKernel d s x - C) / b))) ∧
  (∀ x : Torus d, x ≠ 0 →
    IntegrableOn (fun t : ℝ =>
      t ^ ((d : ℝ) - s) * (fdlPer (fdlPhiScale ψ t) x - ∫ y, fdlPhi ψ y) / t) (Set.Ioi 0) ∧
    periodicRiesz d s x =
      b * ∫ t in Set.Ioi (0 : ℝ),
        t ^ ((d : ℝ) - s) * (fdlPer (fdlPhiScale ψ t) x - ∫ y, fdlPhi ψ y) / t)

/-- Lemma D.1 (`M:B:lem:fdl-rep`, TeX M L12362-12378).  For every profile `ψ` (L12360) and `0 ≤ s < d`
there is `b_{d,s} > 0` such that the Euclidean representation (`0 < s < d`, resp. `s = 0` with the
renormalised limit) and the mean-zero torus representation (`B:eq:fdl-torus-representation`) hold
(`IsFDLConst ψ s b`).  The torus integral is "interpreted distributionally, and pointwise away from
zero" (L12375): the pointwise statement is stated, with its absolute convergence.
Technical hypotheses: `1 ≤ d`. -/
theorem fdl_rep (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) : ∃ b : ℝ, IsFDLConst ψ s b := by
  sorry

/-! ### Lemma D.3: kernel facts -/

/-- Lemma D.3 (`M:B:lem:fdl-kernel`, TeX M L12403-12427), real-space items (i), (ii), (iv) on `ℝ^d`.
For all `0 ≤ s < d` and `j ≥ 0`, with constants depending only on `d, s, j, φ` (not on `λ ∈ (0,1)`
or the point):
(i) `w_λ ≥ 0` is supported in `B(0,λ)`, `g_λ = g` on `|z| ≥ λ`, `0 ≤ w_λ ≤ g + C 1_{s=0}` (for `s = 0` only on `|z| ≤ 1`: the printed bound is false for large `|z|`, where `g = -log|z|` is negative and `w_λ = 0`; repair FDL-E1, ISSUES 2026-10-18), `∫ w_λ ≤ C λ^{d-s}`;
(ii) for `j + s > 0`: `|∇^j w_λ(z)| ≤ C |z|^{-s-j} 1_{|z| ≤ λ}`, `|∇^j g_λ(z)| ≤ C (λ ∨ |z|)^{-s-j}`;
for `s = j = 0`: `|w_λ| ≤ C log(λ/|z|) 1_{0<|z|≤λ}`, `|g_λ| ≤ C (1 + |log(λ ∨ |z|)|)`; `g_λ ∈ C^∞`, with
`‖∇^j g_λ‖_∞ ≤ C λ^{-s-j}` for `j ≥ 1` and also `j = 0` when `s > 0`, and `|g_λ(0)| ≤ C(λ^{-s} + |log λ| 1_{s=0})`;
(iv) `g_λ(z) ≥ c |z|^{-s}` for `λ ≤ |z|`, `s > 0`; `g_λ(z) ≥ c log(1/|z|) - C` for `λ ≤ |z| ≤ 1/2`, `s = 0`;
`w_{Kλ}(z) ≥ c_K λ^{-s}` (resp. `≥ c_K` for `s = 0`) for `0 < |z| ≤ 2λ` and any fixed `K ≥ 16`.
Pointwise statements exclude `z = 0` where `w_λ = ∞` (Lean junk `0`).  Item (iii) (Fourier side on `ℝ^d`)
is not stated (see the module docstring).
Technical hypotheses: `1 ≤ d`; `z ≠ 0` in the lower bound for `w_{Kλ}`. -/
theorem fdl_kernel_euclid (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    -- (i)
    (∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 →
      (∀ z : Euc d, z ≠ 0 → 0 ≤ fdlWE ψ s b lam z) ∧
      (∀ z : Euc d, lam ≤ ‖z‖ →
        fdlWE ψ s b lam z = 0 ∧ fdlTruncE ψ s b lam z = Whole.rieszKernel d s z) ∧
      (∀ z : Euc d, z ≠ 0 → (s = 0 → ‖z‖ ≤ 1) →
        fdlWE ψ s b lam z ≤ Whole.rieszKernel d s z + C * (if s = 0 then 1 else 0)) ∧
      ∫⁻ z : Euc d, ENNReal.ofReal (fdlWE ψ s b lam z) ≤
        ENNReal.ofReal (C * lam ^ ((d : ℝ) - s))) ∧
    -- (ii), `j + s > 0`
    (∀ j : ℕ, 0 < (j : ℝ) + s → ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 →
      ∀ z : Euc d, z ≠ 0 →
        ‖iteratedFDeriv ℝ j (fdlWE ψ s b lam) z‖ ≤
          (if ‖z‖ ≤ lam then C * ‖z‖ ^ (-s - (j : ℝ)) else 0) ∧
        ‖iteratedFDeriv ℝ j (fdlTruncE ψ s b lam) z‖ ≤ C * (max lam ‖z‖) ^ (-s - (j : ℝ))) ∧
    -- (ii), `s = j = 0`
    (s = 0 → ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ z : Euc d, z ≠ 0 →
      |fdlWE ψ s b lam z| ≤ (if ‖z‖ ≤ lam then C * Real.log (lam / ‖z‖) else 0) ∧
      |fdlTruncE ψ s b lam z| ≤ C * (1 + |Real.log (max lam ‖z‖)|)) ∧
    -- (ii), smoothness and sup bounds ("in particular")
    (∀ lam : ℝ, 0 < lam → lam < 1 →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fdlTruncE ψ s b lam)) ∧
    (∀ j : ℕ, 0 < (j : ℝ) + s → ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ z : Euc d,
      ‖iteratedFDeriv ℝ j (fdlTruncE ψ s b lam) z‖ ≤ C * lam ^ (-s - (j : ℝ))) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 →
      |fdlTruncE ψ s b lam 0| ≤
        C * (lam ^ (-s) + (if s = 0 then |Real.log lam| else 0))) ∧
    -- (iv)
    (0 < s → ∃ c : ℝ, 0 < c ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ z : Euc d, lam ≤ ‖z‖ →
      c * ‖z‖ ^ (-s) ≤ fdlTruncE ψ s b lam z) ∧
    (s = 0 → ∃ c C : ℝ, 0 < c ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ z : Euc d, lam ≤ ‖z‖ →
      ‖z‖ ≤ 1 / 2 → c * Real.log (1 / ‖z‖) - C ≤ fdlTruncE ψ s b lam z) ∧
    (∀ K : ℝ, fdlK ≤ K → ∃ c : ℝ, 0 < c ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ z : Euc d, z ≠ 0 →
      ‖z‖ ≤ 2 * lam → c * (if s = 0 then 1 else lam ^ (-s)) ≤ fdlWE ψ s b (K * lam) z) := by
  sorry

/-- Lemma D.3 (`M:B:lem:fdl-kernel`, TeX M L12403-12427) on `𝔻 = 𝕋^d`: items (i)-(iv), with
`|z| = tdist z 0` the torus distance, derivatives on the covering space, and Fourier coefficients
through `Torus.fcoef`.  For all `0 ≤ s < d`, `j ≥ 0`, with constants depending only on `d, s, j, φ`:
(i) `w_λ ≥ 0` supported in `B(0,λ)` (periodically), `g_λ = g` on `|z| ≥ λ`, `∫ w_λ ≤ C λ^{d-s}`, and
`w_λ ≤ g + C` (see SUSPECTED ISSUE);
(ii) for `j + s > 0`: `|∇^j w_λ| ≤ C|z|^{-s-j} 1_{|z|≤λ}`, `|∇^j g_λ| ≤ C(λ ∨ |z|)^{-s-j} + C`; for `s = j = 0`:
`|w_λ| ≤ C log(λ/|z|) 1_{0<|z|≤λ}` and the periodic bound `|g_λ| ≤ C(1 + |log λ|)`; `g_λ ∈ C^∞(𝕋^d)`,
`‖∇^j g_λ‖_∞ ≤ C λ^{-s-j}` for `j ≥ 1` and `j = 0, s > 0`, `|g_λ(0)| ≤ C(λ^{-s} + |log λ| 1_{s=0})`;
(iii) `ŵ_λ(k) = b ∫_0^λ t^{d-s} ψ̂(tk)² dt/t ≥ 0` (all `k`), `ĝ_λ(k) = b ∫_λ^∞ t^{d-s} ψ̂(tk)² dt/t ≥ 0`
for `k ≠ 0`, `∑ |k|² ĝ_λ(k) < ∞`, and `|Δg_λ(0)| ≤ 4π² ∑ |k|² ĝ_λ(k) ≤ C λ^{-s-2}`;
(iv) `g_λ(z) ≥ c|z|^{-s} - C` for `λ ≤ |z|`, `s > 0`; `g_λ(z) ≥ c log(1/|z|) - C` for `λ ≤ |z| ≤ 1/2`, `s = 0`;
`w_{Kλ}(z) ≥ c_K λ^{-s}` (resp. `c_K`) for `0 < |z| ≤ 2λ`, any fixed `K ≥ 16`.
SUSPECTED ISSUE (TeX L12406): on `𝕋^d` and `s > 0` the bound `0 ≤ w_λ ≤ g + C 1_{s=0}` is false, because the
periodic `g` has mean zero and is negative somewhere at distance `≥ λ` from `0` (small `λ`), where
`w_λ = 0`; the statement here carries `+ C` for all `s` (as in the "additional `-C`" of item (iv)).  The TeX
bound is correct on `ℝ^d` (`fdl_kernel_euclid`).
`ĝ_λ(0)` is excluded in (iii) (the zero mode of `g_λ` is `-b λ^{d-s}/(d-s) ∫φ`, i.e. the constant
renormalisation of the TeX, irrelevant against mean-zero measures).
Technical hypotheses: `1 ≤ d`; `z ≠ 0` for pointwise bounds on `w_λ` (junk value at `0`). -/
theorem fdl_kernel_torus (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    -- (i)
    (∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 →
      (∀ x : Torus d, x ≠ 0 → 0 ≤ fdlWT ψ s b lam x) ∧
      (∀ x : Torus d, lam ≤ KernelGrad.tdist x 0 →
        fdlWT ψ s b lam x = 0 ∧ fdlTruncT ψ s b lam x = periodicRiesz d s x) ∧
      (∀ x : Torus d, x ≠ 0 → fdlWT ψ s b lam x ≤ periodicRiesz d s x + C) ∧
      ∫⁻ x : Torus d, ENNReal.ofReal (fdlWT ψ s b lam x) ≤
        ENNReal.ofReal (C * lam ^ ((d : ℝ) - s))) ∧
    -- (ii), `j + s > 0`
    (∀ j : ℕ, 0 < (j : ℝ) + s → ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 →
      ∀ y : Euc d, Torus.mk y ≠ 0 →
        ‖iteratedFDeriv ℝ j (Torus.lift (fdlWT ψ s b lam)) y‖ ≤
          (if KernelGrad.tdist (Torus.mk y) 0 ≤ lam then
            C * KernelGrad.tdist (Torus.mk y) 0 ^ (-s - (j : ℝ)) else 0) ∧
        ‖iteratedFDeriv ℝ j (Torus.lift (fdlTruncT ψ s b lam)) y‖ ≤
          C * (max lam (KernelGrad.tdist (Torus.mk y) 0)) ^ (-s - (j : ℝ)) + C) ∧
    -- (ii), `s = j = 0`
    (s = 0 → ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ x : Torus d, x ≠ 0 →
      |fdlWT ψ s b lam x| ≤
        (if KernelGrad.tdist x 0 ≤ lam then C * Real.log (lam / KernelGrad.tdist x 0) else 0)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ x : Torus d,
      s = 0 → |fdlTruncT ψ s b lam x| ≤ C * (1 + |Real.log lam|)) ∧
    -- (ii), smoothness and sup bounds ("in particular")
    (∀ lam : ℝ, 0 < lam → lam < 1 → Torus.IsSmooth (fdlTruncT ψ s b lam)) ∧
    (∀ j : ℕ, 0 < (j : ℝ) + s → ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ y : Euc d,
      ‖iteratedFDeriv ℝ j (Torus.lift (fdlTruncT ψ s b lam)) y‖ ≤ C * lam ^ (-s - (j : ℝ))) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 →
      |fdlTruncT ψ s b lam 0| ≤
        C * (lam ^ (-s) + (if s = 0 then |Real.log lam| else 0))) ∧
    -- (iii)
    (∀ lam : ℝ, 0 < lam → lam < 1 → ∀ k : Lattice d,
      Torus.fcoef (fdlWT ψ s b lam) k = ((fdlWhat ψ s b lam k : ℝ) : ℂ) ∧
        0 ≤ fdlWhat ψ s b lam k) ∧
    (∀ lam : ℝ, 0 < lam → lam < 1 → ∀ k : Lattice d, k ≠ 0 →
      IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - s) * fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 / t)
        (Set.Ioi lam) ∧
      Torus.fcoef (fdlTruncT ψ s b lam) k = ((fdlGhat ψ s b lam k : ℝ) : ℂ) ∧
        0 ≤ fdlGhat ψ s b lam k) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 →
      Summable (fun k : Lattice d => Lattice.enorm k ^ 2 * fdlGhat ψ s b lam k) ∧
      |Torus.laplacian (fdlTruncT ψ s b lam) 0| ≤
        4 * Real.pi ^ 2 * ∑' k : Lattice d, Lattice.enorm k ^ 2 * fdlGhat ψ s b lam k ∧
      4 * Real.pi ^ 2 * ∑' k : Lattice d, Lattice.enorm k ^ 2 * fdlGhat ψ s b lam k ≤
        C * lam ^ (-s - 2)) ∧
    -- (iv)
    (0 < s → ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ x : Torus d,
      lam ≤ KernelGrad.tdist x 0 →
      c * KernelGrad.tdist x 0 ^ (-s) - C ≤ fdlTruncT ψ s b lam x) ∧
    (s = 0 → ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ x : Torus d,
      lam ≤ KernelGrad.tdist x 0 → KernelGrad.tdist x 0 ≤ 1 / 2 →
      c * Real.log (1 / KernelGrad.tdist x 0) - C ≤ fdlTruncT ψ s b lam x) ∧
    (∀ K : ℝ, fdlK ≤ K → ∃ c : ℝ, 0 < c ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ x : Torus d, x ≠ 0 →
      KernelGrad.tdist x 0 ≤ 2 * lam →
      c * (if s = 0 then 1 else lam ^ (-s)) ≤ fdlWT ψ s b (K * lam) x) := by
  sorry

/-! ### Lemma D.4: endpoint comparisons -/

/-- Lemma D.4 (`M:B:lem:fdl-compare`, TeX M L12435-12442).  Let `X_N` be pairwise distinct, `μ = ρ dx`
admissible with `ρ ≤ Λ`, `λ = (NΛ)^{-1/d} < 1/2`.  Then, after enlarging `C₀` (constants `C₀, C` depend
only on `d, s, φ`):
(i) `F_{N,η} + o_N ≥ 0` for every `η ∈ [λ, 2Kλ]` (`K = 16`);
(ii) `0 ≤ N⁻² ∑_{i≠j} w_η(x_i - x_j) ≤ C (F_N + o_N)` for every `η ∈ [λ, 2Kλ]`;
(iii) `F_N - F_{N,λ} = (2N²)⁻¹ ∑_{i≠j} w_λ(x_i - x_j) + O(Λ λ^{d-s})`; in particular
`F_{N,λ} + o_N ≤ C (F_N + o_N)` and `F_N ≥ F_{N,λ} - C o_N`.
`o_N` is `oNΛ d s C₀ Λ N` (module docstring).  The `O(Λλ^{d-s})` is `|⋯| ≤ C Λ λ^{d-s}`.
SUSPECTED ISSUE (L12396-12397 vs L12436-12438): Definition D.2 restricts to `λ ∈ (0,1)`, but (i), (ii) use
`η` up to `2Kλ = 32 λ`, which exceeds `1` as soon as `λ ≥ 1/32`; here `g_η, w_η` are defined for every
`η > 0` and the statement is taken literally.
Technical hypotheses: `1 ≤ N` (`λ` is defined), `1 ≤ Λ` (implied by `ρ` a probability density, kept as in
`commutator_estimate`). -/
theorem fdl_compare (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 1 ≤ N → smearScale d N Λ < 1 / 2 →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
        (∀ η : ℝ, smearScale d N Λ ≤ η → η ≤ 2 * fdlK * smearScale d N Λ →
          0 ≤ fdlEnergy ψ s b η X (withDensityReal ρ) + oNΛ d s C₀ Λ N) ∧
        (∀ η : ℝ, smearScale d N Λ ≤ η → η ≤ 2 * fdlK * smearScale d N Λ →
          0 ≤ fdlPairW ψ s b η X ∧
          fdlPairW ψ s b η X ≤ C * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N)) ∧
        (|rieszEnergy d s X (withDensityReal ρ) - fdlEnergy ψ s b (smearScale d N Λ) X (withDensityReal ρ)
            - (1 / 2) * fdlPairW ψ s b (smearScale d N Λ) X|
          ≤ C * Λ * smearScale d N Λ ^ ((d : ℝ) - s) ∧
        fdlEnergy ψ s b (smearScale d N Λ) X (withDensityReal ρ) + oNΛ d s C₀ Λ N
          ≤ C * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N) ∧
        fdlEnergy ψ s b (smearScale d N Λ) X (withDensityReal ρ) - C * oNΛ d s C₀ Λ N
          ≤ rieszEnergy d s X (withDensityReal ρ)) := by
  sorry

/-- The italic sentence of Lemma D.4(iii) (TeX M L12440): "The reverse control
`F_N ≤ C (F_{N,λ} + o_N)` is false pathwise: sub-`λ` pairs carry `F_N`-energy invisible to `F_{N,λ}`."
For every `C₀, C`, `N ≥ 2`, `Λ`, admissible `ρ` with `λ = (NΛ)^{-1/d} < 1/2`, there is a pairwise
distinct configuration with `C (F_{N,λ} + o_N) < F_N`.
Technical hypotheses: `2 ≤ N` (a pair is needed), `1 ≤ d`. -/
theorem fdl_compare_reverse_false (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) (C₀ C : ℝ) {N : ℕ} (hN : 2 ≤ N)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) (hlam : smearScale d N Λ < 1 / 2)
    {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (hρΛ : ∀ x, ρ x ≤ Λ) :
    ∃ X : Config d N, X ∉ collisionSet d N ∧
      C * (fdlEnergy ψ s b (smearScale d N Λ) X (withDensityReal ρ) + oNΛ d s C₀ Λ N)
        < rieszEnergy d s X (withDensityReal ρ) := by
  sorry

/-! ### Lemma D.5: the one-sided Itô bound -/

/-- Lemma D.5 (`M:B:lem:fdl-ito`, TeX M L12452-12457).  For every pairwise distinct `X_N` and
admissible `μ` with `‖μ‖_∞ ≤ Λ`, with `λ = (NΛ)^{-1/d}`,
`∬_{𝔻²∖△} Δg_λ(x - y) d(μ_N - μ)^{⊗2} ≤ |Δg_λ(0)|/N ≤ C Λ^{(s+2)/d} N^{(s+2)/d - 1}`
(`C` depending only on `d, s, φ`).
Technical hypotheses: `1 ≤ N`, `1 ≤ Λ`. -/
theorem fdl_ito (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 1 ≤ N →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
        offDiagPairing (fun x y => Torus.laplacian (fdlTruncT ψ s b (smearScale d N Λ)) (x - y))
            X (withDensityReal ρ)
          ≤ |Torus.laplacian (fdlTruncT ψ s b (smearScale d N Λ)) 0| / N ∧
        |Torus.laplacian (fdlTruncT ψ s b (smearScale d N Λ)) 0| / N
          ≤ C * Λ ^ ((s + 2) / d) * (N : ℝ) ^ ((s + 2) / d - 1) := by
  sorry
























/-! ### Remark D.7: scope -/

/-- Remark D.7 (`M:B:rem:fdl-scope`, TeX M L12477-12479), the checkable content: the statements of
Lemmas D.4 and D.5 are not specific to `s ≥ d - 2` or to `η = λ`: they hold for all `0 ≤ s < d` and all
`η ∈ [λ, 1)` with `η`-dependent constants, where the dependence on `η` is through the ratio `η/λ ≤ R`
(constants `C₀, C` depend on `R`; for `η = λ` this is D.4/D.5).  Stated here: for every `R ≥ 1`, items
(i), (ii) and (iii) of D.4 with `g_η` in place of `g_λ` for every `η ∈ [λ, Rλ] ∩ (0,1)`
(item (iii) as `F_N - F_{N,η} = (2N²)⁻¹ ∑ w_η + O(Λ η^{d-s})`, with its two consequences), and D.5 for
`g_η` with the same `λ`-bound `C Λ^{(s+2)/d} N^{(s+2)/d-1}`.  The last clause of the remark (D.4(i)
gives an independent proof of the coercivity lower bound `B:eq:hrs-periodic-coercivity-lower`) is a
proof remark: it is `fdl_compare` (i), (iii) combined, and the statement is the existing
`HRS.coercivity_lower`; it is not restated.  D.1, D.3 hold for every `λ ∈ (0,1)` and `0 ≤ s < d` already.
SUSPECTED ISSUE (TeX L12478): read literally ("`η ∈ [λ,1)` with `η`-dependent constants", `η` fixed and the
constants uniform in `N`) the D.4(ii) statement is false: for well-spread configurations
`N⁻² ∑ w_η(x_i - x_j) ≈ Λ η^{d-s}`, which is of order one, while `F_N + o_N` is of order `a_N^Λ → 0`.  The
ratio form `η ≤ Rλ` (constants depending on `R`) is the reading that can be true and is stated.
Technical hypotheses: `1 ≤ N`, `1 ≤ Λ`. -/
theorem fdl_scope (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) {R : ℝ} (hR : 1 ≤ R) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 1 ≤ N → smearScale d N Λ < 1 / 2 →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
      ∀ η : ℝ, smearScale d N Λ ≤ η → η ≤ R * smearScale d N Λ → η < 1 →
        0 ≤ fdlEnergy ψ s b η X (withDensityReal ρ) + oNΛ d s C₀ Λ N ∧
        (0 ≤ fdlPairW ψ s b η X ∧
          fdlPairW ψ s b η X ≤ C * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N)) ∧
        (|rieszEnergy d s X (withDensityReal ρ) - fdlEnergy ψ s b η X (withDensityReal ρ)
            - (1 / 2) * fdlPairW ψ s b η X| ≤ C * Λ * η ^ ((d : ℝ) - s) ∧
          fdlEnergy ψ s b η X (withDensityReal ρ) + oNΛ d s C₀ Λ N
            ≤ C * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N) ∧
          fdlEnergy ψ s b η X (withDensityReal ρ) - C * oNΛ d s C₀ Λ N
            ≤ rieszEnergy d s X (withDensityReal ρ)) ∧
        (offDiagPairing (fun x y => Torus.laplacian (fdlTruncT ψ s b η) (x - y)) X (withDensityReal ρ)
            ≤ |Torus.laplacian (fdlTruncT ψ s b η) 0| / N ∧
          |Torus.laplacian (fdlTruncT ψ s b η) 0| / N
            ≤ C * Λ ^ ((s + 2) / d) * (N : ℝ) ^ ((s + 2) / d - 1)) := by
  sorry

end HRS
