import HRS.Whole.AppendixBEnergy

/-!
# Sub-Coulomb commutator estimate on `ℝ^d` (note of M. Rosenzweig, 2026-10-13): definitions

Source: `source/external/subcoulomb_commutator_20261013T142216Z/
subcoulomb_commutator_HCRS_rewrite_20261013T142216Z.tex` (cited below as `[N]`, with TeX line
numbers), "Optimal transport regularity in sub-Coulomb commutator estimates".  Plan:
`docs/external/subcoulomb-plan.md`.

This file contains only definitions (no `sorry`); the statements are in the sibling files
`Positive`, `Energy`, `Local`, `Continuous`, `External`, `Unit`, `Assembly`, `Bridge`.

## Representation decisions (consequential)

* **Kernel.**  `kern s` is the note's `g` (`[N] L76-83`): `g(x) = s⁻¹|x|^{-s}` for `s > 0`, `-log|x|` for
  `s = 0` (note the factor `s⁻¹`, absent from the repository's `HRS.Whole.rieszKernel`; the translation
  is `rieszKernel = s • kern` for `s > 0`, see `Bridge.lean`).  `kernGrad s x = -|x|^{-(s+2)} x` is `∇g`
  for `x ≠ 0` (explicit formula, no Mathlib `gradient`, no junk).
* **Signed reference density.**  `μ` is a function `ρ : Euc d → ℝ` (an a.e. class is enough: every
  quantity is an integral against `ρ dx`), `‖μ‖_{L^p} = (eLpNorm ρ p).toReal`.  The modulated energy
  `F_N` and the commutator `𝖠₁` (`[N] L84-94`) are written out with the particle diagonal deleted
  (`pairGen`), exactly as `HRS.Whole.centeredPairFunctional`; the absolute convergence of the integrals
  is a separate predicate (`PairIntegrable`) which is part of the conclusion of the main results.
* **Signed measures** (needed for `ν = μ_N - μ`, `[N] L161`) are pairs of positive measures
  (`SMeas`), `∫ f dσ = ∫ f dσ⁺ - ∫ f dσ⁻`.  The class "compactly supported finite real measure or real
  Schwartz density" of Lemma 3.2/4.1 is `IsAdmissible`.
* **Fourier objects** use Mathlib's `𝓕` (`e^{-2πi x·ξ}`, as `[N] (1.fourier-convention)`, L222).
  `P_{≤L}` is *convolution with the Schwartz kernel* `psiL L = 𝓕⁻[χ(·/L)]` (so it is defined for
  functions of polynomial growth, e.g. Lipschitz `v`, and for the singular kernels `∇g`), `P_{>L} = I - P_{≤L}`.
  The cutoff `χ` is Mathlib's `ContDiffBump` with radii `1 < 2` (radial, `0 ≤ χ ≤ 1`, `χ = 1` on
  `B(0,1)`, `supp χ ⊂ B(0,2)`): a fixed choice, as the note ("the fixed cutoff functions", L239).
  Sobolev seminorms of `σ` (a measure, with `σ̂` a function) and of `a ∈ L²` (with `fourierL2`) are
  `ℝ≥0∞`-valued weighted `L²(dξ)` norms of the Fourier transform (`sobSqE`, `homSqE`), so that
  "infinite" is `⊤`, never a junk `0`.  Homogeneous spaces modulo polynomials are never used: the
  fractional derivative `|∇|^α v` of a Lipschitz `v` is the repository's distributional
  `IsFracDerivRep`, packaged in `HRS.Whole.HasFracTransportBound` (`‖∇v‖_∞ + ‖|∇|^α v‖_{L^p} ≤ K`).
* The inhomogeneous fractional derivative `⟨∇⟩^α f ∈ L^p` of a non-Schwartz `f` is `IsBesselRep`
  (distributional, same shape as `IsFracDerivRep`); the Fourier support `supp f̂ ⊂ B(0,R)` of a
  function is `FourierSuppIn`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d N : ℕ}

/-! ### Exponents (`[N] (1.exponents)`, L162-175) -/

/-- `α = (d-s)/2`. -/
def alphaE (d : ℕ) (s : ℝ) : ℝ := ((d : ℝ) - s) / 2

/-- `p₁ = 2d/(d-s-2)`. -/
def p1E (d : ℕ) (s : ℝ) : ℝ := 2 * d / ((d : ℝ) - s - 2)

/-- `p₂ = 2d/(s+2)`. -/
def p2E (d : ℕ) (s : ℝ) : ℝ := 2 * d / (s + 2)

/-- `‖∇v‖_{L^∞} + ‖|∇|^{(d-s)/2} v‖_{L^{2d/(d-s-2)}} ≤ K` (`C(v) ≤ K`, `[N] (1.velocity-bound)`,
L166): the repository's `HasFracTransportBound` with the exponents of Theorem 1.1 (the same
expressions as in `HRS.Whole.whole_commutator_sub_lower`). -/
abbrev SubTransport (d : ℕ) (s : ℝ) (v : Euc d → Euc d) (K : ℝ) : Prop :=
  HasFracTransportBound (((d : ℝ) - s) / 2) (2 * d / ((d : ℝ) - s - 2)) v K

/-! ### The kernel, the modulated energy and the commutator (`[N] L76-94`) -/

/-- The log/Riesz potential `g` of `[N] (1.kernel)` (L77-83); junk value at `0` is never used. -/
def kern (s : ℝ) (x : Euc d) : ℝ :=
  if s = 0 then -Real.log ‖x‖ else s⁻¹ * ‖x‖ ^ (-s)

/-- `∇g(x) = -|x|^{-(s+2)} x` (`x ≠ 0`; for `s = 0` this is `-x/|x|²`). -/
def kernGrad (s : ℝ) (x : Euc d) : Euc d := -(‖x‖ ^ (-(s + 2))) • x

/-- The deleted-diagonal pair functional `∬_{(ℝ^d)²∖△} k d(μ_N - μ)^{⊗2}` of `[N] (1.energy)`,
`(1.comm)`:
`N⁻² ∑_{i≠j} k(x_i,x_j) - 2N⁻¹ ∑_i ∫ k(x_i,y)ρ(y)dy + ∬ k(x,y)ρ(x)ρ(y)`
(Bochner integrals; absolute convergence is `PairIntegrable`). -/
def pairGen (k : Euc d → Euc d → ℝ) (X : Fin N → Euc d) (ρ : Euc d → ℝ) : ℝ :=
  (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, k (X i) (X j)
    - (2 / (N : ℝ)) * ∑ i, (∫ y, k (X i) y * ρ y)
    + ∫ x, ∫ y, k x y * ρ x * ρ y

/-- Absolute convergence of the integrals defining `pairGen k X ρ`. -/
def PairIntegrable (k : Euc d → Euc d → ℝ) (X : Fin N → Euc d) (ρ : Euc d → ℝ) : Prop :=
  (∀ i, Integrable (fun y => k (X i) y * ρ y)) ∧
    Integrable (fun p : Euc d × Euc d => k p.1 p.2 * ρ p.1 * ρ p.2)

/-- The modulated energy `F_N(X_N, μ) = ½ ∬_{△ᶜ} g(x-y) d(μ_N-μ)^{⊗2}` (`[N] (1.energy)`, L86-88). -/
def modEnergy (s : ℝ) (X : Fin N → Euc d) (ρ : Euc d → ℝ) : ℝ :=
  (1 / 2) * pairGen (fun x y => kern s (x - y)) X ρ

/-- The commutator kernel `(v(x) - v(y)) · F(x-y)`, `0` on the diagonal (the diagonal of
`(ℝ^d)²` is `μ⊗μ`- and `μ_N⊗μ`-null; the particle diagonal is deleted in `pairGen`). -/
def commKer (F : Euc d → Euc d) (v : Euc d → Euc d) (x y : Euc d) : ℝ :=
  if x = y then 0 else inner ℝ (v x - v y) (F (x - y))

/-- `𝖠₁[X_N, μ, v] = ∬_{△ᶜ} (v(x)-v(y))·∇g(x-y) d(μ_N-μ)^{⊗2}` (`[N] (1.comm)`, L91-94). -/
def commA (s : ℝ) (X : Fin N → Euc d) (ρ : Euc d → ℝ) (v : Euc d → Euc d) : ℝ :=
  pairGen (commKer (kernGrad s) v) X ρ

/-- Absolute convergence of the integrals defining `F_N` (for the kernel `g`). -/
def EnergyIntegrable (s : ℝ) (X : Fin N → Euc d) (ρ : Euc d → ℝ) : Prop :=
  PairIntegrable (fun x y => kern s (x - y)) X ρ

/-- Absolute convergence of the integrals defining `𝖠₁`. -/
def CommIntegrable (s : ℝ) (X : Fin N → Euc d) (ρ : Euc d → ℝ) (v : Euc d → Euc d) : Prop :=
  PairIntegrable (commKer (kernGrad s) v) X ρ

/-- The logarithmic hypothesis `[N] (1.loghyp)` (L102-104):
`∬ |g(x-y)| d|μ|^{⊗2} < ∞` for `s = 0` (`g = -log|·|`). -/
def LogIntegrable (ρ : Euc d → ℝ) : Prop :=
  Integrable (fun p : Euc d × Euc d => kern 0 (p.1 - p.2) * (ρ p.1 * ρ p.2))

/-- `‖ρ‖_{L^p}` (finite when `ρ ∈ L^p`). -/
def normE (p : ℝ≥0∞) (ρ : Euc d → ℝ) : ℝ := (eLpNorm ρ p volume).toReal

/-- The length scale `λ = (N ‖μ‖_{L^∞})^{-1/d}` (`[N] (1.lambda)`, L108). -/
def lamN (d N : ℕ) (ρ : Euc d → ℝ) : ℝ := ((N : ℝ) * normE ⊤ ρ) ^ (-(1 : ℝ) / d)

/-- "`ρ` is a bounded, compactly supported, measurable real density of mass one" (the temporary
assumption of `[N]` L161, L325, L641; either sign). -/
structure BddCptDensity (ρ : Euc d → ℝ) : Prop where
  measurable : Measurable ρ
  bdd : ∃ B : ℝ, ∀ x, |ρ x| ≤ B
  cpt : HasCompactSupport ρ
  mass : ∫ x, ρ x = 1

/-! ### The Fourier cutoff and the operators `P_{≤L}`, `P_{>L}` (`[N] L379-391`) -/

/-- The cutoff `χ ∈ C_c^∞` of `[N] L379`: `0 ≤ χ ≤ 1`, `χ = 1` on `B(0,1)`, `supp χ ⊂ B(0,2)`
(Mathlib's `ContDiffBump` with radii `1 < 2`). -/
def chiBump (d : ℕ) : ContDiffBump (0 : Euc d) := ⟨1, 2, one_pos, one_lt_two⟩

/-- `χ`. -/
def chi (ξ : Euc d) : ℝ := chiBump d ξ

/-- The (real, even, Schwartz) kernel `ψ_L = 𝓕⁻[χ(·/L)]` of `P_{≤L}`. -/
def psiL (L : ℝ) (x : Euc d) : ℝ := (𝓕⁻ (fun ξ : Euc d => ((chi (L⁻¹ • ξ) : ℝ) : ℂ)) x).re

/-- `P_{≤L} f = ψ_L * f` (`\widehat{P_{≤L}f} = χ(ξ/L) f̂`), for `f` of polynomial growth. -/
def Pleq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : ℝ) (f : Euc d → E)
    (x : Euc d) : E :=
  ∫ y, psiL L y • f (x - y)

/-- `P_{>L} = I - P_{≤L}`. -/
def Pgt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : ℝ) (f : Euc d → E)
    (x : Euc d) : E :=
  f x - Pleq L f x

/-- `∇g_{≤1} = ∇(P_{≤1}g) = ψ_1 * ∇g` (`[N] L386`, L393). -/
def gloForce (s : ℝ) (x : Euc d) : Euc d := Pleq 1 (kernGrad s) x

/-- `∇g_{>1} = ∇g - ∇g_{≤1}`. -/
def ghiForce (s : ℝ) (x : Euc d) : Euc d := kernGrad s x - gloForce s x

/-- The Fourier-side multiplier `F ↦ χ(ξ/L) F(ξ)` (the Fourier transform of `P_{≤L}`). -/
def lowFreq (L : ℝ) (F : Euc d → ℂ) : Euc d → ℂ := fun ξ => ((chi (L⁻¹ • ξ) : ℝ) : ℂ) * F ξ

/-! ### Sobolev seminorms, in `ℝ≥0∞` -/

/-- `‖f‖²_{H^t}`-type quantity `∫ (1+4π²|ξ|²)^t |F(ξ)|² dξ` for the Fourier transform `F`
(`[N] (1.fourier-convention)`, L224-225). -/
def sobSqE (t : ℝ) (F : Euc d → ℂ) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ t) * ‖F ξ‖ₑ ^ 2

/-- `‖f‖²_{Ḣ^t}`-type quantity `∫ (2π|ξ|)^{2t} |F(ξ)|² dξ` (weight `0` at `ξ = 0` for `t < 0`, a null
set). -/
def homSqE (t : ℝ) (F : Euc d → ℂ) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal ((2 * Real.pi * ‖ξ‖) ^ (2 * t)) * ‖F ξ‖ₑ ^ 2

/-! ### Signed measures -/

/-- A real signed measure `σ = σ⁺ - σ⁻` as a pair of positive measures. -/
structure SMeas (d : ℕ) where
  pos : Measure (Euc d)
  neg : Measure (Euc d)

namespace SMeas

/-- `∫ f dσ`. -/
def int (σ : SMeas d) (f : Euc d → ℝ) : ℝ := ∫ x, f x ∂σ.pos - ∫ x, f x ∂σ.neg

/-- `∫ F dσ` for `ℝ^d`-valued `F`. -/
def intV (σ : SMeas d) (F : Euc d → Euc d) : Euc d := ∫ x, F x ∂σ.pos - ∫ x, F x ∂σ.neg

/-- `σ(ℝ^d)`. -/
def mass (σ : SMeas d) : ℝ := σ.int fun _ => 1

/-- The Fourier transform `σ̂(ξ) = ∫ e^{-2πi x·ξ} dσ(x)`. -/
def fourier (σ : SMeas d) (ξ : Euc d) : ℂ :=
  ∫ x, Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ))) ∂σ.pos
    - ∫ x, Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ))) ∂σ.neg

/-- `∬ k(x,y) dσ(x) dσ(y)` (iterated integral; `k` bounded or absolutely integrable in the uses). -/
def pair2 (σ : SMeas d) (k : Euc d → Euc d → ℝ) : ℝ := σ.int fun x => σ.int fun y => k x y

/-- `(F * σ)(x) = ∫ F(x-y) dσ(y)` for `ℝ^d`-valued `F`. -/
def convForce (σ : SMeas d) (F : Euc d → Euc d) (x : Euc d) : Euc d := σ.intV fun y => F (x - y)

/-- Both parts finite. -/
def IsFinite (σ : SMeas d) : Prop := IsFiniteMeasure σ.pos ∧ IsFiniteMeasure σ.neg

/-- Compact support. -/
def CompactSupp (σ : SMeas d) : Prop :=
  ∃ R : ℝ, σ.pos (closedBall 0 R)ᶜ = 0 ∧ σ.neg (closedBall 0 R)ᶜ = 0

/-- The signed measure `a dx`. -/
def ofDensity (a : Euc d → ℝ) : SMeas d :=
  ⟨volume.withDensity fun x => ENNReal.ofReal (a x),
    volume.withDensity fun x => ENNReal.ofReal (-a x)⟩

end SMeas

/-- A real Schwartz function. -/
def IsRealSchwartz (a : Euc d → ℝ) : Prop :=
  ∃ φ : SchwartzMap (Euc d) ℂ, ∀ x, φ x = ((a x : ℝ) : ℂ)

/-- "A compactly supported finite real measure or a real Schwartz density"
(`[N] L447`, L520-525, L571). -/
def IsAdmissible (σ : SMeas d) : Prop :=
  σ.IsFinite ∧ (σ.CompactSupp ∨ ∃ a, IsRealSchwartz a ∧ σ = SMeas.ofDensity a)

/-- `ν = μ_N - μ` (`[N] L161`): `ν⁺ = μ_N + μ⁻`, `ν⁻ = μ⁺`. -/
def chargeOf (X : Fin N → Euc d) (ρ : Euc d → ℝ) : SMeas d :=
  ⟨HRS.Whole.empirical X + volume.withDensity (fun x => ENNReal.ofReal (-ρ x)),
    volume.withDensity fun x => ENNReal.ofReal (ρ x)⟩

/-- The auxiliary notation `𝒞_h(v,σ) = ∬_{△ᶜ} (v(x)-v(y))·∇h(x-y) dσ^{⊗2}` of `[N] (1.aux-comm)`
(L229-232), with the force `F = ∇h` and the iterated integral over the signed measure `σ`. -/
def Ccomm (F : Euc d → Euc d) (v : Euc d → Euc d) (σ : SMeas d) : ℝ :=
  σ.pair2 (commKer F v)

/-- `𝒞_h(v,a)` for a density `a` (an `L²` function), `[N] (1.aux-comm)`. -/
def CcommFun (F : Euc d → Euc d) (v : Euc d → Euc d) (a : Euc d → ℝ) : ℝ :=
  ∫ x, ∫ y, commKer F v x y * a x * a y

/-- The kernel energy `‖σ‖²_h = ∬ h(x-y) dσ^{⊗2}` (`[N] (1.kernel-energy)`, L235) for a kernel `h`. -/
def kerEnergy (h : Euc d → ℝ) (σ : SMeas d) : ℝ := σ.pair2 fun x y => h (x - y)

/-! ### Fourier support, Bessel representatives, unit cubes -/

/-- `supp f̂ ⊂ B̄(0,R)`: `f` annihilates every Schwartz function whose Fourier transform has support
disjoint from the closed ball. -/
def FourierSuppIn (R : ℝ) (u : Euc d → ℝ) : Prop :=
  ∀ φ : SchwartzMap (Euc d) ℂ, Disjoint (tsupport (𝓕 (⇑φ))) (closedBall (0 : Euc d) R) →
    ∫ x, ((u x : ℝ) : ℂ) * φ x = 0

/-- `F` represents `⟨∇⟩^α f` in the sense of distributions (`⟨∇⟩^α φ = 𝓕⁻[(1+4π²|ξ|²)^{α/2} 𝓕φ]`),
the inhomogeneous analogue of `HRS.Whole.IsFracDerivRep`. -/
def IsBesselRep (α : ℝ) (f F : Euc d → ℝ) : Prop :=
  ∀ φ : SchwartzMap (Euc d) ℂ,
    Integrable (fun x => ((f x : ℝ) : ℂ) *
      (𝓕⁻ (fun ξ : Euc d => (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (α / 2) : ℝ) : ℂ) * 𝓕 (⇑φ) ξ)) x) ∧
    Integrable (fun x => ((F x : ℝ) : ℂ) * φ x) ∧
    ∫ x, ((f x : ℝ) : ℂ) *
        (𝓕⁻ (fun ξ : Euc d => (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (α / 2) : ℝ) : ℂ) * 𝓕 (⇑φ) ξ)) x =
      ∫ x, ((F x : ℝ) : ℂ) * φ x

/-- The unit cube `Q_j = j + [0,1)^d`, `j ∈ ℤ^d`. -/
def cube (j : Fin d → ℤ) : Set (Euc d) := {x | ∀ i, (j i : ℝ) ≤ x i ∧ x i < (j i : ℝ) + 1}

/-- `(∑_j sup_{Q_j} |f|^p)^{1/p}` (`[N] (1.intro-suprema)`, L196-199), in `ℝ≥0∞`. -/
def cubeSupNorm {E : Type*} [NormedAddCommGroup E] (p : ℝ) (f : Euc d → E) : ℝ≥0∞ :=
  (∑' j : Fin d → ℤ, (⨆ x ∈ cube j, ‖f x‖ₑ) ^ p) ^ (1 / p)

open Classical in
/-- The unit-cube mass `n_j = μ_N(Q_j)`. -/
def occ (X : Fin N → Euc d) (j : Fin d → ℤ) : ℝ :=
  (1 / (N : ℝ)) * ((Finset.univ.filter fun i => X i ∈ cube j).card : ℝ)

/-! ### Scaling (`[N] (5.rescaling)`, L732-736) -/

/-- `μ̃(x) = η^d μ(ηx)`. -/
def scaleDens (η : ℝ) (ρ : Euc d → ℝ) (x : Euc d) : ℝ := η ^ (d : ℕ) * ρ (η • x)

/-- `ṽ(x) = η⁻¹ v(ηx)`. -/
def scaleVec (η : ℝ) (v : Euc d → Euc d) (x : Euc d) : Euc d := η⁻¹ • v (η • x)

/-- `X̃ = X/η`. -/
def scaleConf (η : ℝ) (X : Fin N → Euc d) : Fin N → Euc d := fun i => η⁻¹ • X i

/-! ### The positive truncation (`[N] L245-263`) -/

/-- `φ(x) = (1+|x|²)^{-(d+2)}` (`[N] (2.phi)`, L246). -/
def phi (x : Euc d) : ℝ := (1 + ‖x‖ ^ 2) ^ (-((d : ℝ) + 2))

/-- Radial profile `φ(r)`. -/
def phiR (d : ℕ) (r : ℝ) : ℝ := (1 + r ^ 2) ^ (-((d : ℝ) + 2))

/-- `φ_t(x) = t^{-d} φ(x/t)`. -/
def phiT (t : ℝ) (x : Euc d) : ℝ := t ^ (-(d : ℝ)) * phi (t⁻¹ • x)

/-- The normalising constant `c_{φ,d,s}` (`[N] (2.normalizing-constant)`, L253-258). -/
def cPhi (d : ℕ) (s : ℝ) : ℝ :=
  if s = 0 then 1 else (s * ∫ r in Set.Ioi (0 : ℝ), r ^ (s - 1) * phiR d r)⁻¹

/-- `f_η(x) = c_φ ∫_0^η t^{d-s} φ_t(x) dt/t` (`[N] (2.positivecut)`, L261); junk `0` at `x = 0`
(never used). -/
def fTrunc (s η : ℝ) (x : Euc d) : ℝ :=
  cPhi d s * ∫ t in Set.Ioc 0 η, t ^ ((d : ℝ) - s) * phiT t x / t

/-- The value `g_1(0)` (`[N] L299`, `(2.log-g-origin)` L306). -/
def g1Zero (d : ℕ) (s : ℝ) : ℝ :=
  if s = 0 then
    -(∫ r in Set.Ioc (0 : ℝ) 1, (phiR d r - 1) / r) - ∫ r in Set.Ioi (1 : ℝ), phiR d r / r
  else cPhi d s / s

/-- `g_1 = g - f_1` off the origin, extended by `g_1(0)` (which is its limit, Lemma 2.1). -/
def g1 (s : ℝ) (x : Euc d) : ℝ := if x = 0 then g1Zero d s else kern s x - fTrunc s 1 x

/-- The Fourier-side formula `ĝ_1(ξ) = c_φ ∫_1^∞ t^{2α} φ̂(tξ) dt/t` (`[N] (2.fourierpositive)`, L315;
`ξ ≠ 0`). -/
def g1Hat (s : ℝ) (ξ : Euc d) : ℝ :=
  cPhi d s * ∫ t in Set.Ioi (1 : ℝ),
    t ^ (2 * alphaE d s) * (𝓕 (fun x : Euc d => ((phi x : ℝ) : ℂ)) (t • ξ)).re / t

/-- `f̂_1(ξ) = c_φ ∫_0^1 t^{2α} φ̂(tξ) dt/t` (`[N] (2.fourierpositive)`, L317). -/
def f1Hat (s : ℝ) (ξ : Euc d) : ℝ :=
  cPhi d s * ∫ t in Set.Ioc (0 : ℝ) 1,
    t ^ (2 * alphaE d s) * (𝓕 (fun x : Euc d => ((phi x : ℝ) : ℂ)) (t • ξ)).re / t

end HRS.Commutator.Whole
