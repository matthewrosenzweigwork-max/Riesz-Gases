import HRS.PDE.Toolbox.Symbol
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Lemma C.3 on `ℝ^d`: definitions

The source states Lemma C.3 (`B:lem:quadratic-toolbox`, lines 12253–12268) for a Fourier multiplier
"on `𝕋^d` or `ℝ^d`".  `HRS/PDE/Toolbox.lean` has the torus case; this file and the files
`HRS/PDE/ToolboxRd/*.lean` have the `ℝ^d` case.

Conventions.  The Fourier transform is `û(ξ) = ∫ e^{-2πi⟨x,ξ⟩} u(x) dx` (Mathlib's `𝓕`), extended to
`L²` by Plancherel (`Lp.fourierTransformₗᵢ`); for a real function `u` that is not in `L²` the
transform `fourierL2 u` is the junk value `0`.  The multiplier `K` has `\widehat{Ku} = m û`, and
`B(u,v) = ⟨Ku,v⟩_{L²}` is `symbolForm m u v = Re ∫ m û \bar{v̂}`, exactly as on the torus.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate FourierTransform

namespace HRS.PDE.ToolboxRd

variable {d : ℕ}

/-- The Fourier transform (Plancherel) of a real `L²` function, as a function `ℝ^d → ℂ`; the junk
value `0` if `u ∉ L²`. -/
def fourierL2 (u : Euc d → ℝ) : Euc d → ℂ :=
  open Classical in
  if h : MemLp u 2 volume then
    ⇑(Lp.fourierTransformₗᵢ (Euc d) ℂ ((h.ofReal (K := ℂ)).toLp (fun x => ((u x : ℝ) : ℂ))))
  else 0

/-- `B(u,v) = ⟨Ku,v⟩ = Re ∫ m(ξ) û(ξ) \overline{v̂(ξ)} dξ` for a real multiplier `m` (the analogue of
`HRS.PDE.symbolForm`). -/
def symbolForm (m : Euc d → ℝ) (u v : Euc d → ℝ) : ℝ :=
  (∫ ξ, ((m ξ : ℝ) : ℂ) * (fourierL2 u ξ * conj (fourierL2 v ξ))).re

/-- `∫ (1 + 4π²|ξ|²)^s |û(ξ)|² dξ`, the square of the `H^s(ℝ^d)` norm. -/
def sobolevNormSq (s : ℝ) (u : Euc d → ℝ) : ℝ :=
  ∫ ξ, (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ s * ‖fourierL2 u ξ‖ ^ 2

/-- Membership in `H^s(ℝ^d)`: square-integrable with finite weighted Fourier integral. -/
def MemSobolev (s : ℝ) (u : Euc d → ℝ) : Prop :=
  MemLp u 2 volume ∧ Integrable fun ξ => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ s * ‖fourierL2 u ξ‖ ^ 2

/-- `‖w‖²_{L²(ℝ^d)}`. -/
def l2NormSq (w : Euc d → ℝ) : ℝ := ∫ x, w x ^ 2

/-- A Lipschitz function on `ℝ^d` with constant `L`. -/
def IsLipschitz (L : ℝ) (u : Euc d → ℝ) : Prop := ∀ x y, |u x - u y| ≤ L * ‖x - y‖

/-- `u ∈ C^{1,1}_b(ℝ^d)`: `C¹`, bounded with bounded derivative, and the derivative is Lipschitz with
constant `L`. -/
def IsC11 (L : ℝ) (u : Euc d → ℝ) : Prop :=
  ContDiff ℝ 1 u ∧ (∃ B : ℝ, ∀ x, |u x| ≤ B) ∧ (∃ B : ℝ, ∀ x, ‖fderiv ℝ u x‖ ≤ B) ∧
    LipschitzWith (Real.toNNReal L) (fun x => fderiv ℝ u x)

/-- The `C^{0,1}` norm `‖a‖_∞ + [a]_{C^{0,1}}` on `ℝ^d`. -/
def c01Norm (a : Euc d → ℝ) : ℝ :=
  (⨆ x, |a x|) + ⨆ p : {p : Euc d × Euc d // p.1 ≠ p.2}, |a p.1.1 - a p.1.2| / ‖p.1.1 - p.1.2‖

/-- The symbol class of Lemma C.3: `m` is real, even, nonnegative, smooth away from `0`,
homogeneous of degree `θ` away from `0`, and vanishes at `0` (lines 12254–12255). -/
structure IsHomogSymbol (θ : ℝ) (m : Euc d → ℝ) : Prop where
  smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m {ξ | ξ ≠ 0}
  even : ∀ ξ, m (-ξ) = m ξ
  nonneg : ∀ ξ, 0 ≤ m ξ
  homog : ∀ c : ℝ, 0 < c → ∀ ξ, m (c • ξ) = c ^ θ * m ξ
  zero : m 0 = 0

/-- The Lévy-kernel representation of Lemma C.3(ii) (lines 12257–12261) on `ℝ^d`: an even kernel `𝔨`,
smooth away from `0`, with `|𝔨(z)| ≤ C|z|^{-d-θ}`, such that `∫ 𝔨(z)(1 - cos 2π⟨ξ,z⟩) dz = m(ξ)`
(absolutely convergent); the principal-value formula
`Ku(x) = lim_{ε→0} ∫_{|z|>ε} 𝔨(z)(u(x) - u(x-z)) dz` for `u ∈ C^{1,1}_b`, where `Ku` is defined by
duality with Schwartz functions, `∫ Ku φ = ∫ u Kφ`, `Kφ = 𝓕⁻(m 𝓕φ)` (this is the meaning of
"testing against Schwartz functions" in line 12260; for a bounded `u` the function `Ku` is in general
not in `L²`); and the bilinear identity `B(u,v) = ½ ∬ 𝔨(z) δ_z u(x) δ_z v(x) dz dx` (absolutely
convergent) for Lipschitz `u, v ∈ H¹`. -/
structure IsLevyKernel (θ : ℝ) (m : Euc d → ℝ) (𝔨 : Euc d → ℝ) : Prop where
  even : ∀ z, 𝔨 (-z) = 𝔨 z
  smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) 𝔨 {z | z ≠ 0}
  bound : ∃ C : ℝ, ∀ z : Euc d, z ≠ 0 → |𝔨 z| ≤ C * ‖z‖ ^ (-(d : ℝ) - θ)
  symbol : ∀ ξ : Euc d, Integrable (fun z => 𝔨 z * (1 - Real.cos (2 * Real.pi * inner ℝ ξ z))) ∧
    ∫ z, 𝔨 z * (1 - Real.cos (2 * Real.pi * inner ℝ ξ z)) = m ξ
  pv : ∀ (L : ℝ) (u : Euc d → ℝ), IsC11 L u → ∃ Ku : Euc d → ℝ,
    (∀ x, Tendsto (fun ε : ℝ => ∫ z in {z : Euc d | ε < ‖z‖}, 𝔨 z * (u x - u (x - z)))
      (𝓝[>] 0) (𝓝 (Ku x))) ∧
    ∀ φ : SchwartzMap (Euc d) ℂ,
      Integrable (fun x => ((Ku x : ℝ) : ℂ) * φ x) ∧
      Integrable (fun x => ((u x : ℝ) : ℂ) *
        (𝓕⁻ (fun ξ : Euc d => ((m ξ : ℝ) : ℂ) * 𝓕 (⇑φ) ξ)) x) ∧
      ∫ x, ((Ku x : ℝ) : ℂ) * φ x =
        ∫ x, ((u x : ℝ) : ℂ) * (𝓕⁻ (fun ξ : Euc d => ((m ξ : ℝ) : ℂ) * 𝓕 (⇑φ) ξ)) x
  bilinear : ∀ (Lu Lv : ℝ) (u v : Euc d → ℝ), IsLipschitz Lu u → IsLipschitz Lv v →
    MemSobolev 1 u → MemSobolev 1 v →
    Integrable (fun p : Euc d × Euc d => 𝔨 p.2 * (u p.1 - u (p.1 - p.2)) * (v p.1 - v (p.1 - p.2))) ∧
    symbolForm m u v =
      (1 / 2) * ∫ p : Euc d × Euc d, 𝔨 p.2 * (u p.1 - u (p.1 - p.2)) * (v p.1 - v (p.1 - p.2))

/-- The symbol `𝔪_q(ξ) = 4π² c_{d,s} (2π|ξ|)^{s-d} (q·ξ)²` of `K_q = -g * D_q²` on `ℝ^d`
(`B:eq:Kl-def`, lines 1831–1834); this is the function of `ξ ∈ ℝ^d` whose restriction to `ℤ^d ∖ {0}` is
`HRS.PDE.symbolK d s q`, i.e. `HRS.PDE.SymAux.symExt d s q`. -/
def symbolKRd (d : ℕ) (s : ℝ) (q : Euc d) (ξ : Euc d) : ℝ :=
  (2 * Real.pi * inner ℝ q ξ) ^ 2 * (rieszConst d s * (2 * Real.pi * ‖ξ‖) ^ (s - (d : ℝ)))

end HRS.PDE.ToolboxRd
