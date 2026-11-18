import HRS.Equilibrium.PairCorrection
import HRS.PDE.MeanField

/-!
# Prop 4.13 (`pair_poisson`): the diagonal parametrix -- definitions (packet PARX-PLAN)

Source: main manuscript `M:Q:prop:poisson`, statement lines 4709-4735, proof lines 4736-4863.
See `docs/external/parametrix-plan.md` for the packet decomposition.

Everything in this file is a definition (no `sorry`).  Conventions used throughout the parametrix:

* every constructed kernel is `0` on the diagonal (`offZero`), so Bochner junk on `x = y` is
  harmless and measurability is the continuity off the (closed, null) diagonal;
* a kernel is extended across the diagonal only through `diagExt`, which uses `limUnder` and is
  meaningful exactly when the kernel extends continuously;
* conormal classes `Conormal` are defined in the chart `(X, z) = ((x+y)/2, x-y)` of the
  covering space (`toChart`), with `X`-derivatives free and `z`-derivatives costing `r^{-1}`; the
  weight is `1 + r^{-(σ+c)}(1+|log r|)^b`, so bounded kernels belong to every class and classes of
  negative order mean "bounded derivatives".
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

/-! ### Standing hypotheses -/

/-- The standing hypotheses of Proposition 4.13 (`pair_poisson`). -/
structure ParxHyp (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (β : ℝ) (ρ : Torus d → ℝ) : Prop where
  two_le : 2 ≤ d
  crit : s = (d : ℝ) / 2
  beta_pos : 0 < β
  V_smooth : Torus.IsSmooth V
  thermal : IsThermalDensity (periodicRiesz d s) V β ρ
  rho_smooth : SmoothPosDensity ρ

variable {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ}

theorem ParxHyp.s_nonneg (H : ParxHyp d s V β ρ) : 0 ≤ s := by
  rw [H.crit]; positivity

theorem ParxHyp.s_lt (H : ParxHyp d s V β ρ) : s < d := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast H.two_le
  rw [H.crit]; linarith

/-- The dynamics data `M = -I`, `ν = β⁻¹` of the stationary equation (`PDE.mfData`). -/
def ParxHyp.dyn (H : ParxHyp d s V β ρ) : DynData d :=
  PDE.mfData d s H.s_nonneg H.s_lt V β H.beta_pos

/-! ### Charts near the diagonal -/

/-- Midpoint/difference chart of a kernel on the covering space: `(X, z) ↦ F(X + z/2, X - z/2)`. -/
def toChart (F : Torus d → Torus d → ℝ) : Euc d × Euc d → ℝ :=
  fun p => F (Torus.mk (p.1 + (1 / 2 : ℝ) • p.2)) (Torus.mk (p.1 - (1 / 2 : ℝ) • p.2))

/-- A kernel on the torus from a chart function `G(X, z)`; the value on the diagonal is `0`; the
chart point is `(rep y + z/2, z)` with `z` the centred representative of `x - y`.  Only
meaningful for `G` that is `ℤ^d`-periodic in `X`. -/
def ofChart (G : Euc d × Euc d → ℝ) : Torus d → Torus d → ℝ := fun x y =>
  if x = y then 0
  else G (Torus.rep y + (1 / 2 : ℝ) • Torus.centeredRep (x - y), Torus.centeredRep (x - y))

/-- Set a kernel to `0` on the diagonal. -/
def offZero (F : Torus d → Torus d → ℝ) : Torus d → Torus d → ℝ :=
  fun x y => if x = y then 0 else F x y

/-- Extension across the diagonal by the limit `lim_{y' → x, y' ≠ x} F(x, y')` (junk if it does
not exist; used only for kernels that extend continuously). -/
def diagExt (F : Torus d → Torus d → ℝ) : Torus d → Torus d → ℝ := fun x y =>
  if x = y then limUnder (𝓝[≠] x) (fun y' => F x y') else F x y

/-! ### Conormal classes -/

/-- Radius of the chart region in which the conormal bounds are imposed. -/
def r0 : ℝ := 1 / 8

/-- `∂_X^a ∂_z^c G(X, z)`, as an iterated derivative in `X` of the `z`-jet of order `c`. -/
def mixedDeriv (a c : ℕ) (G : Euc d × Euc d → ℝ) (X z : Euc d) :
    ContinuousMultilinearMap ℝ (fun _ : Fin a => Euc d)
      (ContinuousMultilinearMap ℝ (fun _ : Fin c => Euc d) ℝ) :=
  iteratedFDeriv ℝ a (fun X' => iteratedFDeriv ℝ c (fun z' => G (X', z')) z) X

/-- Conormal class of order `σ` with logarithm powers `b c` (at `z`-derivative order `c`), finite
differentiability order `m` and constant `B` (`Q:eq:conormal`, source line 4791):
`C^m` off the diagonal, `|∂_X^a ∂_z^c F| ≤ B (1 + r^{-σ-c} (1+|log r|)^{b c})` for `a + c ≤ m` and
`0 < r = |z| < r₀` in the chart, and the full derivatives up to order `m` are `≤ B` where
`eucDist ≥ r₀`.  A bounded smooth kernel belongs to every class (the weight is `≥ 1`). -/
structure ConormalL (σ : ℝ) (b : ℕ → ℕ) (m : ℕ) (B : ℝ) (F : Torus d → Torus d → ℝ) : Prop where
  smooth : ContDiffOn ℝ (m : WithTop ℕ∞) (lift2 F) (offDiag d)
  near : ∀ a c : ℕ, a + c ≤ m → ∀ X z : Euc d, z ≠ 0 → ‖z‖ < r0 →
    ‖mixedDeriv a c (toChart F) X z‖ ≤
      B * (1 + ‖z‖ ^ (-(σ + c)) * (1 + |Real.log ‖z‖|) ^ b c)
  far : ∀ k : ℕ, k ≤ m → ∀ p : Euc d × Euc d, p ∈ offDiag d →
    r0 ≤ Torus.eucDist (Torus.mk p.1) (Torus.mk p.2) → ‖iteratedFDeriv ℝ k (lift2 F) p‖ ≤ B

/-- Conormal class with a single logarithm power `b`. -/
abbrev Conormal (σ : ℝ) (b : ℕ) (m : ℕ) (B : ℝ) (F : Torus d → Torus d → ℝ) : Prop :=
  ConormalL σ (fun _ => b) m B F

/-! ### The local inverse `𝒩` (`Q:eq:Newton-local`, source line 4795) -/

/-- Smooth radial cutoff `χ`: `= 1` on `|z| ≤ 1/32`, supported in `|z| < 1/16`. -/
def chi (d : ℕ) : Euc d → ℝ :=
  fun z => (⟨1 / 32, 1 / 16, by norm_num, by norm_num⟩ : ContDiffBump (0 : Euc d)) z

/-- Fundamental solution `Γ` of `-2ν Δ_z` on `ℝ^d` (`d ≥ 2`): `E/(2ν)` with `E = -(2π)⁻¹ log|z|` for
`d = 2` and `E = |z|^{2-d} / ((d-2) ω_d)` for `d ≥ 3`, `ω_d = d · vol(B₁)`. -/
def newtonKernel (d : ℕ) (ν : ℝ) (z : Euc d) : ℝ :=
  (1 / (2 * ν)) *
    (if d = 2 then -(1 / (2 * Real.pi)) * Real.log ‖z‖
     else (1 / (((d : ℝ) - 2) * ((d : ℝ) * (volume (Metric.ball (0 : Euc d) 1)).toReal))) *
        ‖z‖ ^ (2 - (d : ℝ)))

/-- `χ(z) ∫ Γ(z - z') χ(z') G(X, z') dz'` on chart functions. -/
def newtonChart (d : ℕ) (ν : ℝ) (G : Euc d × Euc d → ℝ) : Euc d × Euc d → ℝ :=
  fun p => chi d p.2 * ∫ w : Euc d, newtonKernel d ν (p.2 - w) * (chi d w * G (p.1, w))

/-- `𝒩F = P_x P_y [χ(z) ∫ Γ(z - z') χ(z') F(X, z') dz']` (`Q:eq:Newton-local`), `ν = β⁻¹`,
`P = P_μ`, `μ = ρ dx`; `0` on the diagonal. -/
def newtonOp (d : ℕ) (β : ℝ) (ρ : Torus d → ℝ) (F : Torus d → Torus d → ℝ) :
    Torus d → Torus d → ℝ :=
  fun x y => if x = y then 0
    else canonicalCenter (withDensityReal ρ) (ofChart (newtonChart d β⁻¹ (toChart F))) x y

/-- The defect map `ℰ = I + (𝒜_x + 𝒜_y) 𝒩` (`Q:eq:defect-map`, source line 4807); `0` on the
diagonal. -/
def defectOp (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (β : ℝ) (ρ : Torus d → ℝ)
    (F : Torus d → Torus d → ℝ) : Torus d → Torus d → ℝ :=
  fun x y => if x = y then 0
    else F x y + genFst d s V β ρ (newtonOp d β ρ F) x y + genSnd d s V β ρ (newtonOp d β ρ F) x y

/-- `R_0 = H_f`, `R_{j+1} = ℰ R_j` (`Q:eq:parametrix-iteration`, source line 4840). -/
def parxR (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (β : ℝ) (ρ : Torus d → ℝ) (f : Torus d → ℝ) :
    ℕ → Torus d → Torus d → ℝ
  | 0 => offZero (Hsource d s ρ f)
  | j + 1 => defectOp d s V β ρ (parxR d s V β ρ f j)

/-- `ψ^loc_L = ∑_{j<L} 𝒩 R_j` (`Q:eq:parametrix-iteration`). -/
def parxPsi (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (β : ℝ) (ρ : Torus d → ℝ) (f : Torus d → ℝ)
    (L : ℕ) : Torus d → Torus d → ℝ :=
  fun x y => ∑ j ∈ Finset.range L, newtonOp d β ρ (parxR d s V β ρ f j) x y

/-! ### Numerology -/

/-- Number of defect steps for a target differentiability `J` of the remainder:
`s - L/2 + J + 1 = -2 < 0` for `s = d/2`. -/
def parxL (d J : ℕ) : ℕ := 2 * J + d + 6

/-- Derivative index of `f` used when the remainder `R_L` must be `C^J`: the source `H_f` is
needed in the class with `m_0 = (J+1) + 2L` conormal derivatives, i.e. `m_0 + 2` derivatives of `f`. -/
def parxK (d J : ℕ) : ℕ := 5 * J + 2 * d + 15

/-- Differentiability of the remainder that the pair inverse is required to accept
(`d + 12`; the tensor-Sobolev proof gives `2 j₀` with `j₀` the least even integer `> d/2 + 4`). -/
def parxJ (d : ℕ) : ℕ := d + 12

/-! ### The pair inverse as used by the assembly (Lemma 4.14, quantitative form) -/

/-- What the assembly needs from the two-copy inverse `Ψ_R = ∫₀^∞ U_t^x U_t^y R dt` at
differentiability `J`: it maps doubly centred `C^J` kernels linearly into doubly centred `C²`
kernels with `‖Ψ_R‖_{C²} ≤ C ‖R‖_{C^J}`, solves `-(𝒜_x+𝒜_y)Ψ_R = R`, preserves symmetry, and is a
left inverse: if `Δ ∈ C^{J+2}` is doubly centred and `(𝒜_x + 𝒜_y)Δ = R'` with `R'` doubly centred in
`C^J`, then `Ψ_{R'} = -Δ` (the `C^{J+2}` hypothesis on `Δ`: docs/ISSUES.md §I, PX7). -/
def PairInverseSpec (H : ParxHyp d s V β ρ) (J : ℕ) : Prop :=
  ∃ Cinv : ℝ, 0 ≤ Cinv ∧
    (∀ R : Torus d → Torus d → ℝ, PDE.IsCk2 J R → PDE.DoublyCentered (withDensityReal ρ) R →
      PDE.IsCk2 2 (PDE.pairInverse H.dyn ρ R) ∧
      PDE.DoublyCentered (withDensityReal ρ) (PDE.pairInverse H.dyn ρ R) ∧
      PDE.cbNorm2 2 (PDE.pairInverse H.dyn ρ R) ≤ Cinv * PDE.cbNorm2 J R ∧
      ∀ x y, -(PDE.centeredGen H.dyn ρ (fun x' => PDE.pairInverse H.dyn ρ R x' y) x +
        PDE.centeredGen H.dyn ρ (fun y' => PDE.pairInverse H.dyn ρ R x y') y) = R x y) ∧
    (∀ (R R' : Torus d → Torus d → ℝ) (a b : ℝ), PDE.IsCk2 J R → PDE.IsCk2 J R' →
      PDE.pairInverse H.dyn ρ (fun x y => a * R x y + b * R' x y) =
        fun x y => a * PDE.pairInverse H.dyn ρ R x y + b * PDE.pairInverse H.dyn ρ R' x y) ∧
    (∀ R : Torus d → Torus d → ℝ, PDE.IsCk2 J R → (∀ x y, R x y = R y x) →
      ∀ x y, PDE.pairInverse H.dyn ρ R x y = PDE.pairInverse H.dyn ρ R y x) ∧
    (∀ Δ R' : Torus d → Torus d → ℝ, PDE.IsCk2 (J + 2) Δ → PDE.IsCk2 J R' →
      PDE.DoublyCentered (withDensityReal ρ) Δ → PDE.DoublyCentered (withDensityReal ρ) R' →
      (∀ x y, PDE.centeredGen H.dyn ρ (fun x' => Δ x' y) x +
        PDE.centeredGen H.dyn ρ (fun y' => Δ x y') y = R' x y) →
      PDE.pairInverse H.dyn ρ R' = fun x y => -Δ x y)

end HRS.Parx

end
