import HRS.Main.Headline
import HRS.Sections.Sec3
import HRS.Sections.Sec5

/-!
# Proposition 5.10 (`M:A:prop:UI`): path-space qualitative clauses

Statements only (every theorem ends in `sorry`); relocated from `HRS/SA/Drafts/SAD1.lean` after the
independent review recorded in `docs/ISSUES.md` and subsequent approval.  Row 5.10 stays `partial`.

TeX (L7036-7038): "Under (A:eq:UI), all qualitative initial-law and shifted-window conclusions of
`H:thm:equilibrium` hold."  The proof (L7056-7066) says: "The same truncation transfers tightness of paths and works on
arbitrary shifted windows.  Initial-field convergence, when assumed, identifies the initial law of the limiting equation."
The finite-dimensional clauses are `HRS.ui_comparison`, `HRS.ui_qualitative`; the three statements below are the path-space
clauses, in `C([0,T]; E_m)` and centred at the Gibbs first marginal, as in `ui_comparison`:

* `ui_path_tight`: tightness of the laws of all shifted windows, uniformly in the window start;
* `ui_path_shifted`: convergence in law of the shifted windows to the stationary window if the start tends to infinity;
* `ui_path_initial`: if the initial fields converge in law, the paths converge in law to the solution of the linearised
  equation with that initial law.

RESTRICTION (recorded in ISSUES): all three assume `m > max{d+1, d/2+2}`.  The printed theorem also covers
`d/2+1 < m` in the stronger topology (TeX L957-966); that range is not stated here.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS

open HRS.Main

variable {d : ℕ}

open Classical in
/-- The window `t ↦ η_N^{u+t} = √N(μ_N^{u+t} - μ)`, `0 ≤ t ≤ T`, of a particle path, centred at a FIXED measure `μ`
(here the Gibbs first marginal `m_{N,β}`), as an element of `𝒳_{m,T}`.  `0` path if the map is not continuous
(junk value; the particle paths are a.s. continuous, `IsStrongSolution.cont`).  Contrast `HRS.Main.windowZeta`,
which centres at the mean empirical measure of the actual law of `X^{u+t}`; for a non-stationary start the two
centres differ and the TeX (L1226-1228) says "centering at the invariant Gibbs marginal is not the same as
centering at the evolving first marginal". -/
def windowGibbs {Ω : Type*} {N : ℕ} (m T u : ℝ) (μ : Measure (Torus d)) (X : ℝ≥0 → Ω → Config d N)
    (ω : Ω) : PathSpace d m T :=
  if h : Continuous fun t : Set.Icc (0 : ℝ) T => etaE m (X (Real.toNNReal (u + t)) ω) μ then
    ⟨_, h⟩ else 0

/-- Proposition 5.10, path-space clause "tightness of paths ... on arbitrary shifted windows"
(TeX L7036-7038, L7064-7065).  Under `Θ(L) → 0` (`A:eq:UI`) and `ν_N^∘ ≪ ℙ_{N,β}`, the laws of the windows
`(η_N^{u+t})_{0≤t≤T}` of the particle paths in `C([0,T]; E_m)`, over ALL `N ≥ 2` and ALL window starts `u ≥ 0`
(no relation between `u` and `N`), form a tight family of probability measures, for `m > max{d+1, d/2+2}`
(the range of `H:eq:equilibrium-smooth`).  (Proof idea in the TeX: the family is tight for the Gibbs start, uniformly in `u`
by stationarity, and `ν(A) ≤ Θ(L) + L ℙ(A)`.) -/
theorem ui_path_tight (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) (T : ℝ) (hT : 0 ≤ T) (S : ParticleSeq d)
    (hS : ∀ T' : ℝ, 0 ≤ T' → S.IsSolutionOn (PDE.mfData d s hs0 hsd V β hβ) T')
    (hSF : ∀ n, ∃ (ℱ : MeasureTheory.Filtration ℝ (S.mΩ n))
      (W' : ℝ≥0 → S.Ω n → (Fin (n + 2) × Fin d) → ℝ),
      IsFilteredSolution (S.P n) ℱ W' (S.W n) (S.X n))
    (hν : ∀ n, (S.P n).map (S.X₀ n) ≪ canonicalGibbs (periodicRiesz d s) V (n + 2) β)
    (hUI : Tendsto (uiTail d s β V (fun n => (S.P n).map (S.X₀ n))) atTop (𝓝 0))
    (m : ℝ) (hm : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m) :
    IsTightMeasureSet {μ : Measure (PathSpace d m T) | ∃ (n : ℕ) (u : ℝ), 0 ≤ u ∧
      μ = (S.P n).map (windowGibbs m T u
        (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) (S.X n))} := by
  sorry

/-- Proposition 5.10, path-space clause "shifted-window conclusions" (TeX L7036-7038, L7064-7065):
under `Θ(L) → 0` and `ν_N^∘ ≪ ℙ_{N,β}`, for every sequence of window starts `u_N ≥ 0` with `u_N → ∞` the shifted windows
`(η_N^{u_N+t})_{0≤t≤T}` converge in law in `C([0,T]; E_m)`, `m > max{d+1, d/2+2}`, to the window
`(Z_β^t)_{0≤t≤T}` of the stationary Gaussian field (any `IsStationaryGaussianField`; window start `0`).
This is the path-space form of the second conclusion of `ui_qualitative` (finite-dimensional vectors at times
`u_n + t_a`) and of `H:eq:equilibrium-smooth`/`-W2` with the `e^{-cu}` error of `A:eq:UI-error`.
READING: "arbitrary shifted windows" cannot mean `u_N` bounded (the limit would then depend on the initial law:
the error `e^{-cu}` of the printed bound does not vanish), so the qualitative window conclusion is stated for `u_N → ∞`;
`ui_path_tight` is the statement for arbitrary `u`. -/
theorem ui_path_shifted (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) (T : ℝ) (hT : 0 ≤ T) (S : ParticleSeq d)
    (hS : ∀ T' : ℝ, 0 ≤ T' → S.IsSolutionOn (PDE.mfData d s hs0 hsd V β hβ) T')
    (hSF : ∀ n, ∃ (ℱ : MeasureTheory.Filtration ℝ (S.mΩ n))
      (W' : ℝ≥0 → S.Ω n → (Fin (n + 2) × Fin d) → ℝ),
      IsFilteredSolution (S.P n) ℱ W' (S.W n) (S.X n))
    (hν : ∀ n, (S.P n).map (S.X₀ n) ≪ canonicalGibbs (periodicRiesz d s) V (n + 2) β)
    (hUI : Tendsto (uiTail d s β V (fun n => (S.P n).map (S.X₀ n))) atTop (𝓝 0))
    (m : ℝ) (hm : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m)
    (u : ℕ → ℝ) (hu0 : ∀ n, 0 ≤ u n) (hu : Tendsto u atTop atTop)
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → NegSobolev d m)
    (hZ : IsStationaryGaussianField P' s β hs0 hsd hβ V ρβ m Z) :
    TendstoInDistribution
      (fun n ω => windowGibbs m T (u n)
        (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) (S.X n) ω)
      atTop (windowPath m T 0 Z) S.P P' := by
  sorry

/-- Proposition 5.10, path-space clause "initial-field convergence, when assumed, identifies the initial law of the
limiting equation" (TeX L7065-7066; Remark L1219-1226): under `Θ(L) → 0` and `ν_N^∘ ≪ ℙ_{N,β}`, if the initial
fields `η_N^0 = √N(μ_N^0 - m_{N,β})` converge in law in `E_m` to `η°` (a random element of `E_m`), then the
trajectories `(η_N^t)_{0≤t≤T}` converge in law in `C([0,T]; E_m)`, `m > max{d+1, d/2+2}`, to any solution `Y` on `(Ω',P')`
of the linearised equation `H:eq:linear-equation` at the stationary background (`ρ^t ≡ ρ_β`, `q = β⁻¹`,
`M = -I`) with `Y^0 = η°`, whose Gaussian part is independent of `Y^0` (`IsLinearFluctuationSolution`).
Shape as `HRS.dynamic_convergence` (Proposition 5.4, last paragraph).  No Gaussianity of `η°` is assumed. -/
theorem ui_path_initial (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) (T : ℝ) (hT : 0 ≤ T) (S : ParticleSeq d)
    (hS : ∀ T' : ℝ, 0 ≤ T' → S.IsSolutionOn (PDE.mfData d s hs0 hsd V β hβ) T')
    (hSF : ∀ n, ∃ (ℱ : MeasureTheory.Filtration ℝ (S.mΩ n))
      (W' : ℝ≥0 → S.Ω n → (Fin (n + 2) × Fin d) → ℝ),
      IsFilteredSolution (S.P n) ℱ W' (S.W n) (S.X n))
    (hν : ∀ n, (S.P n).map (S.X₀ n) ≪ canonicalGibbs (periodicRiesz d s) V (n + 2) β)
    (hUI : Tendsto (uiTail d s β V (fun n => (S.P n).map (S.X₀ n))) atTop (𝓝 0))
    (m : ℝ) (hm : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m)
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η₀ : Ω' → NegSobolev d m)
    (hlaw : TendstoInDistribution
      (fun n ω => etaE m (S.X₀ n ω)
        (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)))
      atTop η₀ S.P P')
    (Y : ℝ → Ω' → NegSobolev d m)
    (hY : IsLinearFluctuationSolution P' (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) m β⁻¹ T η₀ Y) :
    TendstoInDistribution
      (fun n ω => windowGibbs m T 0
        (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) (S.X n) ω)
      atTop (toPath m T Y) S.P P' := by
  sorry

end HRS
