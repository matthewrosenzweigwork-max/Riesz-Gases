import HRS.Dynamics.Setup

/-!
# Theorem 2.1: transport improvement for the general matrix, and higher heat-filter orders

Statements only (every theorem ends in `sorry`; no new definitions); relocated from `HRS/SA/Drafts/SAD3.lean` after the
independent review recorded in `docs/ISSUES.md` and subsequent approval.  Row `M:prose:L621-666` (and the subsection of
TeX L3283-3310):

* `general_fluctuation_matrix_transport`: "The transport improvement still applies with the positive density bound"
  (TeX M L618-619), for the general-matrix clause of Theorem 2.1;
* `general_fluctuation_filtered` and `general_fluctuation_matrix_filtered`: "Higher heat-filter orders improve the explicit
  spatial error ..." (TeX M L629-632), made precise in the subsection "Higher heat-filter orders and the general theorem"
  (TeX M L3283-3293, `U:eq:gamma-condition`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GeneralSetup

open HRS

variable {d : ℕ}

/-- Theorem 2.1, general-matrix clause, transport improvement (TeX M L609-619: "The transport improvement still
applies with the positive density bound"; the improvement itself is `H:eq:general-transport-improvement`,
L598-604).  For a constant matrix `M` with `Sym M ≤ 0`, under the adjoint input `AdjointInput M K`
(`H:eq:matrix-adjoint-input`) and the positive density bound `PosDensityWith b.c`, the covariance contribution in the
two Wasserstein estimates on `𝒳_{γ+2,T}` can be replaced by
`C √q_N min{𝔈_N^{1/4} + N^{-1/d}, 𝔈_N^{1/max{2,d-s}} + N^{-1/d}}`.
All other hypotheses are those of `HRS.GeneralSetup.general_fluctuation_matrix`; the conclusion is the
matrix-clause analogue of `HRS.GeneralSetup.general_fluctuation_transport` (paths compared in `E_{γ+2}`). -/
theorem general_fluctuation_matrix_transport (b : GeneralBounds d) (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : Torus.SymNonpos M) (K : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHypM M → S.AdjointInput M K →
      S.PosDensityWith b.c →
      ∀ (N : ℕ) (_ : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P]
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (_ : IsVectorBrownian P W)
      (X : ℝ≥0 → Ω → Config d N) (_ : IsStrongSolution P (S.dynM M N) S.T X₀ W X)
      (_ : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
        (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X)
      (_ : S.EnergyMomentFinite P N X)
      (η₀ : Ω → NegSobolev d S.γ) (_ : Measurable η₀)
      (_ : ProbabilityTheory.IndepFun (fun ω => (X₀ ω, η₀ ω)) (fun ω => fun t => W t ω) P)
      (_ : S.InitialErrorFinite P N 1 X₀ η₀)
      (Y : ℝ → Ω → NegSobolev d ((S.γ : ℝ) + 2))
      (_ : IsLinearFluctuationSolution P (S.dynM M N) (S.ρ N) ((S.γ : ℝ) + 2)
        (qScale N (S.κ N) (S.invβ N)) S.T
        (fun ω => Ascale N (S.κ N) (S.invβ N) • NegSobolev.embed ((S.γ : ℝ) + 2) (η₀ ω)) Y),
      let σ := sigmaScale N (S.κ N) (S.invβ N)
      let A := Ascale N (S.κ N) (S.invβ N)
      let q := qScale N (S.κ N) (S.invβ N)
      let 𝔈 := S.energyMoment P N X
      let cov := Real.sqrt q * min (𝔈 ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d))
        (𝔈 ^ ((1 : ℝ) / max 2 ((d : ℝ) - S.s)) + (N : ℝ) ^ (-(1 : ℝ) / d))
      let Ξ := law P (flucPath ((S.γ : ℝ) + 2) S.T σ X (S.ρ N))
      let YN := law P (toPath ((S.γ : ℝ) + 2) S.T Y)
      wassersteinE 1 Ξ YN ≤ ENNReal.ofReal
          (C * (A * S.initialError P N 1 X₀ η₀ + σ * 𝔈 + cov)) ∧
      (S.EnergyMoment2Finite P N X →
        Integrable (fun ω => ‖flucPath ((S.γ : ℝ) + 2) S.T σ X (S.ρ N) ω‖ ^ 2) P →
        S.InitialErrorFinite P N 2 X₀ η₀ →
        wassersteinE 2 Ξ YN ≤ ENNReal.ofReal
          (C * (A * S.initialError P N 2 X₀ η₀ + σ * S.energyMoment2 P N X + cov))) := by
  sorry

/-- Higher heat-filter orders, gradient dynamics (TeX M L629-632 and L3283-3293).  For an integer `L ≥ 1` and
`γ > max{d+4, d/2 + 1 + max(2L, ⌈(d-s)/2⌉ + 1)}` (`U:eq:gamma-condition`), under the hypotheses of
`HRS.GeneralSetup.general_fluctuation` (same coefficient hypotheses, positive density bound), the covariance terms
`N^{-2/d}` and `N^{-1/d}` of `H:eq:general-smooth`-`H:eq:general-W2` are replaced by `N^{-2L/d}` and `N^{-L/d}`,
"without changing the nonlinear energy condition".  The constant depends on `(b, L)`.  (The transport alternative
"retains its stated `N^{-1/d}` term", i.e. it is `HRS.GeneralSetup.general_fluctuation_transport` unchanged, and is
not restated.)  For `L = 1` the condition on `γ` is implied by `2d + 10 < γ` and the statement is
`general_fluctuation`. -/
theorem general_fluctuation_filtered (b : GeneralBounds d) (L : ℕ) (hL : 1 ≤ L)
    (hγL : max ((d : ℝ) + 4) ((d : ℝ) / 2 + 1 +
        max (2 * (L : ℝ)) ((⌈((d : ℝ) - b.s) / 2⌉ : ℝ) + 1)) < (b.γ : ℝ)) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHyp → S.PosDensityWith b.c →
      ∀ (N : ℕ) (_ : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P]
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (_ : IsVectorBrownian P W)
      (X : ℝ≥0 → Ω → Config d N) (_ : IsStrongSolution P (S.dyn N) S.T X₀ W X)
      (_ : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
        (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X)
      (_ : S.EnergyMomentFinite P N X)
      (η₀ : Ω → NegSobolev d S.γ) (_ : Measurable η₀)
      (_ : ProbabilityTheory.IndepFun (fun ω => (X₀ ω, η₀ ω)) (fun ω => fun t => W t ω) P)
      (_ : S.InitialErrorFinite P N 1 X₀ η₀)
      (Y : ℝ → Ω → NegSobolev d S.γ)
      (_ : IsLinearFluctuationSolution P (S.dyn N) (S.ρ N) S.γ (qScale N (S.κ N) (S.invβ N)) S.T
        (fun ω => Ascale N (S.κ N) (S.invβ N) • η₀ ω) Y),
      let σ := sigmaScale N (S.κ N) (S.invβ N)
      let A := Ascale N (S.κ N) (S.invβ N)
      let q := qScale N (S.κ N) (S.invβ N)
      let 𝔈 := S.energyMoment P N X
      let Ξ := law P (flucPath S.γ S.T σ X (S.ρ N))
      let YN := law P (toPath S.γ S.T Y)
      smoothDist 2 Ξ YN ≤
          C * (A * S.initialError P N 1 X₀ η₀ + σ * 𝔈 +
            q * (Real.sqrt 𝔈 + (N : ℝ) ^ (-(2 * (L : ℝ)) / d))) ∧
      wassersteinE 1 Ξ YN ≤ ENNReal.ofReal
          (C * (A * S.initialError P N 1 X₀ η₀ + σ * 𝔈 +
            Real.sqrt q * (𝔈 ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(L : ℝ) / d)))) ∧
      (S.EnergyMoment2Finite P N X →
        Integrable (fun ω => ‖flucPath S.γ S.T σ X (S.ρ N) ω‖ ^ 2) P →
        S.InitialErrorFinite P N 2 X₀ η₀ →
        wassersteinE 2 Ξ YN ≤ ENNReal.ofReal
          (C * (A * S.initialError P N 2 X₀ η₀ + σ * S.energyMoment2 P N X +
            Real.sqrt q * (𝔈 ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(L : ℝ) / d))))) := by
  sorry

/-- Higher heat-filter orders, general-matrix clause (TeX M L629-632, L3283-3293: "Under the same coefficient and
adjoint hypotheses at this index"): the matrix clause of Theorem 2.1 (`general_fluctuation_matrix`, paths in
`E_{γ+2}`, `AdjointInput M K`, no density bound) with `N^{-2/d}`, `N^{-1/d}` replaced by `N^{-2L/d}`, `N^{-L/d}`
under `U:eq:gamma-condition`.  READING: the TeX sentence is attached to "the covariance terms of Theorem 2.1", which
includes the matrix clause; the TeX does not restate it separately. -/
theorem general_fluctuation_matrix_filtered (b : GeneralBounds d) (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : Torus.SymNonpos M) (K : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (hγL : max ((d : ℝ) + 4) ((d : ℝ) / 2 + 1 +
        max (2 * (L : ℝ)) ((⌈((d : ℝ) - b.s) / 2⌉ : ℝ) + 1)) < (b.γ : ℝ)) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHypM M → S.AdjointInput M K →
      ∀ (N : ℕ) (_ : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P]
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (_ : IsVectorBrownian P W)
      (X : ℝ≥0 → Ω → Config d N) (_ : IsStrongSolution P (S.dynM M N) S.T X₀ W X)
      (_ : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
        (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X)
      (_ : S.EnergyMomentFinite P N X)
      (η₀ : Ω → NegSobolev d S.γ) (_ : Measurable η₀)
      (_ : ProbabilityTheory.IndepFun (fun ω => (X₀ ω, η₀ ω)) (fun ω => fun t => W t ω) P)
      (_ : S.InitialErrorFinite P N 1 X₀ η₀)
      (Y : ℝ → Ω → NegSobolev d ((S.γ : ℝ) + 2))
      (_ : IsLinearFluctuationSolution P (S.dynM M N) (S.ρ N) ((S.γ : ℝ) + 2)
        (qScale N (S.κ N) (S.invβ N)) S.T
        (fun ω => Ascale N (S.κ N) (S.invβ N) • NegSobolev.embed ((S.γ : ℝ) + 2) (η₀ ω)) Y),
      let σ := sigmaScale N (S.κ N) (S.invβ N)
      let A := Ascale N (S.κ N) (S.invβ N)
      let q := qScale N (S.κ N) (S.invβ N)
      let 𝔈 := S.energyMoment P N X
      let Ξ := law P (flucPath ((S.γ : ℝ) + 2) S.T σ X (S.ρ N))
      let YN := law P (toPath ((S.γ : ℝ) + 2) S.T Y)
      smoothDist 2 Ξ YN ≤
          C * (A * S.initialError P N 1 X₀ η₀ + σ * 𝔈 +
            q * (Real.sqrt 𝔈 + (N : ℝ) ^ (-(2 * (L : ℝ)) / d))) ∧
      wassersteinE 1 Ξ YN ≤ ENNReal.ofReal
          (C * (A * S.initialError P N 1 X₀ η₀ + σ * 𝔈 +
            Real.sqrt q * (𝔈 ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(L : ℝ) / d)))) ∧
      (S.EnergyMoment2Finite P N X →
        Integrable (fun ω => ‖flucPath ((S.γ : ℝ) + 2) S.T σ X (S.ρ N) ω‖ ^ 2) P →
        S.InitialErrorFinite P N 2 X₀ η₀ →
        wassersteinE 2 Ξ YN ≤ ENNReal.ofReal
          (C * (A * S.initialError P N 2 X₀ η₀ + σ * S.energyMoment2 P N X +
            Real.sqrt q * (𝔈 ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(L : ℝ) / d))))) := by
  sorry

end HRS.GeneralSetup
