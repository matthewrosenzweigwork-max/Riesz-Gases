import HRS.MC.S7ChaosIIDVocab

/-!
# Proposition 7.18: the printed independent-Gaussian form of `Q_ε` (`E:eq:Qepsilon`, TeX L9770-9780)

Statements only (every theorem ends in `sorry`).  The TeX defines `Q_ε = ½ ∑_{ij} (A_ε)_{ij} (G_i G_j - δ_ij)` with
INDEPENDENT standard Gaussians `G_i` and `A_ε = C^{1/2} H_ε C^{1/2}`, where `C = C_{β,μ}` is the susceptibility
covariance and `H_ε` the Hilbert-Schmidt operator of the kernel `h_{φ,ε}`.  `HRS/MC/S7Chaos.lean` states
`chaos_laws_not_tight` and `chaos_no_L2_limit` for a correlated Gaussian field `G` with covariance `C` instead
(`s7_GaussData`, `s7_IsChaosLimit`).  This file states the bridge and the two iid-form versions.

Convention.  A matrix `S` with `∑_k S_ik S_jk = C(e_i, e_j)` (`s7_IsCovFactor`) replaces `C^{1/2}`: with `g` iid and
`G_i = ∑_k S_ik g_k` the pair `(G, Q)` is the correlated representation, and the iid matrix is `A = Sᵀ H S`
(`s7_conjCoeff`); for the symmetric positive semidefinite root `S = C^{1/2}` this is `C^{1/2} H C^{1/2}`
(`chaos_covariance_factor_exists_sym`).  The law of `Q_ε` does not depend on the factor.

RESTRICTION (to be recorded in ISSUES): of the displays of Proposition 7.18 only the two sentence-level statements
(non-tightness, no square-mean limit) get an iid-form theorem here; the other displays remain in the correlated form.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS

open HRS.MC.Sec7

variable {d : ℕ}

/-- Bridge from independent to correlated Gaussians (the mathematics behind `E:eq:Qepsilon`).  For a covariance
factor `S` and iid standard Gaussians `g` there are measurable `G_i`, the `L²(P)`-limits of `∑_{k<n} S_ik g_k`, forming
a Gaussian field with covariance `C` (`s7_GaussData`), such that for EVERY symmetric Hilbert-Schmidt coefficient matrix
of a kernel `h`: `SᵀHS` is symmetric Hilbert-Schmidt, and every `L²`-limit `Q` of the iid sections
`½ ∑_{k,l<n} (SᵀHS)_{kl} (g_k g_l - δ_kl)` is the correlated chaos limit `s7_IsChaosLimit` for the same `G`. -/
theorem chaos_iid_representation (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (e : ℕ → Torus d → ℝ)
    (he : IsONBL2Zero (withDensityReal ρ) e) (S : ℕ → ℕ → ℝ) (hS : s7_IsCovFactor d s β ρ e S)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (g : ℕ → Ω → ℝ)
    (hg : IsStdGaussianSeq P g) :
    ∃ G : ℕ → Ω → ℝ,
      s7_GaussData d s β ρ e P G ∧
      (∀ i, TendstoL2 P (fun n ω => ∑ k ∈ Finset.range n, S i k * g k ω) (G i)) ∧
      ∀ h : Torus d → Torus d → ℝ, IsSymmetricHS (s7_kernelCoeff ρ e h) →
        IsSymmetricHS (s7_conjCoeff S (s7_kernelCoeff ρ e h)) ∧
        ∀ Q : Ω → ℝ, TendstoL2 P (chaosSection (s7_conjCoeff S (s7_kernelCoeff ρ e h)) g) Q →
          s7_IsChaosLimit d s β ρ e P G h Q := by
  sorry

/-- The symmetric positive semidefinite square root `C^{1/2}` of the susceptibility covariance exists as a matrix
in the basis `e`: a symmetric `S` with `∑_k S_ik S_jk = C(e_i, e_j)` and `∑_{ij} x_i x_j S_ij ≥ 0` for every finite
vector `x`.  (With this `S`, `s7_conjCoeff S H` is `C^{1/2} H C^{1/2}`, the matrix `A` of `E:eq:Qepsilon`.) -/
theorem chaos_covariance_factor_exists_sym (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ}
    (hβ : 0 < β) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (e : ℕ → Torus d → ℝ)
    (he : IsONBL2Zero (withDensityReal ρ) e) :
    ∃ S : ℕ → ℕ → ℝ, s7_IsCovFactor d s β ρ e S ∧ (∀ i j, S i j = S j i) ∧
      ∀ (n : ℕ) (x : Fin n → ℝ), 0 ≤ ∑ i, ∑ j, x i * x j * S i j := by
  sorry

/-- Proposition 7.18, "In particular its laws are not tight", in the printed independent form: for `d/2 ≤ s < d`, for
iid standard Gaussians `g`, a covariance factor `S`, and `Q_ε` the `L²`-limit of the sections of
`½ ∑ (Sᵀ H_ε S)_{kl} (g_k g_l - δ_kl)` (`H_ε` the coefficient matrix of `hCut d s φ ε`), the laws of `Q_{ε_n}` are
not tight along every sequence `ε_n ↓ 0`.  Same conclusion as `chaos_laws_not_tight`. -/
theorem chaos_laws_not_tight_iid (hd : 2 ≤ d) {s : ℝ} (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d) {β : ℝ}
    (hβ : 0 < β) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (φ : Torus d → ℝ)
    (hφ : Torus.IsSmooth φ) (hnc : ∃ x y, φ x ≠ φ y) (e : ℕ → Torus d → ℝ)
    (he : IsONBL2Zero (withDensityReal ρ) e) (S : ℕ → ℕ → ℝ) (hS : s7_IsCovFactor d s β ρ e S)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (g : ℕ → Ω → ℝ)
    (hg : IsStdGaussianSeq P g) (Q : ℝ → Ω → ℝ)
    (hQ : ∀ ε, 0 < ε → TendstoL2 P
      (chaosSection (s7_conjCoeff S (s7_kernelCoeff ρ e (hCut d s φ ε))) g) (Q ε))
    (ε : ℕ → ℝ) (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0)) :
    ¬ IsTightMeasureSet (Set.range fun n : ℕ => P.map (Q (ε n))) := by
  sorry

/-- Proposition 7.18, last sentence, in the printed independent form: same hypotheses as
`chaos_laws_not_tight_iid`; there is no (a.e. measurable) `Q₀` with `E|Q_{ε_n} - Q₀|² → 0`. -/
theorem chaos_no_L2_limit_iid (hd : 2 ≤ d) {s : ℝ} (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d) {β : ℝ}
    (hβ : 0 < β) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (φ : Torus d → ℝ)
    (hφ : Torus.IsSmooth φ) (hnc : ∃ x y, φ x ≠ φ y) (e : ℕ → Torus d → ℝ)
    (he : IsONBL2Zero (withDensityReal ρ) e) (S : ℕ → ℕ → ℝ) (hS : s7_IsCovFactor d s β ρ e S)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (g : ℕ → Ω → ℝ)
    (hg : IsStdGaussianSeq P g) (Q : ℝ → Ω → ℝ)
    (hQ : ∀ ε, 0 < ε → TendstoL2 P
      (chaosSection (s7_conjCoeff S (s7_kernelCoeff ρ e (hCut d s φ ε))) g) (Q ε))
    (ε : ℕ → ℝ) (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0)) :
    ¬ ∃ Q₀ : Ω → ℝ, AEMeasurable Q₀ P ∧
      Tendsto (fun n : ℕ => ∫⁻ ω, ‖Q (ε n) ω - Q₀ ω‖ₑ ^ 2 ∂P) atTop (𝓝 0) := by
  sorry

end HRS
