import HRS.MC.S7Chaos
import HRS.Prob.Gaussian

/-!
# Vocabulary for the iid form of Proposition 7.18 (`E:eq:Qepsilon`; sorry-free)

Definitions used by the statements of `HRS/MC/S7ChaosIID.lean`.  The TeX defines `Q_ε = ½ ∑_{ij} (A_ε)_{ij} (G_i G_j - δ_ij)` with
INDEPENDENT standard Gaussians `G_i` and `A_ε = C^{1/2} H_ε C^{1/2}`, where `C = C_{β,μ}` is the susceptibility
covariance and `H_ε` the Hilbert-Schmidt operator of the kernel `h_{φ,ε}`.  `HRS/MC/S7Chaos.lean` states
`chaos_laws_not_tight` and `chaos_no_L2_limit` for a correlated Gaussian field `G` with covariance `C` instead
(`s7_GaussData`, `s7_IsChaosLimit`).  `HRS/MC/S7ChaosIID.lean` states the bridge, the symmetric root and the two iid-form versions.

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

/-- `H_ij = ∬ h e_i e_j dμ dμ`: the matrix of the kernel `h` in the orthonormal basis `e` of `L²_0(μ)`, `μ = ρ dx`
(the same expression as in `s7_IsChaosLimit`; `h` and its canonical centring have the same coefficients because
`e_i` is centred). -/
def s7_kernelCoeff (ρ : Torus d → ℝ) (e : ℕ → Torus d → ℝ) (h : Torus d → Torus d → ℝ) (i j : ℕ) : ℝ :=
  ∫ x, ∫ y, h x y * e i x * e j y ∂(withDensityReal ρ) ∂(withDensityReal ρ)

/-- `S = (S_ik)` is a factor of the susceptibility covariance in the basis `e`:
`∑_k S_ik S_jk = C_{β,μ}(e_i, e_j)` for all `i, j` (`C^{1/2}` is the symmetric positive semidefinite factor). -/
def s7_IsCovFactor (d : ℕ) (s β : ℝ) (ρ : Torus d → ℝ) (e : ℕ → Torus d → ℝ) (S : ℕ → ℕ → ℝ) : Prop :=
  ∀ i j, HasSum (fun k => S i k * S j k)
    (susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j))

/-- `A = SᵀHS`, that is `A_kl = ∑_i ∑_j S_ik H_ij S_jl`.  (An iterated `tsum`; absolutely summable when `S` is a
covariance factor and `H` is Hilbert-Schmidt, see `chaos_iid_representation`.) -/
def s7_conjCoeff (S H : ℕ → ℕ → ℝ) (k l : ℕ) : ℝ := ∑' i, ∑' j, S i k * H i j * S j l

end HRS
