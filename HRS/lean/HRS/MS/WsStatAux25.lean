import HRS.MS.WsStatAux24

/-!
# S21 packet I-3: the stationary master comparison

`s21_master`: on the Gaussian coupling space of the particle martingale (`gff_adapted_coupling_trace`), the centred field
`s21XiPath = window (sigma (mu_N^t - nubar))` is compared with `gamma0 * Gamma` (`*` = convolution on `C([0,T];B_m)`), where `gamma0` is any
probability measure on the path space (the Gaussian initial path of S4.5 + S5 initial-path packets G, H) and `Gamma` is the law of the
path of the Gaussian martingale `T G` (a Gaussian measure with the noise covariance `noiseCovW`).  Errors: the covariance (trace) term, the
`L^1` norm of the centred remainder (`s21_centered_coord`, `s21_Rt_bound`), and the initial-path distances
`smoothDist 2 (law k0path) gamma0`, `W_1(law k0path, gamma0)`.

The proof is that of `s56_master` with the independent initial state: no initial enlargement is needed, since the initial state `s21K0c`
is `F_0`-measurable and hence independent of the Gaussian martingale (`gf_coupling_indep`, `s21_recon_indep`); the law of
`k0path + window(recon G)` is the convolution `law k0path * Gamma` (`law_add_indep`-type identification), and
`t25_smoothDist_conv_le`, `s21_wasserstein_conv_le` contract the convolution.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath HRS.MP.RdRem HRS.GF HRS.Uniform HRS.Whole.AppendixA
open HRS (Euc)

variable {d : ℕ}

/-- The centred initial path `t ↦ A(k_0^c)(t)`. -/
def s21Path0 {b : WholeBounds d} (hT : 0 ≤ b.T) (S : WholeSetup b) {N : ℕ} {Ω : Type*}
    (X : ℝ≥0 → Ω → EucConfig d N) (νb : Measure (Euc d)) (ζ : Ω) : OscPath d b.m b.T :=
  s56EvalPath hT (s21K0c S X νb ζ)

/-- The centred field path `t ↦ σ(μ_N^t - ν̄)`. -/
def s21XiPath {b : WholeBounds d} (S : WholeSetup b) {N : ℕ} {Ω : Type*}
    (X : ℝ≥0 → Ω → EucConfig d N) (νb : Measure (Euc d)) (ζ : Ω) : OscPath d b.m b.T :=
  windowPathOf b.m b.T 0 fun t => s21Xi S X νb t ζ

end HRS.MS.S21
