import HRS.Whole.AppendixAAdjoint
import HRS.Whole.AppendixALemmas
import HRS.MH.AdjointRdDefs
import HRS.MH.ScreenedDefs

/-!
# Proposition S.A.12 `B:thm:adjoint-rd` on `R^d`: statement-only packet specification

Plan and mathematics: `HRS/MH/AdjointRdPlan.md` (read it first: it fixes the route, the sizes, the order, the statement
defects, and what is needed from S.A.33).  Every theorem below is `sorry`; the statements compile.  The six frozen
statements `adjoint_rd`, `adjoint_rd_classical`, `adjoint_rd_planewave`, `adjoint_rd_sobolev`, `adjoint_rd_stability`,
`adjoint_rd_weighted` are re-proved at the very end by `adjoint_rd_proof`, ..., `adjoint_rd_weighted_proof`, with the
types of the frozen declarations.

Conventions.  `Euc d = EuclideanSpace ℝ (Fin d)`.  A packet is one `theorem` (or a few closely related ones); its
docstring gives the size (S/M: at most about 250 lines; L: larger), the proof route, and the existing lemmas to
use (names verified by grep in the plan; "not verified" otherwise).  Where a hypothesis list is long it is bundled in one
of the structures of the section "Definitions" (`IsClassicalSol`, `PerData`).  No frozen statement is edited.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.AdjointRd

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

/-! ### Definitions -/

/-! ### Group N: norm calculus -/

/-- **N1** (size S).  Triangle inequality, a.e.-invariance, monotonicity in the order, and homogeneity of the Fourier
Sobolev norm `sobolevNormE` and of `ulocNormE` (the Mathlib/repository API for `sobolevNormE` is only the multiplier and
translation lemmas, plan section 2).  Route: `MemSobolev r u` is `MemLp u 2` plus the weighted Fourier integrability
(`HRS/PDE/ToolboxRd/Defs.lean:45`); `HRS.PDE.ToolboxRd.fourierL2_add`, `fourierL2_sub`, `fourierL2_smul`,
`fourierL2_congr_ae`, `memSobolev_mono` (Fourier.lean:73-89, 65, 374) and Minkowski in the weighted `L²(ℝ^d)`.  The
`ulocNormE` statements follow by taking suprema. -/
theorem norm_calculus (hd : 1 ≤ d) :
    (∀ (r : ℝ) (u v : Euc d → ℝ), sobolevNormE r (fun x => u x + v x) ≤ sobolevNormE r u + sobolevNormE r v) ∧
    (∀ (r : ℝ) (u v : Euc d → ℝ), sobolevNormE r (fun x => u x - v x) ≤ sobolevNormE r u + sobolevNormE r v) ∧
    (∀ (r : ℝ) (u v : Euc d → ℝ), u =ᵐ[volume] v → sobolevNormE r u = sobolevNormE r v) ∧
    (∀ (r r' : ℝ) (u : Euc d → ℝ), r' ≤ r → sobolevNormE r' u ≤ sobolevNormE r u) ∧
    (∀ (r c : ℝ) (u : Euc d → ℝ), sobolevNormE r (fun x => c * u x) = ENNReal.ofReal |c| * sobolevNormE r u) ∧
    (∀ (m : ℕ) (χ u v : Euc d → ℝ), ulocNormE m χ (fun x => u x - v x) ≤ ulocNormE m χ u + ulocNormE m χ v) ∧
    (∀ (m : ℕ) (χ u v : Euc d → ℝ), u =ᵐ[volume] v → ulocNormE m χ u = ulocNormE m χ v) ∧
    (∀ (m m' : ℕ) (χ u : Euc d → ℝ), m' ≤ m → ulocNormE m' χ u ≤ ulocNormE m χ u) ∧
    (∀ (m : ℕ) (χ : Euc d → ℝ) (c : ℝ) (u : Euc d → ℝ),
      ulocNormE m χ (fun x => c * u x) = ENNReal.ofReal |c| * ulocNormE m χ u) := by
  sorry

/-- **N2** (size M/L).  EXACT Plancherel identity: for `u ∈ C_c^∞`, `‖u‖²_{H^m} = ∑_{j≤m}C(m,j)∑_{idx ∈ [d]^j}‖∂^{idx}u‖²_{L²}`
(`jetSq m 1`; `sobolevNormE m u` is finite).  Route: `(1+4π²|ξ|²)^m = ∑_jC(m,j)(4π²)^j(∑_iξ_i²)^j` and
`(∑_iξ_i²)^j = ∑_{idx}∏_lξ_{idx_l}²`; the Fourier transform of `∂_iu` is `2πiξ_iû` for `u ∈ C_c^∞`
(Mathlib: `Real.fourier`/`VectorFourier` derivative lemmas, or `SchwartzMap.fourierTransformCLE` and
`SchwartzMap.fourier_...deriv`; the repository has `HRS.PDE.ToolboxRd.inner_FT`, `integral_norm_sq_fourierL2`,
Fourier.lean:42, 246, but no derivative-sum form: not verified by grep; `HRS/MS/UlocWeighted.lean` uses `partialDeriv`
only through `wJet`). -/
theorem sobolev_jet_eq (hd : 1 ≤ d) (m : ℕ) (u : Euc d → ℝ) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    sobolevNormE (m : ℝ) u = ENNReal.ofReal (Real.sqrt (jetSq m (fun _ => 1) u)) := by
  sorry

/-- **N3** (size M).  Lower semicontinuity under weak (distributional) convergence: if `∫u_nψ → ∫uψ` for every `ψ ∈ C_c^∞`
and the `H^m_uloc` norms of `u_n` are bounded by `B`, then `‖u‖_{H^m_uloc} ≤ B` (and for the Fourier norm: if
`‖u_n‖_{H^m} ≤ B` then `‖u‖_{H^m} ≤ B`; for `varpiNormE`: `‖u‖_{H^m(ϖ)} ≤ liminf ‖u_n‖_{H^m(ϖ)}` when the norms are finite).
Route: `sobolevNormE m (χ(·-z)u)` is the norm of a bounded set in the Hilbert space `H^m`; the functionals
`u ↦ ∫ (χ(·-z)u) ψ` with `ψ ∈ C_c^∞` are dense in `(H^m)^*` and uniformly bounded on the ball (Banach-Alaoglu in the
separable Hilbert space `H^m`, or directly `‖v‖ = sup_{‖ψ‖_{H^{-m}} ≤ 1}∫vψ`). -/
theorem norm_lsc (hd : 1 ≤ d) (m : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (B : ℝ)
    (un : ℕ → Euc d → ℝ) (u : Euc d → ℝ)
    (hconv : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → Tendsto (fun n => ∫ x, un n x * ψ x) atTop (𝓝 (∫ x, u x * ψ x)))
    (hB : ∀ n, ulocNormE m χ (un n) ≤ ENNReal.ofReal B) (hint : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → Integrable (fun x => u x * ψ x)) :
    ulocNormE m χ u ≤ ENNReal.ofReal B ∧
    (∀ B' : ℝ, (∀ n, sobolevNormE (m : ℝ) (un n) ≤ ENNReal.ofReal B') → sobolevNormE (m : ℝ) u ≤ ENNReal.ofReal B') ∧
    varpiNormE m χ u ≤ liminf (fun n => varpiNormE m χ (un n)) atTop := by
  sorry

/-! ### Group U: uniqueness (from S.A.33) -/

/-- **U1** (size M).  The weak term of `IsForwardSolutionRd` equals the pairing `forwardPairing` of S.A.33 for every
`F(σ)` of locally bounded `L²`-uloc type (so that every one of the `d²` nonlocal terms is separately integrable and
the finite sum can be pulled out of the integral).  Route: `D.coeff μ` unfolds to `⟨D.s, D.M, D.invβ, meanFieldDriftW D (μ ·), μ⟩`;
`movDiv (ψ•b) = ∑_i ∂_i(b_iψ)` because `b ∈ C¹` (packet C1a); `∂_i(g*ψ) = g*∂_iψ` for `ψ ∈ C_c^∞`
(`gradient (convFun g ψ) y i = kernelConvDeriv d s i ψ y`; differentiation under the integral with the locally
integrable kernel, `s < d`); integrability of `F(σ)·∂_j(μ·(g*∂_iψ))` from the uloc bound and the decay
`⟨y⟩^{-(d+3)}` of `μ`, `|∇(g*ψ)(y)| ≤ C⟨y⟩^{-s-1}`. -/
theorem weakTerm_eq_forwardPairing (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (MB Λ ΛV G₀ νbar T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (D : WholeDyn d) (μ : ℝ → Euc d → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T)
    (ψ : Euc d → ℝ) (hψ : IsCcInfty ψ) (F : ℝ → Euc d → ℝ) (σ : ℝ) (hσ : σ ∈ Icc (0 : ℝ) t)
    (hF : ulocNormE 0 χ (F σ) < ⊤) :
    forwardWeakTerm (D.coeff μ) t F ψ σ =
      HRS.Whole.AppendixALemmas.forwardPairing D μ t σ (F σ) ψ := by
  sorry

/-- **U2** (size M).  The uniqueness clause of `adjoint_rd` (and the uniqueness used in `_classical`, `_sobolev`, `_weighted`,
`_stability`): two solutions in `IsUlocSolutionRd` with the same datum agree a.e. at every time.  Route: `z = F₁ - F₂`;
`IsUlBounded χ 1 t z` from `norm_calculus` (triangle, order monotonicity `m ≥ 1`); `IsForwardDistSolutionW` from
`weakTerm_eq_forwardPairing` and linearity of `eq` and of `∫ σ` (the integrability fields of `IsForwardSolutionRd`
give `integrable_σ` for `z`); `z 0 =ᵐ 0` from `eq` at `τ = 0` (`∫ F_a(0)ψ = ∫φψ` for all `ψ ∈ C_c^∞`, plus local
integrability of `F_a(0)` from `integrable_x` with `ψ ≥ 1` on a ball, plus the fundamental lemma of the calculus of
variations); then `HRS.Whole.AppendixALemmas.uloc_uniqueness` (S.A.33, Chunk G) with `hρ := hD.hμ`, `hV := hD.hV`,
`hν := hD.hν`, `hM := hD.hM`, `hRg`.  The needed statement of S.A.33 is exactly the one frozen (plan section 5). -/
theorem uniqueness_rd (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (Rg : PDE.Regime) (MB Λ ΛV G₀ νbar T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ)
    (D : WholeDyn d) (ν₀ : ℝ) (μ : ℝ → Euc d → ℝ) (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ)
    (hR : RdRegimeHolds Rg d s D.M D.invβ ν₀) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) (φ : Euc d → ℝ)
    (F₁ F₂ : ℝ → Euc d → ℝ) (h₁ : IsUlocSolutionRd χ m (D.coeff μ) t φ F₁)
    (h₂ : IsUlocSolutionRd χ m (D.coeff μ) t φ F₂) :
    ∀ τ ∈ Icc (0 : ℝ) t, F₁ τ =ᵐ[volume] F₂ τ := by
  sorry

/-! ### Group C: the coefficients of `AdjointRdData` -/

/-- **C1a** (size M/L).  Drift bounds at fixed time: under `AdjointRdData` the drift `b^r = M∇g*μ^r - ∇V`
(`meanFieldDriftW`, cancellation convention `convGradConvW`) is `C^{m+1}` with `‖∇^jb^r‖_∞ ≤ Cb` for `1 ≤ j ≤ m+1`
(indeed up to `m+2`) and `|b^r(x)| ≤ Cb(1+|x|)`, with `Cb = Cb(d,s,m,MB,Λ,ΛV,G₀,νbar)` independent of `r`.
Route: `HRS.MP.RdGen.rg_conv_comp` and `rg_drift`, `rg_gradV` (HRS/MP/RdGenerator.lean, RdGenCalc.lean; `RgW w k c u`)
give the convolution `∇g*μ` bounded with all derivatives bounded by `Λ`-weights (`∂^α(∇g*μ) = ∇g*∂^αμ`, the kernel is
integrable at infinity against `⟨y⟩^{-(d+3)}`); `∇V` has linear growth `G₀ + ΛV|x|` and bounded derivatives of order
`1..m+2` (`VHypRd (m+3)`); for `d-1 ≤ s` the derivative bound of order `0` of `∇g*μ` uses the `fracForceRd` bound
in `IsRegularMFRd`.  (The first derivative of `∇g*μ`, `s ≥ d-1`, is `∇g*∇μ`: `‖·‖_∞ ≤ C Λ`.) -/
theorem drift_bounds_of_data (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (MB Λ ΛV G₀ νbar T : ℝ) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (D : WholeDyn d) (μ : ℝ → Euc d → ℝ),
      AdjointRdData s m MB Λ ΛV G₀ νbar D T μ → ∀ r ∈ Icc (0 : ℝ) T,
        ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) ((D.coeff μ).drift r) ∧
        (∀ j : ℕ, 1 ≤ j → j ≤ m + 1 → ∀ x, ‖iteratedFDeriv ℝ j ((D.coeff μ).drift r) x‖ ≤ Cb) ∧
        ∀ x, ‖(D.coeff μ).drift r x‖ ≤ Cb * (1 + ‖x‖) := by
  sorry

/-- **C1b** (size M).  Joint continuity of the drift in `(r,x)` on `[0,T] × ℝ^d`, which `AdjointRdData` does not state
(`CoeffHypRd.cont` is only weak continuity of `r ↦ μ^r`).  Route: for fixed `x` the map `r ↦ ∇g*μ^r(x)` is continuous
because, with the cancellation convention, `∇g*μ^r(x) = ∫ (μ^r(y) - μ^r(x)1_{|x-y|≤1/4}) ∇g(x-y)dy` is the pairing of
`μ^r` against the bounded continuous test function `y ↦ ∇g(x-y)1_{|x-y|>δ}` plus a part that is small uniformly in `r`
(Lipschitz bound of `μ^r` in `x`, `Λ`); this gives continuity in `r`; joint continuity with the uniform Lipschitz bound
of `b^r` in `x` (C1a, `j = 1`); `∇V` is continuous and independent of `r`. -/
theorem drift_jointly_continuous (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (MB Λ ΛV G₀ νbar T : ℝ) (D : WholeDyn d) (μ : ℝ → Euc d → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) :
    ContinuousOn (fun p : ℝ × Euc d => (D.coeff μ).drift p.1 p.2) (Icc (0 : ℝ) T ×ˢ univ) := by
  sorry

/-- **C1c** (size S).  The reversed, clamped drift is an advecting drift: for `t ∈ (0,T]`,
`b(τ) = drift(max(t-τ, 0))` satisfies `IsAdvectingDrift m Cb T b` (the clamp makes the time-`τ` coefficient defined for
`τ ∈ (t,T]`, where the equation is not posed; `t - τ` leaves `[0,T]` otherwise), and `μ_rev(τ) = μ(max(t-τ,0))` is
regular: `IsRegularDensityW (m+3) Λ (μ_rev τ)` for `τ ∈ [0,T]`.  From C1a, C1b by composition with the continuous map
`(τ,x) ↦ (max (t-τ) 0, x)` which maps `[0,T] × ℝ^d` into `[0,T] × ℝ^d`; the density statement is `hD.hμ.regular`
unfolded (`MemCb r` gives `ContDiff`; `weightedSupE < ⊤` and the sum bound give the `ℝ≥0∞` inequality). -/
theorem reversed_data (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (MB Λ ΛV G₀ νbar T : ℝ) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (D : WholeDyn d) (μ : ℝ → Euc d → ℝ),
      AdjointRdData s m MB Λ ΛV G₀ νbar D T μ → ∀ t ∈ Ioc (0 : ℝ) T,
        IsAdvectingDrift m Cb T (fun τ => (D.coeff μ).drift (max (t - τ) 0)) ∧
        ∀ τ ∈ Icc (0 : ℝ) T, IsRegularDensityW (m + 3) Λ (μ (max (t - τ) 0)) := by
  sorry

/-- **C2** (size S).  Level monotonicity of the data: `AdjointRdData` at level `m` implies it at every level `m' ≤ m` with
the same constants.  Used for `adjoint_rd_classical` (level `m ≥ m_*` data gives the level-`m_*` and level-`1` data, so
that the level-`m_*` existence theorem and the level-`1` uniqueness apply) and for `adjoint_rd_stability` (level `m+2`
data gives level `m`).  `cbNorm` and `weightedSupE` are monotone in the order (sums/maxima over `j ≤ r`; the
definitions are in `HRS/Whole/Adjoint.lean`, monotonicity lemmas not verified by grep). -/
theorem data_mono (s : ℝ) (m m' : ℕ) (h : m' ≤ m) (MB Λ ΛV G₀ νbar T : ℝ) (D : WholeDyn d)
    (μ : ℝ → Euc d → ℝ) (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) :
    AdjointRdData s m' MB Λ ΛV G₀ νbar D T μ := by
  sorry

/-- **C3** (size S).  `Regime.lambdaM` is monotone in the constant (`R3`: `C ↦ C(1 + ν₀^{-θ/(2-θ)})`, `ν₀ > 0`) and
`0 ≤ lambdaM`, needed to merge the constant `C` appearing both as prefactor and inside `Λ_m` in the six frozen
statements (e.g. `adjoint_rd_classical` for `m ≥ m_*` uses the level-`m_*` constant). -/
theorem lambdaM_mono (Rg : PDE.Regime) (C C' ν₀ θ : ℝ) (hC : C ≤ C') (hν : 0 < ν₀) (hC0 : 0 ≤ C) :
    Rg.lambdaM C ν₀ θ ≤ Rg.lambdaM C' ν₀ θ := by
  sorry

/-! ### Group F: flows, cells, and the comparison of moving and static cells -/

/-- **F0** (size S).  Existence of the flow of `-b` in the sense of `HRS.Whole.IsNegDriftFlow` (with `bij`), for an
advecting drift.  Route: adaptor `HRS.MH.Screened.f1a_drift` (`IsAdvectingDrift → HRS.Whole.AppendixALemmas.IsDriftBounds`,
ScreenedF1.lean:22), `HRS.MS.FlowA.flow_exists` (FlowA.lean:38) for `Ψ`, then bijectivity from
`HRS.MS.FlowA.flow_invertible` (FlowA.lean:78); the converse adaptor is `f1a_flow` (ScreenedF1.lean:33). -/
theorem flow_exists_adv (hd : 1 ≤ d) (m : ℕ) (Cb T : ℝ) (hT : 0 ≤ T) (b : ℝ → Euc d → Euc d)
    (hb : IsAdvectingDrift m Cb T b) : ∃ Ψ : ℝ → Euc d → Euc d, IsNegDriftFlow T b Ψ := by
  sorry

/-- **F1a** (size M).  `screened_far` with centres shifted by a bounded real vector `e` (the cells of the cover by
cutoffs of radius `1` need centres on a lattice finer than `ℤ^d` for `d ≥ 5`, `MH-REPAIRS-1`; the frozen
`screened_far` has the centres `latticePt z`).  Statement: same as `HRS.Whole.screened_far` with the centres
`latticePt z + e`, the cells `Ψ_τ(latticePt z' + e + [0,1]^d)`, `‖e‖ ≤ R`, and the constant depending also on `R`.
Route: translate the problem by `e`: `b^e = b(·+e)` (same `IsAdvectingDrift` with `Cb' = Cb(1+R)`), `Ψ^e_τ = Ψ_τ(·+e) - e`
(a flow of `-b^e`, `bij`), `μ^e = μ(·+e)` (`IsRegularDensityW (m+3) (Λ(1+R)^{d+3})`, since
`⟨y⟩ ≥ ⟨y+e⟩/(1+R)`), `ψ^e = ψ(·+e)`, `advCutoff χ Ψ^e τ (latticePt z) x = advCutoff χ Ψ τ (latticePt z + e) (x+e)`,
the kernel `∂_ig` is translation invariant, `⟨z⟩` and `⟨z+e⟩` are comparable up to `(1+R)` so the Schur conditions
transfer; apply `HRS.MH.Screened.screened_far_proof` (ScreenedFarAsm.lean:31). -/
theorem screened_far_shift (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (Λ Cb T R : ℝ) :
    ∀ χ χh : Euc d → ℝ, IsCutoffPair χ χh →
    ∃ C : ℝ, ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      IsAdvectingDrift m Cb T b → IsNegDriftFlow T b Ψ →
      ∀ μ : Euc d → ℝ, IsRegularDensityW (m + 3) Λ μ →
      ∀ τ ∈ Icc (0 : ℝ) T, ∀ e : Euc d, ‖e‖ ≤ R →
      ∃ Kc : (Fin d → ℤ) → (Fin d → ℤ) → ℝ≥0,
        (⨆ z, ∑' z', (Kc z z' : ℝ≥0∞) ≤ ENNReal.ofReal C) ∧
        (∀ z', ∑' z, ENNReal.ofReal (cellWeight d z) * (Kc z z' : ℝ≥0∞) ≤
          ENNReal.ofReal C * ENNReal.ofReal (cellWeight d z')) ∧
        ∀ (j : ℕ), j ≤ m + 1 → ∀ (idx : Fin j → Fin d) (i : Fin d) (ψ : Euc d → ℝ), Measurable ψ →
          ∀ z : Fin d → ℤ,
            (eLpNorm (fun x => advCutoff χ Ψ τ (latticePt z + e) x *
                gradGConvPlain d s (fun y => (1 - advCutoff χh Ψ τ (latticePt z + e) y) *
                  (partialDeriv idx μ y * ψ y)) x i) 2 volume) ^ 2 ≤
              ENNReal.ofReal (C * Λ ^ 2) * ∑' z', (Kc z z' : ℝ≥0∞) *
                (eLpNorm ((flowCellAt Ψ τ (latticePt z' + e)).indicator ψ) 2 volume) ^ 2 ∧
            (ENNReal.ofReal (C * Λ ^ 2) * ∑' z', (Kc z z' : ℝ≥0∞) *
                (eLpNorm ((flowCellAt Ψ τ (latticePt z' + e)).indicator ψ) 2 volume) ^ 2 < ⊤ →
              ∀ x ∈ tsupport (advCutoff χ Ψ τ (latticePt z + e)),
                Integrable (fun y => rieszKernelGrad d s (x - y) i *
                  ((1 - advCutoff χh Ψ τ (latticePt z + e) y) * (partialDeriv idx μ y * ψ y)))) := by
  sorry

/-- **F1b** (size M).  `screened_comm_cell` with centres shifted by `e`, `‖e‖ ≤ R`, `s < d-1` (same translation
argument as F1a; apply `HRS.MH.Screened.screened_comm_cell_proof`, ScreenedAsmCommCell.lean). -/
theorem screened_comm_cell_shift (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) (m : ℕ)
    (Λ Cb T R : ℝ) :
    ∀ χ χh : Euc d → ℝ, IsCutoffPair χ χh →
    ∃ C : ℝ, ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      IsAdvectingDrift m Cb T b → IsNegDriftFlow T b Ψ →
      ∀ μ : Euc d → ℝ, IsRegularDensityW (m + 3) Λ μ →
      ∀ τ ∈ Icc (0 : ℝ) T, ∀ e : Euc d, ‖e‖ ≤ R →
      ∃ Kc : (Fin d → ℤ) → (Fin d → ℤ) → ℝ≥0,
        (⨆ z, ∑' z', (Kc z z' : ℝ≥0∞) ≤ ENNReal.ofReal (C * Real.exp (C * d * τ))) ∧
        (∀ z', ∑' z, ENNReal.ofReal (cellWeight d z) * (Kc z z' : ℝ≥0∞) ≤
          ENNReal.ofReal (C * Real.exp (C * d * τ)) * ENNReal.ofReal (cellWeight d z')) ∧
        ∀ (j : ℕ), j ≤ m + 1 → ∀ (idx : Fin j → Fin d) (i : Fin d) (ψ : Euc d → ℝ), Measurable ψ →
          ∀ z : Fin d → ℤ,
            ENNReal.ofReal (C * Real.exp (C * d * τ) * Λ ^ 2) * ∑' z', (Kc z z' : ℝ≥0∞) *
                (eLpNorm ((flowCellAt Ψ τ (latticePt z' + e)).indicator ψ) 2 volume) ^ 2 < ⊤ →
            (eLpNorm (fun x => advCutoff χ Ψ τ (latticePt z + e) x *
                ∫ y, (advCutoff χh Ψ τ (latticePt z + e) y - advCutoff χ Ψ τ (latticePt z + e) y) *
                  (partialDeriv idx μ y * ψ y) * rieszKernelGrad d s (x - y) i) 2 volume) ^ 2 ≤
              ENNReal.ofReal (C * Real.exp (C * d * τ) * Λ ^ 2) * ∑' z', (Kc z z' : ℝ≥0∞) *
                (eLpNorm ((flowCellAt Ψ τ (latticePt z' + e)).indicator ψ) 2 volume) ^ 2 ∧
            (eLpNorm (fun x => advCutoff χ Ψ τ (latticePt z + e) x *
                ∫ y, (advCutoff χ Ψ τ (latticePt z + e) x - advCutoff χ Ψ τ (latticePt z + e) y) *
                  (partialDeriv idx μ y * ψ y) * rieszKernelGrad d s (x - y) i) 2 volume) ^ 2 ≤
              ENNReal.ofReal (C * Real.exp (C * d * τ) * Λ ^ 2) * ∑' z', (Kc z z' : ℝ≥0∞) *
                (eLpNorm ((flowCellAt Ψ τ (latticePt z' + e)).indicator ψ) 2 volume) ^ 2 := by
  sorry

/-- **F2** (size S/M).  Fine-centre cover of the cells: for a bijection `Ψ_τ`, every cell `Ψ_τ(z'+[0,1]^d)` is
covered by the supports of the `N_d` advected unit cutoffs with centres at the points of `⌈√d⌉⁻¹ℤ^d` in the cube
`z'+[0,1]^d` (`χ_c^τ = 1` on `Ψ_τ(closedBall c 1)`, and every point of the cube is within `√d/(2⌈√d⌉) ≤ 1/2` of such a
point); so, for every measurable `w`, (i) `∫_{Q_{z'}} w² ≤ N sup_{z∈ℤ^d}∫(χ_{cellPt z}^τ w)²` and (ii) the weighted form
`∑_{z'} ω_{z'}∫_{Q_{z'}}w² ≤ C ∑_{z} ⟨cellPt z⟩^{-(d+3)} ∫(χ_{cellPt z}^τ w)²` (each fine point lies in at most `2^d`
cubes, and `⟨z'⟩ ≍ ⟨cellPt z⟩` for the fine points of the cube `z'`, with constants depending only on `d`).
`N, C` depend only on `d`.  Related existing lemmas (verified): `HRS.MH.Screened.flowCell_geometry_proof`
(ScreenedF3.lean:41), `cellPt` (HRS/Whole/Adjoint.lean). -/
theorem cell_cover (hd : 1 ≤ d) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ N C : ℝ, 0 ≤ N ∧ 0 ≤ C ∧ ∀ (Ψ : ℝ → Euc d → Euc d) (τ : ℝ), Function.Bijective (Ψ τ) →
      ∀ w : Euc d → ℝ, Measurable w →
        (∀ z' : Fin d → ℤ, ∫⁻ x in flowCell Ψ τ z', ENNReal.ofReal (w x ^ 2) ≤
          ENNReal.ofReal N * ⨆ z : Fin d → ℤ, ∫⁻ x, ENNReal.ofReal ((advCutoff χ Ψ τ (cellPt d z) x * w x) ^ 2)) ∧
        ∑' z' : Fin d → ℤ, ENNReal.ofReal (cellWeight d z') * ∫⁻ x in flowCell Ψ τ z', ENNReal.ofReal (w x ^ 2) ≤
          ENNReal.ofReal C * ∑' z : Fin d → ℤ, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
            ∫⁻ x, ENNReal.ofReal ((advCutoff χ Ψ τ (cellPt d z) x * w x) ^ 2) := by
  sorry

/-- **F3** (size L).  Moving cells versus the uniformly local norm: for functions with bounded jets (periodic
approximants), `sup_{z∈ℝ^d} (∑_{|α|≤m}‖χ_z^τ∂^αF‖²)^{1/2}` is equivalent to `‖F‖_{H^m_uloc}`, with constants depending
only on `d, m, Cb, T, χ` (`e^{C(m+d)T}`).  Route: `HRS.Whole.AppendixALemmas.uloc_bilip` (S.A.32, proved as
`HRS.MS.BilipV.uloc_bilip_proof`, BilipV.lean:109) clause (v) is exactly `‖F‖_uloc ≍ sup_z ‖χ_z^τ F‖_{H^m}`
(`ENNReal`, real centres), `sobolev_jet_equiv` (N2) for `χ_z^τF ∈ C_c^∞`, and the Leibniz comparison
`∑_α‖χ_z∂^αF‖² ≤ ∑_α‖∂^α(χ̂_zF)‖² + `(lower-order terms vanish on `supp χ_z` because `χ̂_z = 1` there) and
`∑_α‖∂^α(χ_zF)‖² ≤ C∑_{e∈E}𝓕_{z+e}` (derivatives of `χ_z^τ` are bounded by `cbNorm (m+1)`, clause (ii), supported in
`Ψ^{-1}`-balls covered by finitely many unit balls).  The auxiliary `χ̂` with `IsCutoffRad 6 8` is fixed by the plan. -/
theorem uloc_moving_equiv (hd : 1 ≤ d) (m : ℕ) (Cb T : ℝ) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      IsAdvectingDrift m Cb T b → IsNegDriftFlow T b Ψ → ∀ τ ∈ Icc (0 : ℝ) T, ∀ u : Euc d → ℝ, BddJets m u →
        ENNReal.ofReal c₁ * ulocNormE m χ u ≤ (cellSup m χ Ψ τ u) ^ (1 / 2 : ℝ) ∧
        (cellSup m χ Ψ τ u) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal c₂ * ulocNormE m χ u := by
  sorry

/-- **F4** (size L).  The same for the weighted norm: for functions with bounded jets,
`(∑_z ⟨cellPt z⟩^{-(d+3)} 𝓕_{cellPt z}(τ))^{1/2} ≍ ‖F‖_{H^m(ϖ)}` (`varpiNormE`, static cutoffs at the fine centres), with
constants depending only on `d, m, Cb, T, χ`.  Route: both sides are weighted `ℓ²` sums over the fine lattice of
cell quantities that are comparable cell by cell up to a bounded number of neighbouring cells: for the static cell
`‖χ(·-cellPt z)F‖_{H^m}` use the covering of `Ψ_τ^{-1}(B(cellPt z,2))` by `N(e^{CT})` unit balls with centres in
`Ψ_τ^{-1}`-coordinates, the comparability `⟨cellPt z⟩ ≍ ⟨cellPt z'⟩` for neighbours, and
`‖Ψ_τ(0)‖ ≤ e^{Cb τ} - 1` (`HRS.MH.Screened.flow_origin_proof`, ScreenedF2.lean:18) to move the weight origin; plus N2
and the Leibniz comparison of F3. -/
theorem varpi_moving_equiv (hd : 1 ≤ d) (m : ℕ) (Cb T : ℝ) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      IsAdvectingDrift m Cb T b → IsNegDriftFlow T b Ψ → ∀ τ ∈ Icc (0 : ℝ) T, ∀ u : Euc d → ℝ, BddJets m u →
        ENNReal.ofReal c₁ * varpiNormE m χ u ≤ (cellWeighted m χ Ψ τ u) ^ (1 / 2 : ℝ) ∧
        (cellWeighted m χ Ψ τ u) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal c₂ * varpiNormE m χ u := by
  sorry

/-! ### Group G: abstract Gronwall lemmas for families of cell energies -/

/-- **G1** (size S/M).  Gronwall for a supremum of a family of differentiable functions: each `f_i ≥ 0` is
continuous on `[0,t]`, differentiable within `[0,t]` with derivative `g_i(τ) ≤ A S(τ) + h(τ)`, where
`S(τ) = sup_i f_i(τ)` (bounded) and `h ≥ 0` is integrable.  Then `S(τ) ≤ e^{Aτ}(S(0) + ∫_0^τ h)`.  Route:
each `f_i(τ) ≤ f_i(0) + ∫_0^τ (A S + h)` (mean value inequality / `image_le_of_liminf_slope_right_lt_deriv_boundary`,
or monotonicity of `f_i - ∫(AS+h)`), take the supremum in `i`; `S` is measurable (lower semicontinuous, supremum of
continuous functions) and bounded; then the integral Gronwall inequality (`norm_le_gronwallBound_of_norm_deriv_right_le`
or `le_gronwallBound_of_liminf_deriv_right_le` in Mathlib) for `U(τ) = S(0) + ∫_0^τ(AS+h)`. -/
theorem gronwall_sup {ι : Type*} (t A : ℝ) (hA : 0 ≤ A) (f g : ι → ℝ → ℝ) (h : ℝ → ℝ)
    (hnn : ∀ i, ∀ τ ∈ Icc (0 : ℝ) t, 0 ≤ f i τ) (hbdd : ∃ B : ℝ, ∀ i, ∀ τ ∈ Icc (0 : ℝ) t, f i τ ≤ B)
    (hcont : ∀ i, ContinuousOn (f i) (Icc (0 : ℝ) t))
    (hderiv : ∀ i, ∀ τ ∈ Icc (0 : ℝ) t, HasDerivWithinAt (f i) (g i τ) (Icc (0 : ℝ) t) τ)
    (hh0 : ∀ τ ∈ Icc (0 : ℝ) t, 0 ≤ h τ) (hhint : IntegrableOn h (Icc (0 : ℝ) t))
    (hineq : ∀ i, ∀ τ ∈ Icc (0 : ℝ) t, g i τ ≤ A * (⨆ j, f j τ) + h τ) :
    ∀ τ ∈ Icc (0 : ℝ) t, (⨆ i, f i τ) ≤ Real.exp (A * τ) * ((⨆ i, f i 0) + ∫ σ in Icc (0 : ℝ) τ, h σ) := by
  sorry

/-- **G2** (size M).  Weighted Gronwall with a Schur kernel and absorbed dissipation: index set `ℤ^d`, weights `w_z ≥ 0`
(`w_z ≤ c_w w_{z+k}` for `k ∈ E`), `f_z ≥ 0` continuous and differentiable on `[0,t]` with
`g_z(τ) ≤ -νD_z(τ) + κ∑_{k∈E}D_{z+k}(τ) + A(f_z(τ) + ∑_{z'}K_{zz'}f_{z'}(τ)) + h_z(τ)`, `D_z ≥ 0`, `κ|E|c_w ≤ ν`,
`∑_zw_zK_{zz'} ≤ Qw_{z'}`, all weighted sums finite and bounded on `[0,t]`.  Then
`W(τ) ≤ e^{A(1+Q)τ}(W(0) + ∫_0^τ ∑_zw_zh_z)`, `W = ∑_zw_zf_z`.  Route: integrate in time for each `z`, multiply by `w_z`
and sum (`ENNReal` Tonelli, `lintegral_tsum`), the dissipation terms cancel by `κ|E|c_w ≤ ν` and the comparability of the
weights (re-index `z ↦ z+k`), use the column bound, then the integral Gronwall inequality for `W`. -/
theorem gronwall_weighted (t A Q : ℝ) (hA : 0 ≤ A) (hQ : 0 ≤ Q) (w : (Fin d → ℤ) → ℝ) (hw : ∀ z, 0 ≤ w z)
    (E : Finset (Fin d → ℤ)) (cw : ℝ) (hcw : ∀ z, ∀ k ∈ E, w z ≤ cw * w (z + k)) (ν κ : ℝ) (hκ : 0 ≤ κ)
    (hκν : κ * E.card * cw ≤ ν)
    (K : (Fin d → ℤ) → (Fin d → ℤ) → ℝ) (hK : ∀ z z', 0 ≤ K z z')
    (hcol : ∀ z', ∑' z, ENNReal.ofReal (w z) * ENNReal.ofReal (K z z') ≤ ENNReal.ofReal Q * ENNReal.ofReal (w z'))
    (f g h D : (Fin d → ℤ) → ℝ → ℝ) (hnn : ∀ z, ∀ τ ∈ Icc (0 : ℝ) t, 0 ≤ f z τ)
    (hh : ∀ z, ∀ τ ∈ Icc (0 : ℝ) t, 0 ≤ h z τ) (hD : ∀ z, ∀ τ ∈ Icc (0 : ℝ) t, 0 ≤ D z τ)
    (hcont : ∀ z, ContinuousOn (f z) (Icc (0 : ℝ) t))
    (hderiv : ∀ z, ∀ τ ∈ Icc (0 : ℝ) t, HasDerivWithinAt (f z) (g z τ) (Icc (0 : ℝ) t) τ)
    (hsum : ∀ z, ∀ τ ∈ Icc (0 : ℝ) t, Summable fun z' => K z z' * f z' τ)
    (hineq : ∀ z, ∀ τ ∈ Icc (0 : ℝ) t,
      g z τ ≤ -ν * D z τ + κ * ∑ k ∈ E, D (z + k) τ + A * (f z τ + ∑' z', K z z' * f z' τ) + h z τ)
    (hfin : ∃ B : ℝ, ∀ τ ∈ Icc (0 : ℝ) t, ∑' z, ENNReal.ofReal (w z) * ENNReal.ofReal (f z τ) ≤ ENNReal.ofReal B) :
    ∀ τ ∈ Icc (0 : ℝ) t, ∑' z, ENNReal.ofReal (w z) * ENNReal.ofReal (f z τ) ≤
      ENNReal.ofReal (Real.exp (A * (1 + Q) * τ)) *
        (∑' z, ENNReal.ofReal (w z) * ENNReal.ofReal (f z 0) +
          ∫⁻ σ in Icc (0 : ℝ) τ, ∑' z, ENNReal.ofReal (w z) * ENNReal.ofReal (h z σ)) := by
  sorry

/-- **G3** (size M).  Gronwall for a supremum with absorbed dissipation (no weights; the price is the factor `2`):
index type `ι` with neighbour sets `nb i` of cardinality `≤ N`; `f_i ≥ 0` continuous, differentiable on `[0,t]` with
`g_i(τ) ≤ -νD_i(τ) + κ∑_{j ∈ nb i}D_j(τ) + A S(τ) + h(τ)`, `S = sup_if_i` bounded, `D_i ≥ 0`, `κN ≤ ν/2`.  Then
`S(τ) ≤ 2e^{2Aτ}(S(0) + ∫_0^τh)`.  Route: integrate: `f_i(τ) + ν∫_0^τD_i ≤ f_i(0) + κ∑_{j∈nb i}∫_0^τD_j + ∫_0^τ(AS+h)`; put
`X = sup_i∫_0^τD_i` (the sum over neighbours is at most `NX` because the integral is taken BEFORE the supremum); take sups:
`(ν/2)X ≤ S(0)+∫(AS+h)` and then `S(τ) ≤ 2(S(0)+∫_0^τ(AS+h))`; Gronwall as in G1. -/
theorem gronwall_sup_dissip {ι : Type*} (t A ν κ : ℝ) (N : ℕ) (hA : 0 ≤ A) (hκ : 0 ≤ κ) (hν : 0 ≤ ν)
    (hκN : κ * N ≤ ν / 2) (nb : ι → Finset ι) (hnb : ∀ i, (nb i).card ≤ N) (f g D : ι → ℝ → ℝ) (h : ℝ → ℝ)
    (hnn : ∀ i, ∀ τ ∈ Icc (0 : ℝ) t, 0 ≤ f i τ) (hDnn : ∀ i, ∀ τ ∈ Icc (0 : ℝ) t, 0 ≤ D i τ)
    (hbdd : ∃ B : ℝ, ∀ i, ∀ τ ∈ Icc (0 : ℝ) t, f i τ ≤ B)
    (hDint : ∀ i, IntegrableOn (D i) (Icc (0 : ℝ) t))
    (hDbdd : ∃ B : ℝ, ∀ i, ∫ σ in Icc (0 : ℝ) t, D i σ ≤ B)
    (hcont : ∀ i, ContinuousOn (f i) (Icc (0 : ℝ) t))
    (hderiv : ∀ i, ∀ τ ∈ Icc (0 : ℝ) t, HasDerivWithinAt (f i) (g i τ) (Icc (0 : ℝ) t) τ)
    (hh0 : ∀ τ ∈ Icc (0 : ℝ) t, 0 ≤ h τ) (hhint : IntegrableOn h (Icc (0 : ℝ) t))
    (hineq : ∀ i, ∀ τ ∈ Icc (0 : ℝ) t, g i τ ≤ -ν * D i τ + κ * ∑ j ∈ nb i, D j τ + A * (⨆ j, f j τ) + h τ) :
    ∀ τ ∈ Icc (0 : ℝ) t, (⨆ i, f i τ) ≤ 2 * Real.exp (2 * A * τ) * ((⨆ i, f i 0) + ∫ σ in Icc (0 : ℝ) τ, h σ) := by
  sorry

/-! ### Group T: periodic (expanding-tori) approximants -/

/-- **T1a** (size L).  Joint regularity of the unit-torus solutions in all jets up to a prescribed order `k`.  The
repository gives, for `m ≥ m_*` (`adjoint_torus_joint_continuity`, HRS/PDE/WellPosed.lean:706), joint continuity of `F, ∇F,
∇²F, ∂_τF` only (jets `≤ 2`).  For the energy identity on `L`-periodic approximants we need `k = m + 3` space jets and the
time derivative of every such jet.  Statement: for data of level `N = N(d,k)`, the lift to `ℝ^d` of the Fourier series
`toFun (propagatorCoeff D μ N t φc τ)` has jointly continuous jets of order `≤ k` on `[0,t] × ℝ^d`, and the jet
`j` is differentiable in `τ` with derivative the same jet of the generator `forwardGen D (μ (t-τ)) (…)`.  Route: the proof of
`adjoint_torus_time_regularity` (WellPosed.lean:291: `τ ↦ forwardGen … F(τ)` is norm continuous in `H^{N-2}` and is the
`H^{N-2}`-derivative) plus Sobolev embedding on the torus (`ClassicalPart.continuous_iteratedFDeriv_toFun`,
WellPosed.lean, used in `adjoint_torus_joint_continuity`) at the order `N-2-⌈d/2⌉ ≥ k`. -/
theorem torus_jet_regularity (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (k : ℕ) (R : PDE.Regime)
    (MB Λ VB : ℝ) :
    ∃ N : ℕ, ∀ (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ),
      PDE.AdjointData s N R MB Λ VB D ν₀ T μ → ∀ t ∈ Ioc (0 : ℝ) T, ∀ φc : PDE.Coeff d,
        PDE.MemHs (N : ℝ) φc → PDE.IsRealCoeff φc →
        (∀ j ≤ k, ContinuousOn (fun p : ℝ × Euc d =>
          iteratedFDeriv ℝ j (Torus.lift (PDE.toFun (PDE.propagatorCoeff D μ (N : ℝ) t φc p.1))) p.2)
            (Icc (0 : ℝ) t ×ˢ univ)) ∧
        (∀ j ≤ k, ∀ y : Euc d, ∀ τ ∈ Icc (0 : ℝ) t,
          HasDerivWithinAt
            (fun τ' => iteratedFDeriv ℝ j (Torus.lift (PDE.toFun (PDE.propagatorCoeff D μ (N : ℝ) t φc τ'))) y)
            (iteratedFDeriv ℝ j (Torus.lift (PDE.toFun
              (PDE.forwardGen D (μ (t - τ)) (PDE.propagatorCoeff D μ (N : ℝ) t φc τ)))) y)
            (Icc (0 : ℝ) t) τ) := by
  sorry

/-- **T1b** (size L, dictionary).  Existence of a smooth `L`-periodic classical solution of the approximating problem
`∂_τF = νΔF + b·∇F - 𝒢_L[F]`, `F(0) = φ`, for smooth periodic coefficients and datum (no uniform bound: the uniform
bound is the energy engine, group E).  `μ` is the time-reversed density path (`μ(τ)` is the coefficient at reversed
time `t-τ`).  Any order `N`: `IsPerSol N`.  Route: rescale to the unit torus `x = Ly`: `u(τ,y) = F(τ,Ly)` solves the
unit-torus problem with `ν ↦ ν/L²`, `M ↦ L^{-s-2}M`, `b ↦ b(L·)/L`, `V ↦ V(L·)/L²`, and the torus probability density
`μ ↦ L^dμ(L·)` (`γ_L(Ly) = L^{-s}g₁(y)` up to an additive constant, `HRS.MS.Ker1.ker1_gam_iter`, Ker1Aux5.lean:193,
`ker1_gam_scale_pow` :274; additive constants are killed by the derivative in `𝒢`); the regime `RdRegimeHolds` is invariant
under positive rescaling of `M, ν` and `ν₀ ↦ ν₀/L²`; apply `HRS.PDE.adjoint_torus`/`propagatorCoeff` at a level `N'`
large enough for T1a (`AdjointData` at level `N'` holds for smooth data with some finite constants `Λ, VB`); T1a gives
jets and time derivatives; the equation holds pointwise because `forwardGen` is the Fourier-coefficient form of
`νΔ + b·∇ - 𝒢` (`HRS.PDE.nonlocalCoeff`, ForwardEq.lean): bridge `toFun (nonlocalCoeff …) = perNonlocal …` (Fourier series
of the periodic convolution `perConv`; `periodic γ` has Fourier coefficients `IsPeriodicRieszKernel.coeff`). -/
theorem per_smooth_solution_exists (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (Rg : PDE.Regime) (N : ℕ)
    (T : ℝ) (L : ℝ) (γ : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ν ν₀ : ℝ) (μ : ℝ → Euc d → ℝ) (V : Euc d → ℝ)
    (b : ℝ → Euc d → Euc d) (hP : PerSmooth s T L γ M ν μ V b) (hR : RdRegimeHolds Rg d s M ν ν₀)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) (φ : Euc d → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hφp : ∀ (x : Euc d) (k : Fin d → ℤ), φ (x + L • latticePt k) = φ x) :
    ∃ F : ℝ → Euc d → ℝ, IsPerSol N L γ M ν μ b (fun _ _ => 0) t F ∧ F 0 = φ := by
  sorry

/-- **T2** (size L).  The periodic coefficients of Step 3 (S L10436-10441), with the mollification needed to make the
approximants smooth and the periodic decay: given `AdjointRdData` at level `m`, the periodized, cut-off, normalised and
`ε`-mollified densities `μ_{L,ε}` and potentials `V_{L,ε}` (for the reversed clamped path, `μ_{L,ε}(τ) ≈ μ(max(t-τ,0))`)
satisfy `PerData` with constants independent of `(L,ε)`, and converge locally uniformly with all derivatives up to order
`m+1` (the drifts) as `L → ∞`, `ε → 0`.  Route: `HRS.MS.ToriCoefB.expanding_tori_coefficients_proof` (ToriCoefB.lean:229) for
the unmollified periodized data (applied to `V - V(0)`: only `∇V` enters the dynamics, and the lemma needs `|V(0)| ≤ V₀`;
`V₀ = 0` after the shift, `VHypRd` is unchanged), the periodic decay from its central-ball decay and the support of `μ_L`
(supp `μ_L ⊂ ∪_kB(Lk, L/3)`, so outside the central ball the decay is relative to the nearest lattice point), mollification
commutes with `perL`, convolution with `γ_L` and `∇`, so sup norms of derivatives are preserved by `η_ε *`;
`HRS.MS.ToriConv.expanding_tori_drift_convergence_proof` (ToriConv.lean:56) for the convergence of `b_L`, and
`‖η_ε*f - f‖_{C^j(K)} → 0` for uniformly continuous `∇^jf`. -/
theorem per_coefficients (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (MB Λ ΛV G₀ νbar T : ℝ) (ζ : Euc d → ℝ) (hζ : HRS.Whole.AppendixALemmas.IsCutoffRad (1 / 4) (1 / 3) ζ) :
    ∃ Λ' ΛV' Cb L₀ : ℝ, ∀ (D : WholeDyn d) (μ : ℝ → Euc d → ℝ),
      AdjointRdData s m MB Λ ΛV G₀ νbar D T μ →
      ∀ γ : ℝ → Euc d → ℝ, (∀ L : ℝ, 1 ≤ L → HRS.Whole.AppendixALemmas.IsPeriodicRieszKernel d s L (γ L)) →
      ∀ t ∈ Ioc (0 : ℝ) T,
      ∃ (μL : ℝ → ℝ → ℝ → Euc d → ℝ) (VL : ℝ → ℝ → Euc d → ℝ),
        (∀ L : ℝ, max 1 L₀ ≤ L → ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) 1 →
          PerData s m MB Λ' ΛV' νbar Cb T L (γ L) D.M D.invβ (μL L ε) (VL L ε)
            (fun τ => HRS.Whole.AppendixALemmas.torusDriftL D.M L (γ L) (μL L ε τ) (VL L ε))) ∧
        (∀ (K : Set (Euc d)), IsCompact K → ∀ j ≤ m + 1, ∀ δ : ℝ, 0 < δ →
          ∃ L₁ ε₀ : ℝ, 0 < ε₀ ∧ ∀ L : ℝ, L₁ ≤ L → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ τ ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
            ‖iteratedFDeriv ℝ j (HRS.Whole.AppendixALemmas.torusDriftL D.M L (γ L) (μL L ε τ) (VL L ε)) x -
              iteratedFDeriv ℝ j ((D.coeff μ).drift (max (t - τ) 0)) x‖ ≤ δ ∧
            ‖iteratedFDeriv ℝ j (μL L ε τ) x - iteratedFDeriv ℝ j (μ (max (t - τ) 0)) x‖ ≤ δ) := by
  sorry

/-- **T2b** (size M).  Initial data of the approximants: for `φ` with `‖φ‖_{H^m_uloc} < ∞`, the periodized, cut-off,
mollified data `φ_{L,ε} = perL L (ζ_L · η_ε * φ)` are smooth, `L`-periodic, have bounded jets, satisfy
`‖φ_{L,ε}‖_{H^m_uloc} ≤ C‖φ‖_{H^m_uloc}` and `‖φ_{L,ε}‖_{H^m(ϖ)} ≤ C‖φ‖_{H^m(ϖ)}` (`C` independent of `(L,ε)`; for the
weighted bound the periodized weights are compared with `ϖ` on the central cell, plan section 3.4), converge weakly
(`∫φ_{L,ε}ψ → ∫φψ`, in fact `φ_{L,ε} = η_ε*φ` on `B(0,L/4)`), and, if `φ ∈ H^m(ℝ^d)`, the global jets satisfy
`jetSq m (⟨·/R⟩^{-(d+3)}) φ_{L,ε} ≤ ‖φ‖²_{H^m} + η` for `L ≥ L₁(R,η)`, `ε ≤ ε₀`.  Route:
`HRS.MS.QMul.sobolevNormE_mul_cb_le` (QMul.lean:43) for `ζ_L·`, mollification is a contraction in `H^m_uloc`
(`norm_calculus`, convexity), and `uloc_embedding_cutoffs` for the periodization. -/
theorem per_initial_data (hd : 1 ≤ d) (m : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (ζ : Euc d → ℝ)
    (hζ : HRS.Whole.AppendixALemmas.IsCutoffRad (1 / 4) (1 / 3) ζ) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ : Euc d → ℝ, ulocNormE m χ φ < ⊤ →
      ∃ φL : ℝ → ℝ → Euc d → ℝ,
        (∀ L ε, 1 ≤ L → 0 < ε → BddJets m (φL L ε) ∧
          ∀ (x : Euc d) (k : Fin d → ℤ), φL L ε (x + L • latticePt k) = φL L ε x) ∧
        (∀ L ε, 1 ≤ L → 0 < ε → ulocNormE m χ (φL L ε) ≤ ENNReal.ofReal C * ulocNormE m χ φ ∧
          varpiNormE m χ (φL L ε) ≤ ENNReal.ofReal C * varpiNormE m χ φ) ∧
        (∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ δ : ℝ, 0 < δ → ∃ L₁ ε₀ : ℝ, 0 < ε₀ ∧ ∀ L : ℝ, L₁ ≤ L → ∀ ε : ℝ, 0 < ε →
          ε ≤ ε₀ → |(∫ x, φL L ε x * ψ x) - ∫ x, φ x * ψ x| ≤ δ) ∧
        (HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) φ → ∀ R η : ℝ, 1 ≤ R → 0 < η → ∃ L₁ ε₀ : ℝ, 0 < ε₀ ∧
          ∀ L : ℝ, L₁ ≤ L → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
            jetSq m (fun x => jbracket (R⁻¹ • x) ^ (-((d : ℝ) + 3))) (φL L ε) ≤
              HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ) φ + η) := by
  sorry

/-- **T3** (size S/M).  The local form of the periodic kernel (the scaling identity of the proof of
`expanding_tori_kernel`): there are `δ > 0` and `q ∈ C^∞(ℝ^d)` (depending on `d, s`) such that for every `L ≥ 1` and every
periodic Riesz kernel `γ` on `𝕋_L^d` there is a constant `c` (`c = 0` unless `s = 0`, where `c = log L` up to an additive
constant independent of `L`) with `γ(u) = γ_E(u) + c + L^{-s} q(u/L)` for `0 < |u| < δL`.  Route (all verified): the
unit-torus local forms `periodicRiesz_local_singularity` (HRS/Kernel/Riesz.lean:3750, `d ≥ 2`),
`periodicLog_local_singularity` (:3757), `periodicRiesz_local_singularity_d1` and `periodicLog_local_singularity_d1`
(HRS/Kernel/D1.lean:1318, 1327), packaged as `HRS.MS.Ker1.ker1_local_form` (Ker1Aux5.lean:18), the scaling
`HRS.MS.Ker1.ker1_gam_iter` (:193), `ker1_gam_eventually` (:205), `ker1_gam_sub_E` (:240), and the identification
`HRS.MS.Ker1.ker1_eventually_eq_gam` (Ker1Aux6.lean:47) of a general `γ` with `ker1_gam d s L` off the lattice
(mean-zero normalisation and Fourier uniqueness, `ker1_coeff_diff_zero`, Ker1Aux3.lean:124).  The statement for `γ`
itself (not only for `ker1_gam`) is what is missing. -/
theorem kernel_local_decomposition (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ (δ : ℝ) (q : Euc d → ℝ), 0 < δ ∧ ContDiff ℝ ∞ q ∧ ∀ L : ℝ, 1 ≤ L →
      ∀ γ : Euc d → ℝ, HRS.Whole.AppendixALemmas.IsPeriodicRieszKernel d s L γ →
        ∃ c : ℝ, (s ≠ 0 → c = 0) ∧ ∀ u : Euc d, u ≠ 0 → ‖u‖ < δ * L →
          γ u = rieszKernel d s u + c + L ^ (-s) * q (L⁻¹ • u) := by
  sorry

/-- **T4** (size S/M).  Derivative bounds of `γ_L` on the whole period cell `|u|_∞ ≤ L/2` (the cube corners
`L/2 < |u| ≤ √d L/2` are not covered by clause (a) of `expanding_tori_kernel`, which is on `|u| ≤ L/2`): for
`0 ≤ n ≤ m+2`, `n + s > 0`, `‖∇^nγ_L(u)‖ ≤ C(|u|^{-s-n} + L^{-s-n}1_{s>0} + L^{-n}1_{s=0})` for `0 ≠ u` with `|u_i| ≤ L/2`.
Route: scaling `γ_L(u) = L^{-s}g₁(u/L) + c_L` (`ker1_gam_iter`, Ker1Aux5.lean:193) and the bound of `g₁` and its
derivatives on the unit cube `[-1/2,1/2]^d \ {0}` (`ker1_g1_bound`, :79; `periodicRiesz_grad_bound`, Riesz.lean:3765, is
stated on this cube); the cube corners are compact subsets of the open set where `g₁` is smooth, so the bound is
`C·L^{-s-n}`. -/
theorem kernel_cube_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L → ∀ γ : Euc d → ℝ,
      HRS.Whole.AppendixALemmas.IsPeriodicRieszKernel d s L γ →
      ∀ n : ℕ, n ≤ m + 2 → 0 < (n : ℝ) + s → ∀ u : Euc d, u ≠ 0 → (∀ i, |u i| ≤ L / 2) →
        ‖iteratedFDeriv ℝ n γ u‖ ≤ C * (‖u‖ ^ (-s - n) + (if 0 < s then L ^ (-s - n) else 0) +
          (if s = 0 then L ^ (-(n : ℝ)) else 0)) := by
  sorry

/-- **T5** (size S).  The derivative of the periodic convolution falls on the smooth periodic density:
for `L`-periodic `C¹` `h` and `L`-periodic locally integrable `γ`, `∂_i(γ ⊛_L h) = γ ⊛_L ∂_ih`
(translation invariance of the period integral: `perConv L γ h (x + te_i) = ∫ γ(y) h(x+te_i-y) dy`
over the period cell, differentiation under the integral sign for `h ∈ C¹` with bounded derivative).
Hence `perNonlocal L γ M μ F = ∑_{ij} M_{ji} perConv L γ (∂_i(μ ∂_jF))`. -/
theorem perConv_fderiv (L : ℝ) (hL : 0 < L) (γ h : Euc d → ℝ) (hγ : LocallyIntegrable γ volume)
    (hγp : ∀ (x : Euc d) (k : Fin d → ℤ), γ (x + L • latticePt k) = γ x) (hh : ContDiff ℝ 1 h)
    (hhp : ∀ (x : Euc d) (k : Fin d → ℤ), h (x + L • latticePt k) = h x) (i : Fin d) (x : Euc d) :
    fderiv ℝ (perConv L γ h) x (EuclideanSpace.single i (1 : ℝ)) =
      perConv L γ (fun y => fderiv ℝ h y (EuclideanSpace.single i (1 : ℝ))) x := by
  sorry

/-- **T6** (size M).  Near/far splitting of the periodic nonlocal operator (exact identity).  Let `θ` be a cutoff (`0 ≤ θ ≤ 1`,
`θ = 1` on `B̄(c,R₁)`, `tsupport θ ⊆ B(c,R₂)`, `R₂ + R₁ < δ L`), `γ` as in `kernel_local_decomposition`.  For `x ∈ B(c, R₁/2)`
and periodic smooth `μ, F`:
`perNonlocal L γ M μ F x = eucNonlocal s M (θ μ) F x
   + ∑_{ij}M_{ji} L^{-s-1} ∫ (∇q)(L⁻¹(x-y))_i (θ μ ∂_jF)(y) dy
   + ∑_{ij}M_{ji} ∫_{y ∈ c + [-L/2,L/2)^d} ∂_iγ(x-y) (1-θ(y)) μ(y) ∂_jF(y) dy`
(near part: Euclidean kernel; smooth remainder; far part, absolutely convergent since `|x-y| ≥ R₁/2` on `supp(1-θ)`).
The constant `c_L` of the decomposition drops out after differentiation.  Route: `perConv_fderiv` (T5),
`kernel_local_decomposition` (T3) on the support of `θ`, translation invariance of the period cell integral,
differentiation under the integral. -/
theorem perNonlocal_split (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (δ : ℝ) (q : Euc d → ℝ)
    (hq : ContDiff ℝ ∞ q) (L : ℝ) (hL : 1 ≤ L) (γ : Euc d → ℝ)
    (hγ : HRS.Whole.AppendixALemmas.IsPeriodicRieszKernel d s L γ) (c₀ : ℝ)
    (hdec : ∀ u : Euc d, u ≠ 0 → ‖u‖ < δ * L → γ u = rieszKernel d s u + c₀ + L ^ (-s) * q (L⁻¹ • u))
    (M : Matrix (Fin d) (Fin d) ℝ) (μ F : Euc d → ℝ) (hμ : ContDiff ℝ ∞ μ) (hF : ContDiff ℝ ∞ F)
    (hμp : ∀ (x : Euc d) (k : Fin d → ℤ), μ (x + L • latticePt k) = μ x)
    (hFp : ∀ (x : Euc d) (k : Fin d → ℤ), F (x + L • latticePt k) = F x)
    (c : Euc d) (R₁ R₂ : ℝ) (hR : R₁ < R₂) (hRδ : R₂ + R₁ < δ * L) (θ : Euc d → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (hθ1 : ∀ y ∈ Metric.closedBall c R₁, θ y = 1) (hθs : tsupport θ ⊆ Metric.ball c R₂)
    (hθ01 : ∀ y, θ y ∈ Icc (0 : ℝ) 1) (x : Euc d) (hx : x ∈ Metric.ball c (R₁ / 2)) :
    perNonlocal L γ M μ F x = eucNonlocal s M (fun y => θ y * μ y) F x +
      ∑ i : Fin d, ∑ j : Fin d, M j i * (L ^ (-s - 1) * ∫ y, fderiv ℝ q (L⁻¹ • (x - y)) (EuclideanSpace.single i (1 : ℝ)) *
        (θ y * μ y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ)))) +
      ∑ i : Fin d, ∑ j : Fin d, M j i * ∫ y in {y | y - c ∈ centeredBox d L},
        fderiv ℝ γ (x - y) (EuclideanSpace.single i (1 : ℝ)) *
          ((1 - θ y) * (μ y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ)))) := by
  sorry

/-- **T7** (size M/L, two instances `n = 1, 2`; the threshold `L₁ ≤ L` was added on 2026-10-19 after a counterexample for small `L`, plan §8a).  The periodic far field, the analogue of `screened_far` for the periodic
kernel `γ_L` and for its first (`n = 1`) and second (`n = 2`) derivatives (the second derivative is needed for the
top-order terms: `∫∂_iγ(x-y)(1-θ)μ∂_jw dy` must be integrated by parts because `∂_jw` is of order `m+1`):
cell estimate with Schur coefficients `K_{zz'}` (row sums `≤ C`, weighted column sums `≤ Cω_{z'}`) for the far part
`χ_c^τ(x) ∫_{y ∈ c+[-L/2,L/2)^d} ∂^nγ_L(x-y)(1-χ̂_c^τ(y))∂^αμ(y)ψ(y)dy` of an `L`-periodic `ψ` (cells `z'` range over
all of `ℤ^d`: periodic images enter with their own coefficients, so that the weighted Schur property is a statement
about periodic weights), uniformly in `L ≥ 1`, with the periodic decay `μ_decay` of `PerData` in place of the decay
about the origin.  Real centres `c = latticePt z + e`, `‖e‖ ≤ R`.  The period box of the far integral is centred at the PHYSICAL centre `Ψ_τ(c)` of the advected cutoff (as in `perNonlocal_split` with `θ` centred at `Ψ_τ(c)`); a box centred at the preimage `c` would be wrong (repair of 2026-10-19: with it the periodic images of `x ∈ supp χ_c^τ` are not shielded by `1 - χ̂_c^τ` when `|Ψ_τ(c) - c|` is large, and a scout's paper counterexample, not formalized, shows the statement fails when `s + n > d`; see AdjointRdPlan.md §6).  Route: the proof of `screened_far`
(`HRS.MH.Screened.far_core_proof`, ScreenedFar.lean:20, takes the flow facts as plain hypotheses) with the pointwise
bound `|∂^nγ_L(u)| ≤ C(|u|^{-s-n} + L^{-s-n})` on the period cell (`kernel_cube_bound`, T4) and `|u| ≥ 4e^{-Cτ}` on
the supports (flow separation); the new point is the Schur weights: for `|c| ≤ L/2` the periodic density is dominated
by `Λ∑_k⟨y - Lk⟩^{-(d+3)}` and `ω_z` (non-periodic) is compared with its periodization on the central cell
(`∑_kω_{z+Lk} ≍ ω_z` for `|z| ≤ L√d`).  RISK: the weighted column estimate for the periodic kernel is not in the TeX
(plan section 6). -/
theorem screened_far_periodic (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (Λ Cb T R : ℝ)
    (n : ℕ) (hn : n = 1 ∨ n = 2) :
    ∀ χ χh : Euc d → ℝ, IsCutoffPair χ χh →
    ∃ C L₁ : ℝ, ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      IsAdvectingDrift m Cb T b → IsNegDriftFlow T b Ψ →
      ∀ (L : ℝ) (γ : Euc d → ℝ), 1 ≤ L → L₁ ≤ L → HRS.Whole.AppendixALemmas.IsPeriodicRieszKernel d s L γ →
      ∀ μ : Euc d → ℝ, ContDiff ℝ ∞ μ → (∀ (x : Euc d) (k : Fin d → ℤ), μ (x + L • latticePt k) = μ x) →
      (∀ j ≤ m + 3, ∀ x : Euc d, ∃ k : Fin d → ℤ,
        jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ j μ x‖ ≤ Λ) →
      ∀ τ ∈ Icc (0 : ℝ) T, ∀ e : Euc d, ‖e‖ ≤ R →
      ∃ Kc : (Fin d → ℤ) → (Fin d → ℤ) → ℝ≥0,
        (⨆ z, ∑' z', (Kc z z' : ℝ≥0∞) ≤ ENNReal.ofReal C) ∧
        (∀ z', ∑' z, ENNReal.ofReal (cellWeight d z) * (Kc z z' : ℝ≥0∞) ≤
          ENNReal.ofReal C * ENNReal.ofReal (cellWeight d z')) ∧
        ∀ (j : ℕ), j ≤ m + 1 → ∀ (idx : Fin j → Fin d) (κ : Fin n → Fin d) (ψ : Euc d → ℝ), Measurable ψ →
          (∀ (x : Euc d) (k : Fin d → ℤ), ψ (x + L • latticePt k) = ψ x) → ∀ z : Fin d → ℤ,
            (eLpNorm (fun x => advCutoff χ Ψ τ (latticePt z + e) x *
                ∫ y in {y | y - Ψ τ (latticePt z + e) ∈ centeredBox d L},
                  iteratedFDeriv ℝ n γ (x - y) (fun l => EuclideanSpace.single (κ l) (1 : ℝ)) *
                    ((1 - advCutoff χh Ψ τ (latticePt z + e) y) * (partialDeriv idx μ y * ψ y))) 2 volume) ^ 2 ≤
              ENNReal.ofReal (C * Λ ^ 2) * ∑' z', (Kc z z' : ℝ≥0∞) *
                (eLpNorm ((flowCellAt Ψ τ (latticePt z' + e)).indicator ψ) 2 volume) ^ 2 := by
  sorry

/-! ### Group E: the energy engine -/

/-- **E1** (size M).  Differentiation of the cell energy: along a classical solution (`IsClassicalSol`) with an advecting
drift and its flow, `τ ↦ 𝓕_c(τ) = cellEnergy m χ Ψ τ c (F τ)` is differentiable on `[0,t]` (one-sided at the ends) with
derivative `cellRate`.  Route: `∂_τ` under `∫` (compact support of `χ_c^τ`, locally uniform continuity of the integrand's
`τ`-derivative: the jets of `F` and the cutoff derivative are jointly continuous, `contF`, and
`(τ,x) ↦ χ(Ψ_τ^{-1}x - c)` is `C¹` in `τ` by `flow_cutoff_hasDerivWithinAt` with the adaptors `f1a_drift`, `f1a_flow`
(ScreenedF1.lean:22, 33) and `flow_inv_hasDerivWithinAt` (FlowDAux2.lean:154)), `hasDerivAt_integral_of_dominated_loc_of_deriv_le`. -/
theorem cell_energy_hasDeriv (hd : 1 ≤ d) (m : ℕ) (Cb T : ℝ) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh)
    (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d) (hb : IsAdvectingDrift m Cb T b) (hΨ : IsNegDriftFlow T b Ψ)
    (ν : ℝ) (G : ℝ → Euc d → ℝ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (F : ℝ → Euc d → ℝ)
    (hF : IsClassicalSol m ν b G t F) (c : Euc d) (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) t) :
    HasDerivWithinAt (fun τ' => cellEnergy m χ Ψ τ' c (F τ')) (cellRate m χ Ψ τ c ν (b τ) (F τ) (G τ))
      (Icc (0 : ℝ) t) τ := by
  sorry

/-- **E2** (size L).  The generic (regime-free) part of the cell inequality: transport, diffusion and Leibniz commutators.
There are a finite set `E ⊂ ℤ^d` of integer offsets and `A ≥ 0`, depending on `d, m, Cb, T, ν̄, χ`, such that
for every classical solution, every `τ ∈ [0,t]` and every lattice centre `cellPt z`,
`cellRate ≤ -ν·cellDissip(z) + A ∑_{k∈E}𝓕_{z+k} + 2·jetPair(χ_z; F, G)`.
Route: (1) transport: `2∫χ²∂^αF b·∇∂^αF + 2∫χ(b·∇χ)(∂^αF)² = -∫χ²(div b)(∂^αF)²` (integrate by parts, compact support);
(2) commutator `∂^α(b·∇F) - b·∇∂^αF = ∑_{0<β≤α}C(α,β)∂^βb·∇∂^{α-β}F`, jets of `F` of order `≤ m`, `‖∂^βb‖_∞ ≤ Cb`
(`IsAdvectingDrift.deriv_bdd`); (3) diffusion: `2ν∫χ²u Δu = -2ν∫χ²|∇u|² - 4ν∫χ u ∇χ·∇u ≤ -ν∫χ²|∇u|² + 4ν∫|∇χ|²u²` and
`|∇χ_c^τ| ≤ Lχe^{CFτ}` (`HRS.MH.Screened.advCutoff_facts_proof`, ScreenedF5.lean:53, `cutoff_lipschitz_proof`, ScreenedF6.lean:25)
with `1_{supp∇χ_c^τ} ≤ ∑_{k∈E}χ_{c+k}^τ` (the finitely many unit balls covering `B(0,2)` in preimage coordinates; `χ=1` on
unit balls); `E` as lattice offsets of the fine lattice `cellPt`. -/
theorem cell_rate_generic (hd : 1 ≤ d) (m : ℕ) (Cb T νbar : ℝ) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) :
    ∃ (E : Finset (Fin d → ℤ)) (A : ℝ), 0 ≤ A ∧ ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      IsAdvectingDrift m Cb T b → IsNegDriftFlow T b Ψ → ∀ ν : ℝ, 0 ≤ ν → ν ≤ νbar →
      ∀ (G : ℝ → Euc d → ℝ) (t : ℝ), t ∈ Icc (0 : ℝ) T → ∀ F : ℝ → Euc d → ℝ, IsClassicalSol m ν b G t F →
      (∀ τ ∈ Icc (0 : ℝ) t, BddJets m (F τ)) → ∀ τ ∈ Icc (0 : ℝ) t, ∀ z : Fin d → ℤ,
        cellRate m χ Ψ τ (cellPt d z) ν (b τ) (F τ) (G τ) ≤
          -ν * cellDissip m χ Ψ τ (cellPt d z) (F τ) +
            A * ∑ k ∈ E, cellEnergy m χ Ψ τ (cellPt d (z + k)) (F τ) +
            2 * jetPair m (advCutoff χ Ψ τ (cellPt d z)) (F τ) (G τ) := by
  sorry

/-- **H1** (size L).  Second-derivative local bound, regime R1 (`s ≤ d-2`, where `∂_i∂_jg` is locally integrable for
`s < d-2` and a Calderón-Zygmund kernel at `s = d-2`).  For `v ∈ C_c^∞` supported in `B̄(c,ρ)`, `ρ ≥ 1`, and every ball
`B` of radius `≤ ρ`: `‖1_B ∂_i∂_j(g*v)‖_{L²} ≤ Cρ^{C₀}‖v‖_{L²}`, `g * v = ∫ g(·-y)v(y)dy`.  Route: `s < d-2`: Young
(`|∂_i∂_jg| ≤ C|u|^{-s-2}` integrable at `0`; the part of the kernel outside `B(0,2ρ)` contributes `ρ^{d-s-2}`-type factors by
Minkowski/Schur); `s = d-2`: Plancherel with the bounded symbol `ξ_iξ_j|ξ|^{-2}ĝ`-type multiplier (`ĝ(ξ) = c|ξ|^{s-d}`, so
`\widehat{∂_i∂_jg}(ξ) = -4π²c ξ_iξ_j|ξ|^{-2}`), which is a bounded multiplier; the repository's `screened_local` (first
derivative, `(θ-1)^+`) is NOT enough: this is the one place where the TeX uses `∂_i∂_jg` (S L10405-10412). -/
theorem hess_local (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd2 : s ≤ (d : ℝ) - 2) :
    ∃ C₀ C : ℝ, ∀ (i j : Fin d) (ρ : ℝ), 1 ≤ ρ → ∀ (c : Euc d) (v : Euc d → ℝ), ContDiff ℝ ∞ v →
      Function.support v ⊆ Metric.closedBall c ρ →
      ∀ (c' : Euc d) (r' : ℝ), r' ≤ ρ →
        eLpNorm ((Metric.closedBall c' r').indicator (fun x =>
            iteratedFDeriv ℝ 2 (fun x' => ∫ y, rieszKernel d s (x' - y) * v y) x
              (fun l => EuclideanSpace.single (if l = 0 then i else j) (1 : ℝ)))) 2 volume ≤
          ENNReal.ofReal (C * ρ ^ C₀) * eLpNorm v 2 volume := by
  sorry

/-- **H2** (size L).  Local bound for the commutator of the second-order kernel with an advected cutoff, `s ≤ d-1` (order
`θ - 1 ≤ 0`): for `v ∈ C_c^∞` supported in a ball of radius `ρ ≥ 1`, any `z ∈ ℝ^d`, `τ ∈ [0,T]`, and balls `B` of radius `≤ ρ`,
`‖1_B(χ_z^τ·∂_i∂_j(g*v) - ∂_i∂_j(g*(χ_z^τ v)))‖_{L²} ≤ Ce^{Cdτ}ρ^{C₀}‖v‖_{L²}`.  Route: kernel
`∂_i∂_jg(x-y)(χ(x)-χ(y))` has size `|u|^{-s-1}` (integrable at `0` for `s < d-1`) times `Lχ e^{CFτ}`; at `s = d-1` an odd
Calderón-Zygmund kernel of degree `-d` (the product of the even `∂_i∂_jg` and the odd `χ(x)-χ(y) ≈ ∇χ·(x-y)`), bounded on
`L²` by Plancherel after the Taylor expansion of `χ`.  Used by the Euclidean regime packets R1, R2a (lower-order terms), R2c.
UNVERIFIED in the TeX (S L10405-10412 only says "commutators are lower order"); the first-order analogue is
`HRS.MH.Screened.screened_comm_local_proof` (ScreenedAsmCommLocal.lean). -/
theorem hess_comm_local (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ (d : ℝ) - 1) (m : ℕ) (Cb T : ℝ) :
    ∀ χ χh : Euc d → ℝ, IsCutoffPair χ χh →
    ∃ C₀ C : ℝ, ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      IsAdvectingDrift m Cb T b → IsNegDriftFlow T b Ψ →
      ∀ τ ∈ Icc (0 : ℝ) T, ∀ (z : Euc d) (i j : Fin d) (ρ : ℝ), 1 ≤ ρ → ∀ (c : Euc d) (v : Euc d → ℝ),
      ContDiff ℝ ∞ v → Function.support v ⊆ Metric.closedBall c ρ →
      ∀ (c' : Euc d) (r' : ℝ), r' ≤ ρ →
        eLpNorm ((Metric.closedBall c' r').indicator (fun x =>
            advCutoff χ Ψ τ z x * iteratedFDeriv ℝ 2 (fun x' => ∫ y, rieszKernel d s (x' - y) * v y) x
                (fun l => EuclideanSpace.single (if l = 0 then i else j) (1 : ℝ)) -
              iteratedFDeriv ℝ 2 (fun x' => ∫ y, rieszKernel d s (x' - y) * (advCutoff χ Ψ τ z y * v y)) x
                (fun l => EuclideanSpace.single (if l = 0 then i else j) (1 : ℝ)))) 2 volume ≤
          ENNReal.ofReal (C * Real.exp (C * d * τ) * ρ ^ C₀) * eLpNorm v 2 volume := by
  sorry

/-- **E3-R1** (size L).  `(HN-E)` in regime R1 (`s ≤ d-2`, any `M` with `|M| ≤ MB`, `κ = 0`).  Route: the TeX proof
(S L10405-10412): the top-order term `⟨χ²∂^αF, ∂_ig*(μ∂_j∂^αF)⟩` is, after integrating by parts in `y`, a pairing with the
kernel `∂_i∂_jg` of order `θ ≤ 0` (`hess_local`, cutoff commutators `hess_comm_local`, plus `screened_local_proof`,
`screened_comm_local_proof` for the terms in which derivatives fall on `μ` and on the cutoff); all other terms are
bounded by `screened_local` with `(θ-1)^+ = 0` (order `0`, since `s ≤ d-2 < d-1`) acting on `∂^βμ·∂^{α-β}∂F`, `|β| ≥ 1`
(derivative order `≤ m`).  The near cut `a = χ̂_c^τ μ` is compactly supported in `B(Ψ_τ(c), 8e^{CFτ})`: the Euclidean
lemmas apply with `ρ = 8e^{CFT}` and the neighbours `E` cover that ball. -/
theorem euc_nl_R1 (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd2 : s ≤ (d : ℝ) - 2) (m : ℕ) (hm : 1 ≤ m)
    (MB Λ Cb T : ℝ) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) :
    ∃ (E : Finset (Fin d → ℤ)) (A : ℝ), CoversBall8 E ∧ 0 ≤ A ∧
      EucNlBound s m Λ Cb T χ χh E A 0 (fun M => PDE.MatBound MB M) := by
  sorry

/-- **E3-R2a** (size M/L).  `(HN-E)` in regime R2a (`d-2 < s < d`, `sym M = 0`, `κ = 0`).  Route (an exact cancellation, which makes
the TeX's appeal to `same_function_rd` (S.B.8, S L10413-10416) unnecessary): with `M` antisymmetric,
`∑_{ij}M_{ji}∂_i∂_jg = 0`, so for any `w` and any smooth `h`
`∑M_{ji}∂_ig*(h∂_jw) = ∑M_{ji}∂_i∂_jg*(hw) - ∑M_{ji}∂_ig*((∂_jh)w) = -∑M_{ji}∂_ig*((∂_jh)w)`.
Apply to `∂^α𝒢[F]`: (i) the top term (`β = 0`, `h = a`) is `-∑M_{ji}∂_ig*((∂_ja)u)`, `u = ∂^αF`, an operator of order `θ-1 ∈ (-1,1)`;
its pairing `⟨χ²u, ·⟩` is, by the oddness of `∂_ig`, `½∬∂_ig(x-y)(c_i(y)-c_i(x))U(x)U(y)` with `c_i = ∑_jM_{ji}∂_ja` Lipschitz,
so it is bounded by `C‖c‖_{C^1}∬|x-y|^{-s}|U(x)||U(y)|`, locally `L¹`-kernel (`s < d`), i.e. by `C𝓕_c` (Young/Schur,
`young_l1_l2`, ScreenedSpec.lean:102) after the cutoff commutators of order `θ-2 < 0` (`hess_comm_local`-type); (ii) the lower terms
`β ≠ 0`: the same identity moves `∂_j` off the factor of order `m-|β|+1`, leaving the kernel `∂_ig` of order `θ-1` on a jet of
order `≤ m-|β|`, total derivative count `≤ 2m + θ - 2 < 2m`: bounded by `screened_local`/`screened_pairing` (S.B.1/B.3)
with the half-half split.  The only global input is `s < d` (local integrability of `|u|^{-s}`).  This avoids any use of positivity. -/
theorem euc_nl_R2a (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hs2 : (d : ℝ) - 2 < s) (m : ℕ) (hm : 1 ≤ m)
    (MB Λ Cb T : ℝ) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) :
    ∃ (E : Finset (Fin d → ℤ)) (A : ℝ), CoversBall8 E ∧ 0 ≤ A ∧
      EucNlBound s m Λ Cb T χ χh E A 0 (fun M => PDE.MatBound MB M ∧ Torus.symPart M = 0) := by
  sorry

/-- **E3-R2c** (size L).  `(HN-E)` in regime R2c (`d-2 < s ≤ d-1`, `sym M ≤ 0`, `κ = 0`).  Route: top order
`⟨u, ∑S_{ij}∂_i∂_jg*(a u)⟩`, `u = χ_c^τ∂^αF`, `S = sym M ≤ 0`, whose Fourier symbol `m(ξ) = -4π²ĝ(ξ)ξᵀSξ ≥ 0` is
homogeneous of degree `θ ∈ (0,1]` (`IsHomogSymbol`, nonnegative): by `HRS.PDE.ToolboxRd.Weighted.weighted_core`
(Weighted.lean:578) `⟨u, K(a u)⟩ = ⟨√a u, K(√a u)⟩ + O((Lip√a² + sup a)‖u‖²_{L²})`, and `symbolForm_self_nonneg'`
(Weighted.lean:566) gives `⟨√a u, K(√a u)⟩ ≥ 0`; `√a` is Lipschitz because `a = μ ≥ 0` is `C^{1,1}` (`IsC11`); the
remainder `u`-norms are `L²`, controlled by `𝓕_c`.  Commutators `[χ_c^τ, K]`: `hess_comm_local` (order `θ-1 ≤ 0`); the
terms where derivatives fall on `μ` or on lower jets: `screened_local`/`screened_pairing`
(order `(θ-1)^+ = 0`).  The antisymmetric part of `M` is handled as in R2a.  UNVERIFIED in the TeX (S L10417-10421). -/
theorem euc_nl_R2c (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hs2 : (d : ℝ) - 2 < s) (hs1 : s ≤ (d : ℝ) - 1)
    (m : ℕ) (hm : 1 ≤ m) (MB Λ Cb T : ℝ) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) :
    ∃ (E : Finset (Fin d → ℤ)) (A : ℝ), CoversBall8 E ∧ 0 ≤ A ∧
      EucNlBound s m Λ Cb T χ χh E A 0 (fun M => PDE.MatBound MB M ∧ Torus.SymNonpos M) := by
  sorry

/-- **E3-R3** (size L, XL risk).  `(HN-E)` in regime R3 (`d-2 < s < d`, any `M`, dissipation `ν ≥ ν₀ > 0`):
for every `ν₀ > 0`, `κ = ν₀/(8|E|)` and `A = C(1 + ν₀^{-θ/(2-θ)})`, `θ = s+2-d ∈ (0,2)` (constants independent of `ν₀`).
Route: the nonlocal term is a pseudo-differential operator of order `θ`: the cell pairing is bounded by
`C‖χ̂_c^τ F‖²_{H^{m+θ/2}}` (half-half split of the kernel: `ξ`-space `|ξ|^θ ≤ |ξ|^{θ/2}|ξ|^{θ/2}`, `bilinear_core`
(Bilinear.lean:291) and `scaling_bound` (:184) for the Gagliardo form with the Lévy kernel `𝔨 = ∂_i∂_jg`), then the cell
interpolation `‖u‖²_{H^{θ/2}} ≤ ε‖∇u‖² + C_ε‖u‖²` with `ε = ν₀/(8|E|C)`, `C_ε ≍ ε^{-θ/(2-θ)}`, giving the form
`κ∑D_{z+k} + A∑𝓕_{z+k}` (`E` also absorbs the cutoff commutators of order `θ-1 < 1`, interpolated the same way).  The cell
version of the interpolation needs the fixed-cutoff Sobolev norm on balls and is not stated in the TeX (S L10422-10427 says "same
argument as on the torus"); the torus version is `HRS/PDE/Energy.lean` (`energy_torus` R3 branch, EnergyEstimate.lean:554) and
the global toolbox is `HRS.PDE.ToolboxRd` (`weighted_core`, `compare_core`, `bilinear_core`, `IsLevyKernel`, `symbolKRd`). -/
theorem euc_nl_R3 (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hs2 : (d : ℝ) - 2 < s) (m : ℕ) (hm : 1 ≤ m)
    (MB Λ Cb T : ℝ) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) :
    ∃ (E : Finset (Fin d → ℤ)) (C : ℝ), CoversBall8 E ∧ 0 ≤ C ∧ ∀ ν₀ : ℝ, 0 < ν₀ →
      EucNlBound s m Λ Cb T χ χh E (C * (1 + ν₀ ^ (-(PDE.thetaOrder d s / (2 - PDE.thetaOrder d s)))))
        (ν₀ / (8 * E.card)) (fun M => PDE.MatBound MB M) := by
  sorry

/-- **E3** (size M, assembly).  From the Euclidean near estimate to the periodic estimate, regime-independently and
uniformly in the regime constants: there are `C₁, A₀, CK ≥ 0` (depending on `d, s, m, MB, Λ, ΛV, ν̄, Cb, T, χ`) such that for every
offset set `E` covering `B̄(0,8)` and all `A, κ` and regime predicates `hreg`, `(HN-E)` at the density bound `C₁Λ`
implies `(HN)` with `A + A₀`, the same `κ`, and the Schur constant `CK`.  Route: `perNonlocal_split` (T6) with
`c = cellPt z`-neighbourhood, `θ = χ̂_c^τ`: the periodic `F, μ` are replaced by the cut `θ μ` (compact support in
`B(c,8)` in preimage coordinates, `IsRegularDensityW (m+3) (C₁Λ)` after translating the cell to the central cube: the periodic
decay gives the origin-centred decay with the factor `⟨R⟩^{d+3}`, `R` the radius of the support); the smooth remainder
`L^{-s-1}(∇q)(·/L) * (θ μ ∂_jF)` has all derivatives bounded by `C‖q‖_{C^{m+3}}` times jets of `F` on the cut ball, hence
by `A₀∑_{k∈E}𝓕_{z+k}` (the derivative `∂_jF` is moved to the other factors by one integration by parts); the far part by
`screened_far_periodic` (T7, `n = 1, 2`; `∂_jF` is integrated by parts) and Cauchy-Schwarz with `‖χ_z∂^αF‖_{L²}`; the shifted
real centres `cellPt z = latticePt z'' + e_r` as in `screened_far_shift` (F1a). -/
theorem periodic_nl_of_euclid (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (MB Λ ΛV νbar Cb T : ℝ) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) :
    ∃ C₁ A₀ CK L₁ : ℝ, 0 ≤ C₁ ∧ 0 ≤ A₀ ∧ 0 ≤ CK ∧ ∀ (E : Finset (Fin d → ℤ)), CoversBall8 E →
      ∀ (A κ : ℝ) (hreg : Matrix (Fin d) (Fin d) ℝ → Prop),
        EucNlBound s m (C₁ * Λ) Cb T χ χh E A κ hreg →
        NlCellBound s m MB Λ ΛV νbar Cb T χ χh E (A + A₀) κ CK L₁ hreg := by
  sorry

/-- **E4** (size M, assembly).  The uniform `H^m_uloc` bound for the periodic approximants: from `cell_energy_hasDeriv` (E1),
`cell_rate_generic` (E2), `(HN)` (E3, per regime) and the Gronwall lemma `gronwall_sup_dissip` (G3, `ν ≥ ν₀` in R3
absorbs the dissipation `κ∑D`; `gronwall_sup` (G1) suffices when `κ = 0`), together with `uloc_moving_equiv` (F3), `cell_cover`
(F2: the Schur term `∑_{z'}K_{zz'}mass_{z'} ≤ CK·N·sup_z𝓕_z`), `flow_exists_adv` (F0) and `reversed_data`-type bounds
(`PerData.b_drift`): `‖F(τ)‖_{H^m_uloc} ≤ C e^{Λ_mτ}‖F(0)‖_{H^m_uloc}` with `C` independent of `L` (and of `ν₀`),
`Λ_m = lambdaM Rg C ν₀ θ` (R3: `A = C(1+ν₀^{-θ/(2-θ)})`; the factor `2` of G3 is the prefactor).  Regime dispatch:
R1 `euc_nl_R1`, R2a `euc_nl_R2a`, R2c `euc_nl_R2c`, R3 `euc_nl_R3`, each through `periodic_nl_of_euclid`. -/
theorem per_uloc_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m) (Rg : PDE.Regime)
    (MB Λ ΛV νbar Cb T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C L₁ : ℝ, 0 < C ∧ ∀ (ν₀ L : ℝ) (γ : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (μ : ℝ → Euc d → ℝ)
      (V : Euc d → ℝ) (b : ℝ → Euc d → Euc d), L₁ ≤ L → PerData s m MB Λ ΛV νbar Cb T L γ M ν μ V b →
      RdRegimeHolds Rg d s M ν ν₀ → ∀ t ∈ Ioc (0 : ℝ) T, ∀ F : ℝ → Euc d → ℝ,
        IsPerSol m L γ M ν μ b (fun _ _ => 0) t F → ∀ τ ∈ Icc (0 : ℝ) t,
          ulocNormE m χ (F τ) ≤
            ENNReal.ofReal (C * Real.exp (Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ)) * ulocNormE m χ (F 0) := by
  sorry

/-- **E5** (size M/L, assembly, RISK).  The uniform weighted bound for the periodic approximants,
`‖F(τ)‖_{H^m(ϖ)} ≤ C e^{Λ_mτ}‖F(0)‖_{H^m(ϖ)}`, with `C` independent of `L`: `gronwall_weighted` (G2) with the fine-lattice
cells (`varpi_moving_equiv`, F4), the Schur kernels of `periodic_nl_of_euclid` (`NlCellBound`: `∑_zω_zK_{zz'} ≤ CKω_{z'}`)
and the comparability `ω_z ≤ c_ω ω_{z+k}`, `k ∈ E`.  The periodic weighted column estimate (T7) is the unverified step. -/
theorem per_weighted_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m) (Rg : PDE.Regime)
    (MB Λ ΛV νbar Cb T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C L₁ : ℝ, 0 < C ∧ ∀ (ν₀ L : ℝ) (γ : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (μ : ℝ → Euc d → ℝ)
      (V : Euc d → ℝ) (b : ℝ → Euc d → Euc d), L₁ ≤ L → PerData s m MB Λ ΛV νbar Cb T L γ M ν μ V b →
      RdRegimeHolds Rg d s M ν ν₀ → ∀ t ∈ Ioc (0 : ℝ) T, ∀ F : ℝ → Euc d → ℝ,
        IsPerSol m L γ M ν μ b (fun _ _ => 0) t F → ∀ τ ∈ Icc (0 : ℝ) t,
          varpiNormE m χ (F τ) ≤
            ENNReal.ofReal (C * Real.exp (Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ)) * varpiNormE m χ (F 0) := by
  sorry

/-- **E6** (size L, assembly).  The stability estimate for periodic approximants: for two data sets with the same `L, γ, M, V`,
`F_a` the solutions with the same datum, the difference `z = F₁ - F₂` solves the equation with the coefficients of the SECOND solution
and the source `S = (ν₁-ν₂)ΔF₂ + (b₁-b₂)·∇F₂ - (𝒢₁-𝒢₂)[F₂]` (`IsPerSol` with `S ≠ 0`), where the three terms are bounded
in the local cell norms by `|ν₁-ν₂|‖F₂‖_{H^{m+2}}`, `δ‖F₂‖_{H^{m+1}}` and, by the screened lemmas with `a = ∂^β(μ₁-μ₂)`
(norm `δ` replaces `Λ`) and the top-order integration by parts, `Cδ‖F₂‖_{H^{m+1+(θ-1)^+}}`.  `G1`/`G2` with the source term
`h(τ) = C(|ν₁-ν₂|+δ)²‖F₂(τ)‖²_{H^{m+2}}` (E4/E5 at level `m+2` for `F₂`) gives the factor `τ`: the cross term is `2√(𝓕 h) ≤ 𝓕/τ + τh`, so apply G1/G2/G3 on `[0,τ]` with `A + 1/τ`
(`e^{(A+1/τ)τ} = e·e^{Aτ}`) and source `τh`, then take square roots: `‖z(τ)‖ ≲ τ·e^{Aτ}·C(|ν₁-ν₂|+δ)‖F₂‖_{m+2}` (a plain Young bound `2√(𝓕h) ≤ 𝓕 + h` would only give `√τ`).  Both the `uloc` and `varpi`
clauses.  The hypotheses `hμδ`, `hbδ` are the periodic images of `coeffNormE ≤ δ` supplied by T2c (packet `per_coefficients_pair`). -/
theorem per_stability_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m) (Rg : PDE.Regime)
    (MB Λ ΛV νbar Cb T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C C' L₁ : ℝ, 0 < C ∧ 0 < C' ∧ ∀ (ν₀ L : ℝ) (γ : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ν₁ ν₂ : ℝ)
      (μ₁ μ₂ : ℝ → Euc d → ℝ) (V : Euc d → ℝ) (b₁ b₂ : ℝ → Euc d → Euc d), L₁ ≤ L →
      PerData s (m + 2) MB Λ ΛV νbar Cb T L γ M ν₁ μ₁ V b₁ → PerData s (m + 2) MB Λ ΛV νbar Cb T L γ M ν₂ μ₂ V b₂ →
      RdRegimeHolds Rg d s M ν₁ ν₀ → RdRegimeHolds Rg d s M ν₂ ν₀ → ∀ δ : ℝ, 0 ≤ δ →
      (∀ τ ∈ Icc (0 : ℝ) T, ∀ j ≤ m + 2, ∀ x : Euc d,
        ‖iteratedFDeriv ℝ j (fun y => μ₁ τ y - μ₂ τ y) x‖ ≤ δ ∧ ∃ k : Fin d → ℤ,
          jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ j (fun y => μ₁ τ y - μ₂ τ y) x‖ ≤ δ) →
      (∀ τ ∈ Icc (0 : ℝ) T, ∀ j ≤ m + 1, ∀ x : Euc d,
        ‖iteratedFDeriv ℝ j (fun y => b₁ τ y - b₂ τ y) x‖ ≤ δ) →
      ∀ t ∈ Ioc (0 : ℝ) T, ∀ F₁ F₂ : ℝ → Euc d → ℝ,
        IsPerSol (m + 2) L γ M ν₁ μ₁ b₁ (fun _ _ => 0) t F₁ →
        IsPerSol (m + 2) L γ M ν₂ μ₂ b₂ (fun _ _ => 0) t F₂ → F₁ 0 = F₂ 0 →
        ∀ τ ∈ Icc (0 : ℝ) t,
          ulocNormE m χ (fun x => F₁ τ x - F₂ τ x) ≤
            ENNReal.ofReal (C * τ * Real.exp (Rg.lambdaM C' ν₀ (PDE.thetaOrder d s) * τ) * (|ν₁ - ν₂| + δ)) *
              ulocNormE (m + 2) χ (F₁ 0) ∧
          varpiNormE m χ (fun x => F₁ τ x - F₂ τ x) ≤
            ENNReal.ofReal (C * τ * Real.exp (Rg.lambdaM C' ν₀ (PDE.thetaOrder d s) * τ) * (|ν₁ - ν₂| + δ)) *
              varpiNormE (m + 2) χ (F₁ 0) := by
  sorry

/-- **T2c** (size M/L).  The PAIR version of `per_coefficients`, with the discrepancy.  For two data sets `(D₁, μ₁)`, `(D₂, μ₂)` at
level `m+2` with `D₁.M = D₂.M`, `D₁.V = D₂.V` and `coeffNormE d s m (μ₁ r - μ₂ r) ≤ δ` for `r ≤ T`, the periodic approximants of
`per_coefficients` can be built with the SAME mollifier, cutoff `ζ` and the same potential `VL`, so that both families satisfy
`PerApprox` (same constants `Λ', ΛV', Cb, L₀`, independent of the data) and the differences obey the hypotheses `hμδ`, `hbδ` of
`per_stability_bound` with `δ` replaced by `C δ`.  Route: the construction of `per_coefficients` is linear in `μ` except for
the normalisation `c_a = ∫ζ_Lμ_a` (a smooth function of the mass, `|c₁-c₂| ≤ Cδ`, `c_a = 1 + O(L^{-big})`); the estimates of
`per_coefficients` applied to the difference `μ₁ - μ₂` (cutoff, periodization, mollification, `torusDriftL`, all linear),
with the weighted `C^{m+2}` part of `coeffNormE` as the decay norm and, for `s ≥ d-1`, the singular-force term of `coeffNormE`
to bound `∇γ_L ⊛ (μ₁-μ₂)` in sup norm.  The statement is a single existential over BOTH families so that no construction has to be named. -/
theorem per_coefficients_pair (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (MB Λ ΛV G₀ νbar T : ℝ) (ζ : Euc d → ℝ) (hζ : HRS.Whole.AppendixALemmas.IsCutoffRad (1 / 4) (1 / 3) ζ) :
    ∃ Λ' ΛV' Cb L₀ C : ℝ, 0 < C ∧ ∀ (D₁ D₂ : WholeDyn d) (μ₁ μ₂ : ℝ → Euc d → ℝ),
      AdjointRdData s (m + 2) MB Λ ΛV G₀ νbar D₁ T μ₁ → AdjointRdData s (m + 2) MB Λ ΛV G₀ νbar D₂ T μ₂ →
      D₁.M = D₂.M → D₁.V = D₂.V → ∀ δ : ℝ, 0 ≤ δ →
      (∀ r ∈ Icc (0 : ℝ) T, coeffNormE d s m (μ₁ r - μ₂ r) ≤ ENNReal.ofReal δ) →
      ∀ γ : ℝ → Euc d → ℝ, (∀ L : ℝ, 1 ≤ L → HRS.Whole.AppendixALemmas.IsPeriodicRieszKernel d s L (γ L)) →
      ∀ t ∈ Ioc (0 : ℝ) T, ∃ (μL₁ μL₂ : ℝ → ℝ → ℝ → Euc d → ℝ) (VL : ℝ → ℝ → Euc d → ℝ),
        PerApprox s (m + 2) MB Λ' ΛV' νbar Cb T D₁ μ₁ γ t L₀ μL₁ VL ∧
        PerApprox s (m + 2) MB Λ' ΛV' νbar Cb T D₂ μ₂ γ t L₀ μL₂ VL ∧
        ∀ L : ℝ, max 1 L₀ ≤ L → ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) 1 → ∀ τ ∈ Icc (0 : ℝ) T,
          (∀ j ≤ m + 2, ∀ x : Euc d,
            ‖iteratedFDeriv ℝ j (fun y => μL₁ L ε τ y - μL₂ L ε τ y) x‖ ≤ C * δ ∧ ∃ k : Fin d → ℤ,
              jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ j (fun y => μL₁ L ε τ y - μL₂ L ε τ y) x‖ ≤ C * δ) ∧
          ∀ j ≤ m + 1, ∀ x : Euc d,
            ‖iteratedFDeriv ℝ j (fun y => HRS.Whole.AppendixALemmas.torusDriftL D₁.M L (γ L) (μL₁ L ε τ) (VL L ε) y -
              HRS.Whole.AppendixALemmas.torusDriftL D₂.M L (γ L) (μL₂ L ε τ) (VL L ε) y) x‖ ≤ C * δ := by
  sorry

/-- **E7** (size XL, RISK).  The global weighted bound with the weights `w_R(x) = ⟨x/R⟩^{-(d+3)}` for the periodic approximants,
for `2(s+1) > d`: with the SAME constant for all `R ≥ 1` (the transport term `b·∇w_R` is bounded by `C_b w_R` with `C_b`
independent of `R` since `|b| ≤ Cb(1+|x|)` and `|∇w_R| ≲ w_R/R·(|x|/R)/⟨x/R⟩`; it only changes the exponent, never the prefactor),
`Jet_R(F(τ)) ≤ e^{2Λ_mτ}(Jet_R(F(0)) + C R^C L^{-κ}B²)`, `Jet_R = jetSq m w_R`, where `B` bounds the `H^m_uloc` norms
(the last term is the interaction with the periodic images, `O(L^{-κ})`).  Route: the energy identity with the
weight `w_R` in place of the cutoff `χ_c^τ` (no cells: `w_R` is a single global weight, `jetSq` is the exact
`H^m` form by N2), diffusion/transport/Leibniz as in E2, the nonlocal term in the regime by the global
`ToolboxRd` forms (`weighted_core`, `symbolForm_self_nonneg'`; the far field by Young with `‖∂_ig 1_{|u|>1}‖_{L²} < ∞` iff
`2(s+1) > d`, weights compared through the monotonicity `w_R(x) ≤ w_R(y)` for `|x| ≥ |y|`), the images by `kernel_cube_bound` (T4). -/
theorem per_globalweight_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (hs : (d : ℝ) < 2 * (s + 1))
    (m : ℕ) (hm : 1 ≤ m) (Rg : PDE.Regime) (MB Λ ΛV νbar Cb T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ (ν₀ R B L : ℝ) (γ : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ)
      (μ : ℝ → Euc d → ℝ) (V : Euc d → ℝ) (b : ℝ → Euc d → Euc d), 1 ≤ R → 0 ≤ B →
      PerData s m MB Λ ΛV νbar Cb T L γ M ν μ V b → RdRegimeHolds Rg d s M ν ν₀ →
      ∀ t ∈ Ioc (0 : ℝ) T, ∀ F : ℝ → Euc d → ℝ, IsPerSol m L γ M ν μ b (fun _ _ => 0) t F →
        (∀ τ ∈ Icc (0 : ℝ) t, ulocNormE m χ (F τ) ≤ ENNReal.ofReal B) → ∀ τ ∈ Icc (0 : ℝ) t,
          jetSq m (fun x => jbracket (R⁻¹ • x) ^ (-((d : ℝ) + 3))) (F τ) ≤
            Real.exp (2 * Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ) *
              (jetSq m (fun x => jbracket (R⁻¹ • x) ^ (-((d : ℝ) + 3))) (F 0) + C * R ^ C * L ^ (-κ) * B ^ 2) := by
  sorry

/-! ### Group L: the limit `L → ∞, ε → 0` -/

/-- **L1** (size M).  The weak form of a smooth periodic solution against compactly supported tests: an `IsPerSol` solution
(with `S = 0`, jets of order `≤ 2`, `t ≤ T`) satisfies `IsWeakSol (weakOpPer L γ M ν μ b) t (F 0) F`.  Route: for fixed `ψ`,
`τ ↦ ∫Fψ` is `C^1` with derivative `∫ ∂_τF ψ` (differentiation under the integral: `ψ` has compact support, `∂_τF`
is jointly continuous on the compact support, `IsClassicalSol.contF`, `deriv_t` with `j = 0`), and
`∫ψ(νΔF + b·∇F) = ∫F(νΔψ - div(bψ))` by integration by parts (compact support of `ψ`, `F ∈ C^2`;
`HRS.Whole.Moving` has `movDiv`); the nonlocal term: Fubini on `(x,y) ∈ ℝ^d × [0,L)^d` and periodicity give
`∫_{ℝ^d}ψ · perNonlocal L γ M μ F = ∑_{ij}M_{ji}∫_{[0,L)^d}F ∂_j(μ ∂_i(γ_L*ψ))` (integration by parts in `∂_j` over the period cell
without boundary terms, periodic integrand).  The cell `centeredBox d L` is a period cell (translation invariance of the
periodic integral).  Integrability fields: `F` bounded, `ψ`, `Aψ` bounded with compact support / box. -/
theorem per_weak_form (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (T : ℝ) (L : ℝ) (γ : Euc d → ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (μ : ℝ → Euc d → ℝ) (V : Euc d → ℝ) (b : ℝ → Euc d → Euc d)
    (hP : PerSmooth s T L γ M ν μ V b) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) (F : ℝ → Euc d → ℝ)
    (hF : IsPerSol 2 L γ M ν μ b (fun _ _ => 0) t F) :
    IsWeakSol (weakOpPer L γ M ν μ b) t (F 0) F := by
  sorry

/-- **L2** (size L, RISK).  Convergence of the test-function operators.  For `ψ ∈ C_c^∞` and a periodic approximating family
(`PerApprox`, with the data of `AdjointRdData` at level `m ≥ 1`), the periodic operators `weakOpPer` converge to the
Euclidean operator `weakOp (D.coeff μ) t` (coefficients at time `t - σ`) in the `ℓ¹(L²)` norm `cellL2Sum`, uniformly in
`σ ∈ [0,t]`; and `cellL2Sum (weakOpPer …) ≤ C_ψ` for ALL `L ≥ L₀`.  Local terms: uniform convergence of the drift and of the
density jets on compacts (`PerApprox`), the support of `ψ` being compact.  Nonlocal term: with `h_L := γ_L * ψ`,
`kernel_local_decomposition` gives `∇h_L = ∇g * ψ + O(L^{-s-1})`-type corrections on the support of `μ`'s significant
part, and for `x` in the box `|∇h_L(x)| + |∇²h_L(x)| ≤ C_ψ⟨x⟩^{-s-1}` uniformly in `L` (`kernel_cube_bound` on the
cells away from `supp ψ`, the near-singularity part is the Euclidean one); `μ_L` decays as `⟨x⟩^{-(d+3)}` on the box (nearest
lattice point is 0, see the plan) so the box tail beyond radius `R_0` has `cellL2Sum ≤ C R_0^{-1}` (summable since the
weights are `⟨cellPt⟩^{-(d+3)-(s+1)}` against `ℓ¹`).  Outside the box the Euclidean term is the same tail bound. -/
theorem weak_operator_converges (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (MB Λ ΛV G₀ νbar T : ℝ) (D : WholeDyn d) (μ : ℝ → Euc d → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) (Λ' ΛV' Cb L₀ : ℝ) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T)
    (γ : ℝ → Euc d → ℝ) (μL : ℝ → ℝ → ℝ → Euc d → ℝ) (VL : ℝ → ℝ → Euc d → ℝ)
    (hA : PerApprox s m MB Λ' ΛV' νbar Cb T D μ γ t L₀ μL VL) (ψ : Euc d → ℝ) (hψ : IsCcInfty ψ) :
    (∃ K : ℝ, ∀ L : ℝ, max 1 L₀ ≤ L → ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) 1 → ∀ σ ∈ Icc (0 : ℝ) t,
      cellL2Sum (weakOpPer L (γ L) D.M D.invβ (μL L ε)
        (fun τ => HRS.Whole.AppendixALemmas.torusDriftL D.M L (γ L) (μL L ε τ) (VL L ε)) σ ψ) ≤ ENNReal.ofReal K) ∧
    ∀ δ : ℝ, 0 < δ → ∃ L₁ ε₀ : ℝ, 0 < ε₀ ∧ ∀ L : ℝ, L₁ ≤ L → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ σ ∈ Icc (0 : ℝ) t,
      cellL2Sum (fun x => weakOpPer L (γ L) D.M D.invβ (μL L ε)
        (fun τ => HRS.Whole.AppendixALemmas.torusDriftL D.M L (γ L) (μL L ε τ) (VL L ε)) σ ψ x -
          weakOp (D.coeff μ) t σ ψ x) ≤ ENNReal.ofReal δ := by
  sorry

/-- **L3** (size L, abstract functional analysis).  Weak compactness in time and space: a sequence `F_n(τ)`, `τ ∈ [0,t]`, bounded
in `L²_uloc` uniformly in `n, τ`, with weak-in-space time-equicontinuity against every `ψ ∈ C_c^∞`, has a subsequence and a
limit `G` with `∫F_{n_k}(τ)ψ → ∫G(τ)ψ` for ALL `τ ∈ [0,t]` and `ψ ∈ C_c^∞`.  Route: separability of `L²_loc` (a countable family
`ψ_k` of test functions dense in `ℓ¹(L²)`-type duals), Banach-Alaoglu/diagonal subsequence at rational times, Arzelà-Ascoli
(equicontinuity) to pass to all `τ`; `G(τ)` is the Riesz representative of the limit functional, which is bounded on the
dual of `ℓ¹(L²)` by `B` (so `G(τ) ∈ L²_uloc`, bound by `norm_lsc` with `m = 0`).  Measurability in space of `G(τ)` is part of
the output; measurability in `τ` is not needed (the weak form uses only `σ ↦ ∫G(σ)Aσψ`, a uniform limit of continuous functions). -/
theorem weak_limit_exists (hd : 1 ≤ d) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (B t : ℝ) (ht : 0 < t)
    (Fn : ℕ → ℝ → Euc d → ℝ) (hB : ∀ n, ∀ τ ∈ Icc (0 : ℝ) t, ulocNormE 0 χ (Fn n τ) ≤ ENNReal.ofReal B)
    (hequi : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∃ K : ℝ, ∀ n, ∀ τ ∈ Icc (0 : ℝ) t, ∀ τ' ∈ Icc (0 : ℝ) t,
      |(∫ x, Fn n τ x * ψ x) - ∫ x, Fn n τ' x * ψ x| ≤ K * |τ - τ'|) :
    ∃ (n : ℕ → ℕ) (G : ℝ → Euc d → ℝ), StrictMono n ∧
      (∀ τ ∈ Icc (0 : ℝ) t, AEStronglyMeasurable (G τ) volume ∧ ulocNormE 0 χ (G τ) ≤ ENNReal.ofReal B) ∧
      ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ τ ∈ Icc (0 : ℝ) t,
        Tendsto (fun k => ∫ x, Fn (n k) τ x * ψ x) atTop (𝓝 (∫ x, G τ x * ψ x)) := by
  sorry

/-- **L4** (size M/L).  Passage to the limit in the weak form: if the periodic solutions `F_n` satisfy the weak forms
`IsWeakSol (A_n) t (φ_n) F_n` with `ulocNormE 0 χ (F_n τ) ≤ B`, `∫F_n(τ)ψ → ∫G(τ)ψ`, `∫φ_nψ → ∫φψ` and the operators
converge, `cellL2Sum (A_n σ ψ - A σ ψ) → 0` uniformly in `σ`, then `G` satisfies `IsWeakSol A t φ G` (the Euclidean `A = weakOp (D.coeff μ) t`), provided
`σ ↦ ∫G(σ)Aσψ` is integrable.  Route: `∫F_n(σ)A_nσψ - ∫G(σ)Aσψ = ∫F_n(σ)(A_n - A)ψ + ∫(F_n - G)(σ)Aσψ`; the first is
`≤ B·cellL2Sum(…) → 0` uniformly; the second tends to 0 pointwise in `σ` (`Aσψ ∈ ℓ¹(L²)` by `weak_operator_converges` and
`weakOp` decay) and is bounded by `2B·cellL2Sum(Aσψ)`: dominated convergence in `σ`.  The measurability of `σ ↦ ∫G(σ)Aσψ` is
the pointwise limit of the measurable (continuous) functions `σ ↦ ∫F_n(σ)A_nσψ`. -/
theorem weak_limit_is_weak_solution (hd : 1 ≤ d) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (B t : ℝ) (ht : 0 < t)
    (A : ℝ → (Euc d → ℝ) → (Euc d → ℝ)) (An : ℕ → ℝ → (Euc d → ℝ) → (Euc d → ℝ))
    (Fn : ℕ → ℝ → Euc d → ℝ) (φn : ℕ → Euc d → ℝ) (G : ℝ → Euc d → ℝ) (φ : Euc d → ℝ)
    (hweak : ∀ n, IsWeakSol (An n) t (φn n) (Fn n))
    (hB : ∀ n, ∀ τ ∈ Icc (0 : ℝ) t, ulocNormE 0 χ (Fn n τ) ≤ ENNReal.ofReal B)
    (hGB : ∀ τ ∈ Icc (0 : ℝ) t, ulocNormE 0 χ (G τ) ≤ ENNReal.ofReal B)
    (hF : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ τ ∈ Icc (0 : ℝ) t,
      Tendsto (fun n => ∫ x, Fn n τ x * ψ x) atTop (𝓝 (∫ x, G τ x * ψ x)))
    (hφ : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → Tendsto (fun n => ∫ x, φn n x * ψ x) atTop (𝓝 (∫ x, φ x * ψ x)))
    (hop : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ σ ∈ Icc (0 : ℝ) t,
      cellL2Sum (fun x => An n σ ψ x - A σ ψ x) ≤ ENNReal.ofReal δ)
    (hopb : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∃ K : ℝ, ∀ σ ∈ Icc (0 : ℝ) t, cellL2Sum (A σ ψ) ≤ ENNReal.ofReal K) :
    IsWeakSol A t φ G := by
  sorry

/-- **L5** (size M).  From the abstract weak form to `IsForwardSolutionRd`: if `G` satisfies `IsWeakSol (weakOp C t) t φ G`
with `ulocNormE 0 χ (G τ) ≤ B` (all `τ`), under `AdjointRdData`, then `IsForwardSolutionRd C t φ G`: the four pairings are
separately integrable and `forwardWeakTerm` equals `∫ G (weakOp ψ)`.  Route: `ψ`, `Δψ`, `div(b^{t-σ}ψ)` have compact support
and are bounded (`b` is `C^1`, C1a); `nonlocalTestRd C τ' ψ` is bounded by `C_ψ⟨y⟩^{-(d+3)-(s+1)}` (decay of `μ` and
its jets, `|∇^k(g*ψ)(y)| ≲ ⟨y⟩^{-s-1-k}` for `ψ ∈ C_c^∞`, `k ≤ 2`, from the cancellation convention; Fubini bookkeeping),
whose `cellL2Sum` is finite, hence the products with a `L²_uloc`-bounded `G` are integrable (`|∫Gg| ≤ B·cellL2Sum g`
and the same with `|g|`); the splitting `∫G(Aψ) = ν∫GΔψ - ∫G div(bψ) - ∫G·nonlocalTestRd` is then linearity of the
integral; `integrable_σ` is the `IsWeakSol` field with the same function. -/
theorem weak_to_forward (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (MB Λ ΛV G₀ νbar T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (D : WholeDyn d) (μ : ℝ → Euc d → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) (φ : Euc d → ℝ)
    (G : ℝ → Euc d → ℝ) (B : ℝ) (hGB : ∀ τ ∈ Icc (0 : ℝ) t, ulocNormE 0 χ (G τ) ≤ ENNReal.ofReal B)
    (hw : IsWeakSol (weakOp (D.coeff μ) t) t φ G) : IsForwardSolutionRd (D.coeff μ) t φ G := by
  sorry

/-- **L6** (size L, RISK).  Continuity in time into `H^{m'}_loc`, `m' < m`.  If `G` solves `IsForwardSolutionRd` with
`sup_τ ‖G(τ)‖_{H^m_uloc} ≤ B` (`m ≥ 1`) then for every real `m' < m`, centre `z`, `τ₀` and `ε` the continuity clause of
`IsUlocSolutionRd` holds.  Route: (i) the time-Lipschitz estimate in a negative Sobolev space: for `ψ ∈ C_c^∞`
`|∫(G(τ)-G(τ'))ψ| = |∫_{τ'}^τ ∫G Aσψ| ≤ B·K_ψ|τ-τ'|`, where `K_ψ` is controlled by the `H^{2}`-type
(`C^2`-jets, support) norm of `ψ` through the bounds of C1a and L5, giving
`‖χ_z(G(τ)-G(τ'))‖_{H^{-r}} ≤ C(r,z,B)|τ-τ'|` for a fixed `r` (duality `H^{-r} = (H^r)^*`, `C_c^∞` dense; the product
`χ_zG` has the same time-regularity since multiplication by `χ_z` costs a lower-order term controlled by `‖G‖_{H^m_uloc}`);
(ii) interpolation `‖u‖_{H^{m'}} ≤ ‖u‖_{H^{-r}}^{λ}‖u‖_{H^m}^{1-λ}` (Hölder on the Fourier side,
`λ = (m-m')/(m+r)`), which needs the bound `‖χ_zG(τ)‖_{H^m} ≤ C B` (definition of `ulocNormE` with the cutoff `χ_z`). -/
theorem weak_solution_cont (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (MB Λ ΛV G₀ νbar T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (D : WholeDyn d) (μ : ℝ → Euc d → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) (φ : Euc d → ℝ)
    (G : ℝ → Euc d → ℝ) (hG : IsForwardSolutionRd (D.coeff μ) t φ G) (B : ℝ)
    (hB : ∀ τ ∈ Icc (0 : ℝ) t, ulocNormE m χ (G τ) ≤ ENNReal.ofReal B) :
    ∀ m' : ℝ, m' < m → ∀ z : Euc d, ∀ τ₀ ∈ Icc (0 : ℝ) t, ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ τ ∈ Icc (0 : ℝ) t, |τ - τ₀| < δ →
        sobolevNormE m' (fun x => χ (x - z) * (G τ x - G τ₀ x)) ≤ ENNReal.ofReal ε := by
  sorry

/-- **L7** (size M).  Sobolev-space limit for (c): let `F_n(τ)` be smooth with `∫F_nψ → ∫Gψ` for all `ψ ∈ C_c^∞` and, for
every `R ≥ 1` and `η > 0`, eventually `jetSq m w_R (F_n) ≤ A + η` (`w_R = ⟨·/R⟩^{-(d+3)}`; `A` independent of `R`).  Then
`G ∈ H^m` and `‖G‖²_{H^m} ≤ A` (constant exactly `1` survives: weights `w_R ↑ 1`).  Route: for `ψ ∈ C_c^∞` with support
in `B(0,ρ)` and `R ≥ R(ρ,η)` with `w_R ≥ 1-η` on `B(0,ρ)`: `∫F_nψ = ⟨F_n, ψ⟩` pairing written through the exact jet
identity `N2` (`⟨u, (1-Δ/4π²)^m ϑ⟩`), Cauchy-Schwarz in the weighted jets, and the dual characterization
`‖G‖_{H^m} = sup{∫Gψ : ψ ∈ C_c^∞, ‖ψ‖_{H^{-m}} ≤ 1}` (density of `C_c^∞` in `H^{-m}`).  A cleaner variant of the same
argument: the functional `ψ ↦ ∫Gψ` on `C_c^∞` extends to `H^{-m}` with norm `≤ sqrt(A)(1-η)^{-1/2}` for every `η`. -/
theorem sobolev_norm_limit (hd : 1 ≤ d) (m : ℕ) (Fn : ℕ → Euc d → ℝ) (hsm : ∀ n, ContDiff ℝ ∞ (Fn n))
    (hb : ∀ n, BddJets m (Fn n)) (G : Euc d → ℝ) (A : ℝ)
    (hconv : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → Tendsto (fun n => ∫ x, Fn n x * ψ x) atTop (𝓝 (∫ x, G x * ψ x)))
    (hbd : ∀ R η : ℝ, 1 ≤ R → 0 < η → ∀ᶠ n in atTop,
      jetSq m (fun x => jbracket (R⁻¹ • x) ^ (-((d : ℝ) + 3))) (Fn n) ≤ A + η) :
    HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) G ∧ HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ) G ≤ A := by
  sorry

/-- **L8** (size S/M).  Weak continuity in `H^m`: if `G(τ) ∈ H^m` for `τ ∈ [0,t]`, `sup_τ‖G(τ)‖_{H^m} ≤ B`, and
`τ ↦ ∫G(τ)ψ` is continuous for each `ψ ∈ C_c^∞`, then `τ ↦ ⟨G(τ),h⟩_{H^m}` is continuous for every `h ∈ H^m`.  Route: for
`h = (1-Δ/4π²)^{-m}ψ`-type elements (`ψ ∈ C_c^∞`; `⟨G,h⟩_{H^m} = ∫Gψ`, up to the Fourier normalisation of
`sobolevInnerRd`) continuity is the hypothesis; the set of such `h` is dense in `H^m` (`C_c^∞` dense in `H^{-m}`); uniform
`3ε`-argument with the bound `B`. -/
theorem sobolev_weak_continuity (hd : 1 ≤ d) (m : ℕ) (t B : ℝ) (G : ℝ → Euc d → ℝ)
    (hG : ∀ τ ∈ Icc (0 : ℝ) t, HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) (G τ) ∧
      Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ) (G τ)) ≤ B)
    (hcont : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ContinuousOn (fun τ => ∫ x, G τ x * ψ x) (Icc (0 : ℝ) t)) :
    ∀ h : Euc d → ℝ, HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) h →
      ContinuousOn (fun τ => sobolevInnerRd m (G τ) h) (Icc (0 : ℝ) t) := by
  sorry

/-- **L9** (size M).  Weak continuity in time of the weak limit against `C_c^∞` (the hypothesis of L8): a solution of
`IsForwardSolutionRd` has `τ ↦ ∫G(τ)ψ` continuous (indeed Lipschitz), directly from the `eq` field: `∫Gψ(τ) = ∫φψ + ∫_0^τ ⟨…⟩`
and the integrability of `forwardWeakTerm` (`integrable_σ`: the primitive of an `L^1` function is continuous). -/
theorem forward_weak_continuity (C : WholeCoeff d) (t : ℝ) (φ : Euc d → ℝ) (G : ℝ → Euc d → ℝ)
    (hG : IsForwardSolutionRd C t φ G) (ψ : Euc d → ℝ) (hψ : IsCcInfty ψ) :
    ContinuousOn (fun τ => ∫ x, G τ x * ψ x) (Icc (0 : ℝ) t) := by
  sorry

/-! ### Group A: the classical statement (a) -/

/-- **A1a** (size L).  A classical adjoint solution is a forward weak solution: if `IsClassicalAdjointW C t φ f` (repaired
linear-growth notion), with `C = D.coeff μ` and data `AdjointRdData` of level `≥ 1`, then
`F(τ) = f(t - τ)` satisfies `IsForwardSolutionRd C t φ F`.  Route: (i) time: for `ψ ∈ C_c^∞` the function
`r ↦ ∫f(r)ψ` is continuous on `[0,t]` and has derivative `-∫𝓛_rf ψ` on `(0,t)` (`time_deriv` + differentiation under the
integral, the derivative is dominated by `B(1+|x|)|ψ|`, `bdd_time_deriv`, `cont_time_deriv`); so the fundamental theorem of
calculus on `(0,t)` with continuity at the end points gives the integrated form; (ii) space: integration by parts
`∫ψ(νΔf + b·∇f) = ∫f(νΔψ - div(bψ))` (`f ∈ C^2` bounded jets, `b ∈ C^1`, `ψ` compactly supported); (iii) the nonlocal
term: A1c (`nonlocal_bridge`); (iv) integrability fields: `f` bounded, test operators in `ℓ¹(L²)`
(see L5). -/
theorem classical_forward_weak (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (MB Λ ΛV G₀ νbar T : ℝ) (D : WholeDyn d) (μ : ℝ → Euc d → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) (φ : Euc d → ℝ)
    (f : ℝ → Euc d → ℝ) (hf : IsClassicalAdjointW (D.coeff μ) t φ f) :
    IsForwardSolutionRd (D.coeff μ) t φ (fun τ => f (t - τ)) := by
  sorry

/-- **A1b** (size S/M).  A classical adjoint solution is in `L^∞([0,t]; H^1_uloc)`: bounded jets of order `≤ 2`
(`IsClassicalAdjointW.bdd`) give `ulocNormE 1 χ (f r) ≤ C_χ(sup|f| + sup|∇f|)`, uniform in `r`.  Route: for a real centre `z`
the function `χ(·-z)f(r)` is `C^2` with compact support so `sobolev_jet_eq` (`m = 1`) gives `‖·‖_{H^1}² = ‖·‖²_{L²} + ‖∇·‖²_{L²}`,
bounded by `(|supp χ| )(‖χ‖_{C^1}²·(‖f‖_∞ + ‖∇f‖_∞)²)`; sup over `z`. -/
theorem classical_uloc_bounded (hd : 1 ≤ d) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (C : WholeCoeff d) (t : ℝ) (φ : Euc d → ℝ)
    (f : ℝ → Euc d → ℝ) (hf : IsClassicalAdjointW C t φ f) :
    ∃ B : ℝ, ∀ r ∈ Icc (0 : ℝ) t, ulocNormE 1 χ (f r) ≤ ENNReal.ofReal B := by
  sorry

/-- **A1c** (size M, the cancellation-convention Fubini bridge).  For `u ∈ C^1` with bounded `u, ∇u`, a density `ρ` with
`IsRegularDensityW` (bounded, decaying like `⟨y⟩^{-(d+3)}` with Lipschitz bound), and `ψ ∈ C_c^∞`: the principal-value-free
convolution of `generatorW` (with the cancellation subtraction `ρ(x)` inside `|x-y| ≤ 1/4`) integrates against `ψ` to the
transposed form,
`∫ψ(x)·∑_j (convGradConvW (rieszKernelGrad d s) (ρ M^T∇u)_j)(x)_j dx = ∫u(x)·nonlocalTestRd C τ' ψ x dx`.
Route: Fubini on the region `|x-y|>1/4` (absolutely convergent: `|∇g| ≤ C|·|^{-s-1}` and decay of `ρ`, bounded `∇u`, compactly
supported `ψ`); on `|x-y| ≤ 1/4` the subtraction `ρ(x)` integrates to `0` against the odd kernel `∇g` (`∇g(-u) = -∇g(u)` over the
symmetric ball) — so write it as a truncated integral `lim_{δ→0}∫_{|x-y|>δ}`, Fubini at fixed `δ`, then `∂_ig` is odd to move it
onto `ψ` giving `-∂_i(g*ψ)(y)` (derivative of `g*ψ` commutes with the locally integrable `g`), then integrate by parts in `∂_j` on `u`
(`ρ ∂_i(g*ψ)` is `C^1` and decays). -/
theorem nonlocal_bridge (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (C : WholeCoeff d) (hCs : C.s = s)
    (τ' : ℝ) (Λ : ℝ) (hρ : IsRegularDensityW 1 Λ (C.ρ τ')) (u : Euc d → ℝ) (hu : ContDiff ℝ 1 u)
    (hub : ∃ B : ℝ, ∀ x, |u x| ≤ B ∧ ‖gradient u x‖ ≤ B) (ψ : Euc d → ℝ) (hψ : IsCcInfty ψ) :
    ∫ x, ψ x * ∑ j : Fin d, (convGradConvW (rieszKernelGrad d s)
      (fun y => C.ρ τ' y * (Torus.matVec C.M.transpose (gradient u y)) j) x) j =
      ∫ x, u x * nonlocalTestRd C τ' ψ x := by
  sorry

/-- **A1d** (size M).  Uniqueness of the weak solutions bounded in `H^1_uloc` (version of **U2** that needs neither the
`C([0,t];H^{m'}_loc)` clause nor level `m`): two functions `F₁, F₂` with `IsForwardSolutionRd (D.coeff μ) t φ F_a` and
`ulocNormE 1 χ (F_a τ) ≤ B` for all `τ` agree a.e. at each `τ`.  Same proof as `uniqueness_rd` (it IS that proof after
`IsUlBounded` has been established), from `HRS.Whole.AppendixALemmas.uloc_uniqueness` with `m = 1`, applied with data of level
`1` (`data_mono`).  Used for classical uniqueness, hence for `propagatorW = f` in (a). -/
theorem uniqueness_rd_level1 (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (Rg : PDE.Regime) (MB Λ ΛV G₀ νbar T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ)
    (D : WholeDyn d) (ν₀ : ℝ) (μ : ℝ → Euc d → ℝ) (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ)
    (hR : RdRegimeHolds Rg d s D.M D.invβ ν₀) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) (φ : Euc d → ℝ)
    (F₁ F₂ : ℝ → Euc d → ℝ) (h₁ : IsForwardSolutionRd (D.coeff μ) t φ F₁) (h₂ : IsForwardSolutionRd (D.coeff μ) t φ F₂)
    (B : ℝ) (hB₁ : ∀ τ ∈ Icc (0 : ℝ) t, ulocNormE 1 χ (F₁ τ) ≤ ENNReal.ofReal B)
    (hB₂ : ∀ τ ∈ Icc (0 : ℝ) t, ulocNormE 1 χ (F₂ τ) ≤ ENNReal.ofReal B) :
    ∀ τ ∈ Icc (0 : ℝ) t, F₁ τ =ᵐ[volume] F₂ τ := by
  sorry

/-- **A2a** (size L, RISK).  Regularity of the uloc solution for `m ≥ m_* = ⌊d/2⌋+3`: there is a representative
`F̃(τ) = F(τ)` a.e. that is `C^2`, with `‖∇^jF̃(τ)‖_∞ ≤ C_emb‖F(τ)‖_{H^m_uloc}`, `j ≤ 2`, and jointly continuous jets of order `≤ 2`
in `(τ,x)` on `[0,t] × ℝ^d`.  Route: the Sobolev embedding `H^{m'}_loc ⊂ C^2` for `m' = m - 1/4 > 2 + d/2` (for `m ≥ ⌊d/2⌋+3`:
`m - 1/4 ≥ ⌊d/2⌋ + 11/4 > d/2 + 2`), applied to `χ_zF(τ)` with the uniform constant (the repository has the torus form
`HRS.PDE.ClassicalPart.continuous_iteratedFDeriv_toFun`, WellPosed.lean; the Euclidean form with arbitrary compact support is
not verified by grep); joint continuity in `τ` from the `C([0,t];H^{m'}_loc)` clause of `IsUlocSolutionRd` and the uniform
embedding constant (continuity into `C^2_b(B(z,1))`); the a.e.-representative at each fixed `τ` is the continuous one. -/
theorem solution_regularity (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : mStar d ≤ m)
    (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (C : WholeCoeff d) (t : ℝ) (ht : 0 < t) (φ : Euc d → ℝ)
    (F : ℝ → Euc d → ℝ) (hF : IsUlocSolutionRd χ m C t φ F) :
    ∃ F' : ℝ → Euc d → ℝ, (∀ τ ∈ Icc (0 : ℝ) t, F' τ =ᵐ[volume] F τ) ∧
      (∀ τ ∈ Icc (0 : ℝ) t, ContDiff ℝ 2 (F' τ)) ∧
      (∃ B : ℝ, ∀ j ≤ 2, ∀ τ ∈ Icc (0 : ℝ) t, ∀ x, ‖iteratedFDeriv ℝ j (F' τ) x‖ ≤ B) ∧
      (∀ j ≤ 2, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ j (F' p.1) p.2) (Icc (0 : ℝ) t ×ˢ univ)) := by
  sorry

/-- **A2b** (size L, RISK).  The classical equation for the regular representative: with `F'` of `solution_regularity` and
`m ≥ m_*`, the function `f(r) = F'(t - r)` satisfies `IsClassicalAdjointW (D.coeff μ) t φ f` provided `φ ∈ C^2` (`f(t) = F'(0) = φ`
since `F'(0) = φ` a.e. and both are continuous).  Route: the weak form with `ψ ∈ C_c^∞` and the regularity: by
`nonlocal_bridge` and integration by parts, `∫F'(τ)ψ = ∫φψ + ∫_0^τ∫𝓛̃F'(σ)ψ dσ`, `𝓛̃ = νΔ + b·∇ - 𝒢` the classical operator
(`generatorW`, reversed time), whose output is jointly continuous in `(σ,x)` (bounded `C^2` jets, `b` jointly continuous
by C1b, the nonlocal term is jointly continuous by dominated convergence with the cancellation form: `ρ` is Lipschitz in
`x` and the kernel is integrable); so `∫F'(τ)ψ - ∫φψ` is `C^1` in `τ` for every `ψ`, and the pointwise-in-`x` statement
follows (a continuous function whose integral against every `ψ ∈ C_c^∞` is the `τ`-integral of a continuous function is
that time-integral, so `τ ↦ F'(τ,x)` is `C^1`); bounds: `|∂_rf| ≤ |𝓛f| ≤ B(1+|x|)` using `|b| ≤ Cb(1+|x|)` (C1a), bounded jets,
and a bounded nonlocal term (`cancellation convention`, `‖ρ‖_{C^1}`, `‖∇u‖_∞`). -/
theorem solution_classical (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : mStar d ≤ m)
    (MB Λ ΛV G₀ νbar T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (D : WholeDyn d) (μ : ℝ → Euc d → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) (φ : Euc d → ℝ)
    (hφ : ContDiff ℝ 2 φ) (F : ℝ → Euc d → ℝ) (hF : IsUlocSolutionRd χ m (D.coeff μ) t φ F) :
    ∃ f : ℝ → Euc d → ℝ, IsClassicalAdjointW (D.coeff μ) t φ f ∧ ∀ r ∈ Icc (0 : ℝ) t, f r =ᵐ[volume] F (t - r) := by
  sorry

/-- **A3** (size M).  The propagator is the classical solution and its `C_b^2` norm is controlled by the `H^{m_*}_uloc` bound:
if `IsClassicalAdjointW C t φ f`, any two classical solutions coincide (A1d + continuity), so `propagatorW C r t φ = f r`
(`propagatorW` is defined by `Classical.choose`); and `cbNorm 2 (f r) ≤ C_emb ·(sup jets)` where the jets are bounded by the
embedding constant times `ulocNormE (mStar d) χ (F (t-r))` (`solution_regularity`) and `ulocNormE ≤ C e^{Λτ}‖φ‖` (existence part of
`adjoint_rd`).  The `C_b^2` norm is the sum convention `cbNorm`. -/
theorem propagator_eq_classical (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (Rg : PDE.Regime) (MB Λ ΛV G₀ νbar T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (D : WholeDyn d) (ν₀ : ℝ)
    (μ : ℝ → Euc d → ℝ) (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) (hR : RdRegimeHolds Rg d s D.M D.invβ ν₀)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ)
    (hf : IsClassicalAdjointW (D.coeff μ) t φ f) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) t) :
    propagatorW (D.coeff μ) r t φ = f r := by
  sorry

/-- **A4** (size M).  The `C_b^2` bound: for `m ≥ m_*` and `F` with `ulocNormE (mStar d) χ (F τ) ≤ K` for a representative
`F'` as in `solution_regularity`, `MemCb 2 (F' τ)` and `cbNorm 2 (F' τ) ≤ C_emb · K` (uniform embedding
`H^{m_*}_uloc ⊂ C_b^2`, `m_* > d/2 + 2`).  Route: the same Sobolev embedding as A2a with the quantitative constant. -/
theorem cb2_of_uloc (hd : 1 ≤ d) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ Cemb : ℝ, 0 < Cemb ∧ ∀ (u : Euc d → ℝ), ContDiff ℝ 2 u → ulocNormE (mStar d) χ u < ⊤ →
      MemCb 2 u ∧ cbNorm 2 u ≤ Cemb * (ulocNormE (mStar d) χ u).toReal := by
  sorry

/-! ### The six final assemblies

Each `*_proof` has exactly the type of the frozen declaration (`type_of%`), so that on the day the packets are proved the
frozen `sorry` can be replaced by `exact HRS.MH.AdjointRd.*_proof` (or the statement moved).  The order of quantifiers is not
changed.  Outline of each; the dependency graph is in the plan, section 4. -/

/-- Assembly of `adjoint_rd` (existence, uniqueness, bound).  Constants: `Cb` from `reversed_data` (C1c); `(Λ', ΛV', Cb', L₀)` from
`per_coefficients`; `C₁` from `per_uloc_bound` (E4) at the primed constants; `C₂` from `per_initial_data` (T2b); the final `C` is
`max(C₁C₂, …)` and the monotonicity `lambdaM_mono` merges the constant of `Λ_m`.  Existence: for `φ` choose `φL L ε` (T2b), solve with
`per_smooth_solution_exists` (T1b, after `torus_jet_regularity` T1a), bound by E4, apply `weak_limit_exists` (L3) along
`L_n → ∞, ε_n → 0`, then `per_weak_form` (L1) + `weak_operator_converges` (L2) + `weak_limit_is_weak_solution` (L4) +
`weak_to_forward` (L5) to get `IsForwardSolutionRd`, `norm_lsc` (N3) for the bound, `weak_solution_cont` (L6) for the continuity
clause, `norm_lsc` again for the `Ce^{Λτ}‖φ‖` bound.  Uniqueness: `uniqueness_rd` (U2) (this needs S.A.33 `uloc_uniqueness`). -/
theorem adjoint_rd_proof : type_of% @HRS.Whole.AppendixA.adjoint_rd := by
  sorry

/-- Assembly of `adjoint_rd_classical`.  Constant `C` from `adjoint_rd` at level `m_* = mStar d` (hence `Λ_{m_*}`), with `data_mono`
(C2) to pass from level `m ≥ m_*` data to level `m_*`; for the given `F` (any `IsUlocSolutionRd` at level `m`, in particular at
level `m_*`: `ulocNormE m_* ≤ ulocNormE m` by `norm_calculus`, same `φ`) use `solution_classical` (A2b) for `f`, then
`propagator_eq_classical` (A3) and `cb2_of_uloc` (A4) with the bound `ulocNormE (mStar d) χ (F (t-r)) ≤ C e^{Λ_{m_*}(t-r)} ‖φ‖`
from the existence clause of `adjoint_rd` and its uniqueness clause (U2) identifying `F` with the constructed solution. -/
theorem adjoint_rd_classical_proof : type_of% @HRS.Whole.AppendixA.adjoint_rd_classical := by
  sorry

/-- Assembly of `adjoint_rd_planewave`.  Reduction to `adjoint_rd`'s bound: `ulocNormE m χ (cos(2πk·))` and `ulocNormE m χ (sin(2πk·))`
are `≤ C_χ(1+‖k‖)^m` (`∂^α cos(2πk·x) = (2π)^{|α|}k^α·(±cos or sin)`, bounded by `(2π‖k‖)^{|α|}`, times the cutoff norm; `norm_calculus`
and `sobolev_jet_eq` N2 for `χ(·-z)·plane wave`: `‖χ(·-z)e_k‖_{H^m} ≤ C_χ(1+|k|)^m`), apply the `adjoint_rd` bound
(`adjoint_rd_proof` existence part plus uniqueness (U2) to identify the arbitrary `F`).  Packet: `planewave_uloc_bound` below. -/
theorem adjoint_rd_planewave_proof : type_of% @HRS.Whole.AppendixA.adjoint_rd_planewave := by
  sorry

/-- Assembly of `adjoint_rd_sobolev` (c).  `hs : d < 2(s+1)`.  Existence/uniqueness/regularity from `adjoint_rd`; the global
bound with constant `1`: `per_globalweight_bound` (E7) for the periodic approximants with datum `φL` of `per_initial_data` (last
clause, `jetSq m w_R φL ≤ ‖φ‖²_{H^m} + η`), the interaction term `C R^C L^{-κ}B²` is eliminated by `L → ∞` first and then `η → 0`; `sobolev_norm_limit`
(L7) gives `MemSobolev (m) (F τ)` and `sobolevNormSq (F τ) ≤ e^{2Λτ}‖φ‖²` (take square roots), `forward_weak_continuity` (L9) and
`sobolev_weak_continuity` (L8) the `C_w`.  Identification of `F` (given, arbitrary in the class) with the limit by U2. -/
theorem adjoint_rd_sobolev_proof : type_of% @HRS.Whole.AppendixA.adjoint_rd_sobolev := by
  sorry

/-- Assembly of `adjoint_rd_stability` (d).  Constants `C, C'` from `per_stability_bound` (E6) at level `m` (with `(Λ',ΛV',Cb)` of `per_coefficients_pair` T2c,
`C' ≥ C` after `lambdaM_mono`); the solutions `F_a` of the statement are the weak limits of the periodic solutions `F_a^{L,ε}` with datum `φL L ε`
(common datum!) — the common subsequence is extracted from `weak_limit_exists` for the pair, identified with the given `F_a` by U2 at level `m+2`; the bound
passes to the limit with `norm_lsc` (N3, `ulocNormE` and `varpiNormE` parts) applied to `F₁^{L,ε}(τ) - F₂^{L,ε}(τ)`, and the right side with
`ulocNormE (m+2) χ (φL L ε) ≤ C₂ ulocNormE (m+2) χ φ` (T2b) — NOTE: this puts the constant `C₂` into `C`. -/
theorem adjoint_rd_stability_proof : type_of% @HRS.Whole.AppendixA.adjoint_rd_stability := by
  sorry

/-- Assembly of `adjoint_rd_weighted` (e).  Existence and the periodic weighted bound `per_weighted_bound` (E5) for approximants with datum
`φL` of T2b (`varpiNormE m χ (φL L ε) ≤ C₂ varpiNormE m χ φ`); the limit with `norm_lsc` (third conjunct: `liminf` of `varpiNormE`); identification
of the given `F` by U2. -/
theorem adjoint_rd_weighted_proof : type_of% @HRS.Whole.AppendixA.adjoint_rd_weighted := by
  sorry

/-- **P1** (size S/M).  The plane-wave `H^m_uloc` norm: for `k ∈ ℝ^d` and `φ ∈ {cos(2π k·x), sin(2π k·x)}`,
`ulocNormE m χ φ ≤ C_{χ,m,d}(1+‖k‖)^m`.  Route: `sobolev_jet_eq` for the compactly supported `χ(·-z)φ`; by Leibniz the jet
`∂^α(χ(·-z)φ)` is a sum over `β ≤ α` of `∂^{α-β}χ_z ∂^βφ`, `|∂^βφ| ≤ (2π‖k‖)^{|β|}`; sum of squares gives `(1+‖k‖)^{2m}`
(the constant uses the bounded `C^m` norm of `χ` and `|supp χ|`). -/
theorem planewave_uloc_bound (hd : 1 ≤ d) (m : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : Euc d, ∀ φ : Euc d → ℝ,
      (φ = (fun x => Real.cos (2 * Real.pi * inner ℝ k x)) ∨ φ = (fun x => Real.sin (2 * Real.pi * inner ℝ k x))) →
      ulocNormE m χ φ ≤ ENNReal.ofReal (C * (1 + ‖k‖) ^ m) := by
  sorry

end HRS.MH.AdjointRd

