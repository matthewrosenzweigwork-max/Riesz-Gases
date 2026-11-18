import HRS.Main.GFSpec1

/-!
# Packet GF-SPEC, part 2: the stochastic inputs of the proof of Theorem 2.1

Sorried STATEMENTS of the sub-packets GF-PM (particle martingale), GF-PAIR (identification of the stochastic convolution),
GF-MILD (the mild identity at the level of `E_m`), GF-REM (remainder bound; pointwise commutator estimate and the
dual-norm passage), GF-TE (trace-norm covariance error; pointwise and in moment form), GF-TR-moment (transport moment).
See `HRS/Main/GFSpec1.lean` for the representation decisions and `HRS/Main/GFSpec7.lean` for how these are assembled.

TeX: M L2445-2478 (proof of Theorem 2.1), L2447-2455 (`U:eq:quantitative-mild`, `U:eq:quantitative-drift`),
L2285-2293 (`U:eq:particle-covariances`), L2266-2299 (Lemma 3.22), L2354-2361 (Lemma 3.23), L2457-2465 (transport variant).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS.Uniform

variable {d : ℕ}

/-! ### GF-PM: the `E_γ`-valued particle martingale -/

/-- The Itô integrand of the particle noise (NEW definition): for the label `k = (i,j) ∈ Fin N × Fin d` the vector
`(c/N) b_{X_r^i, j} ∈ E_γ`, `b_{x,j} = -∂_jδ_x` (`Uniform.bVec`), with `c = σ_N √(2β_N⁻¹)`.  Then
`⟨∫ Φ dW', φ⟩ = σ_N M_N[φ]`, `M_N[φ] = ∫ N⁻¹√(2β⁻¹) ∑ ∂_jφ(x_i) dW'^{ij}` (`HRS.empiricalMartingale`). -/
def noiseIntegrand {Ω : Type*} {N : ℕ} (γ c : ℝ) (X : ℝ → Ω → Config d N) :
    ℝ → Ω → (Fin N × Fin d) → NegSobolev d γ :=
  fun r ω k => (c / N) • bVec γ k.2 (X r ω k.1)

/-- The scalar `σ_N √(2β_N⁻¹)` of the noise (NEW definition). -/
def noiseScale (S : GeneralSetup d) (N : ℕ) : ℝ := sigN S N * Real.sqrt (2 * S.invβ N)

/-- **GF-PM** (TeX M L2285-2293, L2450-2452: "`M` is the `E_γ`-valued martingale of the particle noise, with covariation
`C_N^t = covForm γ q_N μ_N^t`").  SORRIED.  Estimated size: L.
`Lemmas 3.24/3.31 ASSUME` such a martingale; no construction of it exists in the repository.  Construction: the Hilbert
Itô integral over the countable index set `κ = Fin N × Fin d` (`IsHilbertItoIntegral`) of the bounded progressive
integrand `noiseIntegrand` (bounded: `‖b_{x,j}‖_{E_γ} ≤ C` for `γ > d/2 + 1`; progressive from `IsFilteredSolution.progressive`
and continuity of `x ↦ b_{x,j} ∈ E_γ`), and the identity `hsCovForm (noiseIntegrand r ω) = covForm γ q_N (empirical (X_r))`
(`q_N = σ_N²β_N⁻¹/N`, with the `β = ∞` convention `q = 0`, `c = 0`).  The covariation martingales follow from the Itô
isometry (`isHM_of_ito`-type lemma of `Prob/HilbertMartingale`).  The conclusion is on all times (the process `X` beyond
`T` is arbitrary but adapted/progressive, which is all that is used). -/
theorem gf_particle_martingale (S : GeneralSetup d) (N : ℕ) (hN : 1 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (X : ℝ≥0 → Ω → Config d N) (hF : IsFilteredSolution P ℱ W' W X) :
    ∃ Mart : ℝ → Ω → NegSobolev d (S.γ : ℝ),
      IsHilbertItoIntegral P ℱ W'
        (noiseIntegrand (S.γ : ℝ) (noiseScale S N) (fun r => X (Real.toNNReal r))) Mart ∧
      IsHilbertMartingaleWithCovariation P ℱ S.T Mart
        (fun r ω => covForm (S.γ : ℝ) (qN S N) (empirical (X (Real.toNNReal r) ω))) := by
  sorry

/-! ### GF-PAIR: identification of the stochastic convolution by pairing -/

/-- **GF-PAIR** (TeX M L2447-2451, `U:eq:quantitative-mild`: "`Z^t(φ) = σ M_N^t[U^{·,t}φ]`").  SORRIED.
Estimated size: L.
If `Z_t` is the stochastic convolution `∫_0^t V(t,r) j dM_r` of the particle martingale `M` (`IsStochConv`, the `L²`-limit of
left-endpoint Riemann sums) against the evolution `EV` of `GFEvo`, then for every smooth test `φ`, almost surely
`⟨Z_t, φ⟩ = σ_N · M_N^t[U^{·,t}φ]` (`HRS.empiricalMartingale` with the time-dependent test `r ↦ U^{r,t}φ`).
Proof: by `IsDualOn`, `⟨V(t,r_i) j(M_{r_{i+1}} - M_{r_i}), φ⟩ = ⟨M_{r_{i+1}} - M_{r_i}, U^{r_i,t}φ⟩`
(`U^{r,t}φ ∈ H^γ ⊂ C²`, so `⟨M_τ, f⟩ = ∫_0^τ ∑ N⁻¹σ√(2β⁻¹) ∂_jf(x_i)dW'` for time-independent `f ∈ H^γ`, by `approx`);
these are the Riemann sums of the stochastic Fubini identity for the `C¹([0,t]; H^γ)` deterministic integrand
`r ↦ U^{r,t}φ` (`∂_r U^{r,t}φ = -𝓛_r U^{r,t}φ`), whose `L²`-limit is `σ M_N^t[U^{·,t}φ]` (Itô isometry + continuity of
`r ↦ U^{r,t}φ` in `C¹`).  `Q54cAux5` ("Itô sums") is the deterministic half.

Repaired 2026-10-17, ISSUES GFB3: the hypothesis `hZm` (measurability of the pairing) was missing; without it the statement is false
(`IsStochConv` uses the lower integral). -/
theorem gf_pair_identification (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (N : ℕ) (m K : ℝ)
    (EV : EvolData (NegSobolev d (S.γ : ℝ)) (NegSobolev d m)) (hEV : GFEvo S M N m K EV)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (X : ℝ≥0 → Ω → Config d N) (hF : IsFilteredSolution P ℱ W' W X)
    (Mart : ℝ → Ω → NegSobolev d (S.γ : ℝ))
    (hMart : IsHilbertItoIntegral P ℱ W'
      (noiseIntegrand (S.γ : ℝ) (noiseScale S N) (fun r => X (Real.toNNReal r))) Mart)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) S.T) (Zt : Ω → NegSobolev d m)
    (hZ : IsStochConv P EV.VE EV.j Mart 0 t Zt) (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ)
    (hZm : AEMeasurable (fun ω => NegSobolev.eval (Zt ω) φ) P) :
    ∀ᵐ ω ∂P, NegSobolev.eval (Zt ω) φ = sigN S N *
      empiricalMartingale P ℱ W' (S.dynM M N) t
        (fun r => propagator (S.dynM M N) (S.ρ N) r t φ) X ((Real.toNNReal t : ℝ≥0) : ℝ) ω := by
  sorry

/-! ### GF-MILD: the scalar mild identity at the level of `E_m` -/

/-- **GF-MILD** (TeX M L2445-2451, `U:eq:quantitative-mild`; Lemma 3.7 `B:prop:duality-identity`).  SORRIED.
Estimated size: M.
For every `t ∈ [0,T]` and smooth `φ`, almost surely
`⟨Ξ^t, φ⟩ = ⟨V(t,0) j Ξ^0, φ⟩ + σ_N M_N^t[U^{·,t}φ] + σ_N ∫_0^t flucInteraction(U^{r,t}φ; X_r, ρ_r) dr`,
with `Ξ^t = flucProc m σ_N X ρ_N t` (level `m`) and `Ξ^0` at level `γ`.
Proof: `HRS.duality_identity_all` at `τ = t` with the classical adjoint solution `f_r = U^{r,t}φ` (`GFEvo.adjoint`),
hypotheses supplied by `nullContactOccupation_of_strong` and `IsStrongSolution.toContact`,
`hρ : IsMeanFieldSolution`, `hreg : IsRegularMF 3 Λ T ρ` by monotonicity of `C^k`,
`NegSobolev.eval_ofMeasureDiff_of_summable` for `⟨Ξ, ψ⟩ = σ(μ_N(ψ) - μ(ψ))` (`ψ ∈ H^γ ⊂ C^2` has summable Fourier
coefficients), `GFEvo.dual` and `GFEvo.j_eq` for `⟨V(t,0) j Ξ^0, φ⟩ = ⟨Ξ^0, U^{0,t}φ⟩`. -/
theorem gf_mild_identity (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (hMF : S.MFHypM M) (N : ℕ)
    (hN : 2 ≤ N) (m K : ℝ) (hm : (S.γ : ℝ) ≤ m)
    (EV : EvolData (NegSobolev d (S.γ : ℝ)) (NegSobolev d m)) (hEV : GFEvo S M N m K EV)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hX : IsStrongSolution P (S.dynM M N) S.T X₀ W X)
    (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsFilteredSolution P ℱ W' W X)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) S.T) (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ) :
    ∀ᵐ ω ∂P,
      NegSobolev.eval (flucProc m (sigN S N) X (S.ρ N) t ω) φ =
        NegSobolev.eval (EV.VE t 0 (EV.j (flucProc (S.γ : ℝ) (sigN S N) X (S.ρ N) 0 ω))) φ +
        sigN S N * empiricalMartingale P ℱ W' (S.dynM M N) t
          (fun r => propagator (S.dynM M N) (S.ρ N) r t φ) X ((Real.toNNReal t : ℝ≥0) : ℝ) ω +
        sigN S N * ∫ r in (0 : ℝ)..t,
          flucInteraction (S.dynM M N) (propagator (S.dynM M N) (S.ρ N) r t φ)
            (X (Real.toNNReal r) ω) (S.ρ N r) := by
  sorry

/-! ### Small analytic facts on the pairing `E_m × C^∞` (needed to combine the packets) -/

/-- **GF-SMOOTH** (technical).  SORRIED.  Estimated size: S-M.  A smooth test function is `C²` and lies in every `H^m`
(rapid decay of its Fourier coefficients), so the transported test `U^{r,t}φ` of the remainder estimates has the regularity
`GFEvo.adjoint` asks for. -/
theorem gf_smooth_mem {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (m : ℝ) :
    Torus.IsCk 2 φ ∧ MemSobolev m φ := by
  sorry

/-- **GF-EVAL** (technical).  SORRIED.  Estimated size: S.  The pairing `F ↦ ⟨F, φ⟩ = ∑' k, F̂(k) φ̂(k)` is additive in `F` for a
smooth test function (the series is absolutely summable by Cauchy–Schwarz, `abs_eval_le`). -/
theorem gf_eval_sub {m : ℝ} (F G : NegSobolev d m) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    NegSobolev.eval (F - G) φ = NegSobolev.eval F φ - NegSobolev.eval G φ := by
  sorry

/-- PROVED.  `σ_N ≥ 0`. -/
theorem sigN_nonneg (S : GeneralSetup d) (N : ℕ) : 0 ≤ sigN S N := by
  unfold sigN sigmaScale
  split_ifs
  · exact (S.hκ N).le
  · exact le_min (S.hκ N).le (Real.sqrt_nonneg _)

/-! ### GF-REM: the remainder -/

/-- **GF-REM-ptw** (pointwise commutator estimate for the remainder integrand; TeX M L2452-2455,
`U:eq:quantitative-drift`, and Proposition 3.32 L3294-3310).  SORRIED.  Estimated size: M-L.
For every level `m ≥ γ` (the constants do not depend on `m`: only `‖ψ‖_{H^γ} ≤ ‖ψ‖_{H^m}` is used) and the transported test `ψ = U^{r,t}φ` with `‖ψ‖_{H^m} ≤ K‖φ‖_{H^m}`, `|flucInteraction(ψ; X, ρ_r)| ≤ C ‖φ‖_{H^m}·𝓔_N(X, r)`
for every collision-free configuration, where `𝓔_N = F_N + o_N(C₀) = S.energyCompletion` and `C₀ ≥ C₀min`.
Proof: `flucInteraction = commQuantity d s v X ρ` with `v = Mᵀ∇ψ` (the off-diagonal convention of `interactionPairing`);
`HasTransportBound d s v K'` with `K' ≲ ‖ψ‖_{H^γ} ≤ ‖ψ‖_{H^m}` (Sobolev embedding `H^γ ⊂ C²` and
`|∇|^{(d+1)/2}∇ψ ∈ L^∞ ⊂ L^{2d/(d-1)}` on the unit torus, `γ > 2d+10`); `HRS.Commutator.commutator_estimate_of_packets`
with `Λ' = max Λ 1` (`‖ρ‖_∞ ≤ cbNorm 0 ≤ Λ`); then `oNΛ d s C₀* Λ' N ≤ oN d s C₀ N` for `C₀ ≥ C₀min(d,s,Λ)`
(`oNΛ_le_oN`, `oNΛ_mono`).  This is where the C₀ bookkeeping of ISSUES "SPEC-C0" is used (it is `D1` of `GFAux1`). -/
theorem gf_remainder_pointwise (b : GeneralBounds d) (M : Matrix (Fin d) (Fin d) ℝ) (K : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHypM M → ∀ N : ℕ, 2 ≤ N →
      ∀ m : ℝ, (S.γ : ℝ) ≤ m →
      ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ S.T → ∀ φ : Torus d → ℝ, Torus.IsCk 2 φ → MemSobolev m φ →
        MemSobolev m (propagator (S.dynM M N) (S.ρ N) r t φ) →
        sobolevNorm m (propagator (S.dynM M N) (S.ρ N) r t φ) ≤ K * sobolevNorm m φ →
      ∀ X : Config d N, X ∉ collisionSet d N →
        |flucInteraction (S.dynM M N) (propagator (S.dynM M N) (S.ρ N) r t φ) X (S.ρ N r)| ≤
          C * sobolevNorm m φ * S.energyCompletion N X r := by
  sorry

/-- **GF-REM-norm** (dual-norm passage; TeX M L2452-2455: "uniformly over the unit ball of `H^γ`").  SORRIED.
Estimated size: S-M.  If `R : ℝ → Ω → E_m` has a.s. continuous paths on `[0,T]`, `B` has a.s. continuous paths, and for
every fixed `t ∈ [0,T]` and smooth `φ` almost surely `|⟨R_t, φ⟩| ≤ B_t ‖φ‖_{H^m}`, then almost surely
`‖R_t‖_{E_m} ≤ B_t` for all `t ∈ [0,T]` simultaneously.
Proof: `‖F‖_{E_m} = sup{⟨F, φ⟩ : φ` trigonometric polynomial with rational coefficients, `‖φ‖_{H^m} ≤ 1}` (Parseval in `ℓ²`),
a countable family; rational times and continuity of both sides. -/
theorem gf_norm_of_pairings {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (m T : ℝ)
    (R : ℝ → Ω → NegSobolev d m) (B : ℝ → Ω → ℝ)
    (hRc : ∀ᵐ ω ∂P, ContinuousOn (fun t => R t ω) (Set.Icc 0 T))
    (hBc : ∀ᵐ ω ∂P, ContinuousOn (fun t => B t ω) (Set.Icc 0 T))
    (hpair : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
      ∀ᵐ ω ∂P, |NegSobolev.eval (R t ω) φ| ≤ B t ω * sobolevNorm m φ) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, ‖R t ω‖ ≤ B t ω := by
  sorry

/-- **GF-EN** (energy moments of the remainder; TeX M L2452-2455 with `𝔈_N`, `𝔈_{N,2}` of L556-561).  SORRIED.
Estimated size: S-M.  `hMF` is needed (repair): without it `r ↦ ρ_N^r` may be non-measurable and the measurability/integrability
conjuncts fail.  For a filtered strong solution with finite energy moment, the completed energy is a.s. integrable
in time and nonnegative (`energy_nonneg` and `no_collision`), and
`E ∫_0^T 𝓔_N^r dr ≤ T 𝔈_N`, and (under `EnergyMoment2Finite`) `‖∫_0^T 𝓔_N^r dr‖_{L²(P)} ≤ T 𝔈_{N,2}` (Minkowski).
Needs the joint measurability of `(r,ω) ↦ 𝓔_N(X_r(ω), r)` (progressive measurability of `X`, measurability of `rieszEnergy`);
the last conjunct (a.e.-measurability of `ω ↦ ∫_0^T 𝓔`) is what lets the `ℝ≥0∞`-integral of the pathwise bound `C σ ∫_0^T 𝓔` be
moved between the enlargements and `Ω` by `lintegral_map'`.
The first two conjuncts are the integrability of the nonnegative upper bound `B_t = C σ ∫_0^t 𝓔` and its continuity in `t`,
needed by `gf_norm_of_pairings`. -/
theorem gf_energy_integral_moment (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (hMF : S.MFHypM M) (N : ℕ)
    (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hX : IsStrongSolution P (S.dynM M N) S.T X₀ W X)
    (hF : ∃ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X)
    (hE : S.EnergyMomentFinite P N X) :
    (∀ᵐ ω ∂P, ∀ r ∈ Set.Icc (0 : ℝ) S.T, 0 ≤ S.energyCompletion N (X (Real.toNNReal r) ω) r) ∧
    (∀ᵐ ω ∂P, IntegrableOn (fun r => S.energyCompletion N (X (Real.toNNReal r) ω) r) (Set.Icc (0 : ℝ) S.T)) ∧
    ∫⁻ ω, ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) S.T, S.energyCompletion N (X (Real.toNNReal r) ω) r) ∂P ≤
      ENNReal.ofReal (S.T * S.energyMoment P N X) ∧
    (S.EnergyMoment2Finite P N X →
      (∫⁻ ω, ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) S.T,
        S.energyCompletion N (X (Real.toNNReal r) ω) r) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (S.T * S.energyMoment2 P N X)) ∧
    AEMeasurable (fun ω => ∫ r in Set.Icc (0 : ℝ) S.T, S.energyCompletion N (X (Real.toNNReal r) ω) r) P := by
  sorry

/-! ### GF-TE: the trace-norm covariance error -/

/-- **GF-TE** (TeX M L2285-2299, `U:eq:trace-error` with `L = 1`; used at L2455-2459).  SORRIED.  Estimated size: L.
Pointwise: for a probability density `ρ ∈ C^{γ+2d+12}` with `cbNorm ≤ Λ`, a collision-free `X` and `q ≥ 0`,
`‖C_N - C̄_N‖_{𝔖₁} ≤ C q (𝓔_N^{1/2} + N^{-2/d})`, `C_N = covForm γ q (empirical X)`, `C̄_N = covForm γ q ρ`,
`𝓔_N = F_N + o_N(C₀)`, for `C₀ ≥ C₀min`.
Proof: trace duality `‖C - C̄‖₁ = 2q sup_{‖A‖≤1} (μ_N - μ)(φ_A)`, `φ_A(x) = ∑_j ⟨A b_{x,j}, b_{x,j}⟩`, with
`‖φ_A‖_{Ḣ^{(d-s)/2}} + ‖Δφ_A‖_∞ ≤ C‖A‖` (uniform in the unit ball of `𝔅(E_γ)`; `γ > max{d+4, …}`), and
`HRS.Uniform.Q12.filtered_coercivity_proof` with `L = 1`.  (Q14Aux6/7, Q48cCov have the Lipschitz/Fourier-feature analogues
for `bures2`; the trace-norm version is new.) -/
theorem gf_trace_error (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (γ : ℕ) (hγ : 2 * d + 10 < γ)
    (Λ : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, 2 ≤ N → ∀ ρ : Torus d → ℝ, IsProbDensity ρ → Torus.IsCk (γ + 2 * d + 12) ρ →
        Torus.cbNorm (γ + 2 * d + 12) ρ ≤ Λ → ∀ X : Config d N, X ∉ collisionSet d N →
        ∀ q : ℝ, 0 ≤ q →
          traceNormForm (covForm (γ : ℝ) q (empirical X) - covForm (γ : ℝ) q (withDensityReal ρ)) ≤
            C * q * (Real.sqrt (rieszEnergy d s X (withDensityReal ρ) + oN d s C₀ N) +
              (N : ℝ) ^ (-(2 : ℝ) / d)) := by
  sorry

/-- **GF-TE-moment** (TeX M L2455-2459: `E ∫_0^T ‖C_N^t - C̄_N^t‖₁ dt ≤ C q_N (𝔈_N^{1/2} + N^{-2/d})`).  SORRIED.
Estimated size: M (Tonelli on the progressive process `X`, Jensen `E 𝓔^{1/2} ≤ (E 𝓔)^{1/2}`, `0 ≤ 𝓔` a.s. from `energy_nonneg`
and `no_collision`, `E 𝓔^t ≤ 𝔈_N`; the pointwise bound is `gf_trace_error` with `q = q_N`).  Both sides in `ℝ≥0∞`. -/
theorem gf_trace_moment (b : GeneralBounds d) (M : Matrix (Fin d) (Fin d) ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHypM M → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStrongSolution P (S.dynM M N) S.T X₀ W X →
        (∃ (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        S.EnergyMomentFinite P N X →
        ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (traceNormForm
          (covForm (S.γ : ℝ) (qN S N) (empirical (X (Real.toNNReal r) ω)) -
            covForm (S.γ : ℝ) (qN S N) (withDensityReal (S.ρ N r))))) ∂P ≤
          ENNReal.ofReal (C * qN S N *
            (Real.sqrt (S.energyMoment P N X) + (N : ℝ) ^ (-(2 : ℝ) / d))) := by
  sorry

/-- **GF-TR-moment** (TeX M L2459-2465, `U:eq:transport-moment`: `E ∫_0^T W_2(μ_N^t, μ^t)² dt ≤ C(𝔈_N^{2a_{d,s}} + N^{-2/d})`,
`a_{d,s} = 1/max{2,d-s}`).  SORRIED.  Estimated size: M.
Pointwise input: `HRS.Uniform.Q12.energy_W2_proof` (proved; needs `ρ ≥ c`, `C₀ ≥ C₀min`), then `2a ≤ 1` and Jensen
`E 𝓔^{2a} ≤ (E 𝓔)^{2a} ≤ 𝔈^{2a}`, Tonelli.  Both sides in `ℝ≥0∞`.  The first conjunct (a.e.-measurability of the time integral of
`W₂²`, from joint measurability of `(r,ω) ↦ W₂(μ_N^r, μ^r)`, continuous in the configuration and in `r`) is needed to move the coupling cost
between enlargements. -/
theorem gf_transport_moment (b : GeneralBounds d) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHyp → S.PosDensityWith b.c →
      ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStrongSolution P (S.dyn N) S.T X₀ W X →
        (∃ (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        S.EnergyMomentFinite P N X →
        AEMeasurable (fun ω => ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal
          ((torusWassersteinE 2 (empirical (X (Real.toNNReal r) ω))
            (withDensityReal (S.ρ N r))).toReal ^ 2)) P ∧
        ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal
          ((torusWassersteinE 2 (empirical (X (Real.toNNReal r) ω))
            (withDensityReal (S.ρ N r))).toReal ^ 2)) ∂P ≤
          ENNReal.ofReal (C * (S.energyMoment P N X ^ ((2 : ℝ) / max 2 ((d : ℝ) - S.s)) +
            (N : ℝ) ^ (-(2 : ℝ) / d))) := by
  sorry

end HRS.GF
