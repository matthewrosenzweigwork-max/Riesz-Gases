import HRS.Main.GFSpec6

/-!
# Packet GF-SPEC, part 7 (LAST FILE): the conditional assembly of Theorem 2.1 and the assembly plan

## Status

All three statements of Theorem 2.1 (TeX M L580-620) are ASSEMBLED from the 21 sorried sub-packet statements of `GFSpec1`-`GFSpec3`
(listed below), up to proved glue (`GFSpec3`-`GFSpec6`):

* `gf_general_fluctuation_of_packets`          : `HRS.GeneralSetup.general_fluctuation`            (gradient clause: `d₂`, `W₁`, `W₂`)
* `gf_general_fluctuation_transport_of_packets`: `HRS.GeneralSetup.general_fluctuation_transport`  (transport improvement)
* `gf_general_fluctuation_matrix_of_packets`   : `HRS.GeneralSetup.general_fluctuation_matrix`     (general-matrix clause)

each followed by `example := (@… : type_of% @HRS.GeneralSetup.…)`, so the assembled statement is *literally* the frozen one.  The
assembly theorems use only the proved inputs `smooth_path_comparison_proof`, `Q45.maximal_estimate_meas`,
`relative_covariance_coupling_proof`, `Q14.q14_bures2_W2` and the 21 packets (`#print axioms`: only `sorryAx`, coming from the packets).
Since the frozen `C₀`-threshold prefix of ISSUES "SPEC-C0" is mirrored in the packets (`C₀min = max` of the `C₀min`'s of
`gf_remainder_bound` and of the moment packets), the chain below is closed.  Nothing was proved about the sorried packets.

## The chain (one chain for the three statements; `m = γ` or `γ+2`, `M = -I` or general)

(0) `GFEvo` evolution `EV : EvolData E_γ E_m` (`gf_ev_grad` / `gf_ev_mat`).  (1) `gf_init_enlargement` : `Ω₁ → Ω`, `ℱ₁`, `ℱ₁_0`-measurable `η'`;
`isStrongSolution_comp`, `energyMoment_comp`.  (2) `gf_particle_martingale` on `Ω₁`.  (3) `maximal_estimate_meas` on `Ω₁` +
`gf_measurable_modification` : measurable continuous `Z`.  (4) `gf_fluc_continuous`.  (5) `gf_remainder_bound` (from `gf_mild_identity`,
`gf_pair_identification`, `gf_remainder_pointwise`, `gf_norm_of_pairings`, `gf_energy_integral_moment`) : `sup_t ‖R_t‖ ≤ C σ ∫_0^T 𝓔`;
this is `gf_stage1` (`GFSpec6`).  (6) `gf_adapted_coupling_trace` / `_transport` (cost `‖Sg - Cb‖₁` / `C q W₂²`, deterministic covariation
`covDensT`) : second enlargement `Ω₂`, `Gb`, `Sd`.  (7) `gf_stage2` (`GFSpec5`): `smooth_path_comparison_proof` and `gf_wasserstein_comparison` on
`Ω₂`, `gf_law_identification` for `Law X̄ = Law Y`, laws/integrals moved back to `Ω₁` (`law_comp_mp`, `lintegral_comp_mp`).  (8) `gf_core` /
`gf_core_transport` (this file): initial term `= A_N ε_{N,p}` (`initial_term_eq`), remainder `≤ C σ T 𝔈`, covariance error
`≤ C q T(𝔈^{1/2} + N^{-2/d})` (`gf_trace_moment`) resp. `≤ C q T(𝔈^{2a} + N^{-2/d})`, `a = 1/max{2,d-s}` (`gf_transport_moment`), then
`(E∫cost)^{1/2} ≤ C √q (𝔈^{1/4} + N^{-1/d})` (`sqrt_cost_bound`, `sqrt_cost_bound2`).  (9) the three theorems: instantiate `gf_core` with
`(M, Hyp, μ, embedY, hev) = (-I, PosDensity, γ, id, gf_ev_grad)` resp. `(M, AdjointInput M K, γ+2, embed, gf_ev_mat)`, and for the
transport clause take the minimum of `gf_core` and `gf_core_transport` (`le_total` on the two covariance terms).

## Hypothesis table for `smooth_path_comparison_proof` / `gf_wasserstein_comparison` (verified by `gf_stage2` compiling)

`MaxHyp T K` ← `GFEvo.maxHyp`; `X₀, X₀'` `ℱ₂_0`-measurable ← `IsFilteredSolution.adapted`, `gf_measurable_ofMeasureDiff`, `η'` `ℱ₁_0`-measurable,
`filtration` field of the coupling; `M∘π₂` martingale ← `gf_particle_martingale` + `martingale` field; `G = Gb`, `Cb = covDensT` ← `gaussian` field +
`covDensT_truncated` + `gf_detCovDensity`; `IsStochConv` for `Z∘π₂` ← `isStochConv_comp`, for `Zb` ← `maximal_estimate_meas` + `gf_measurable_modification` +
`isStochConv_congr_ae`; continuity/measurability of `R` ← `gf_fluc_continuous`, `EV` strong continuity; `Xb` and the law ← `gf_law_identification`
(hypotheses from `gf_coupling_indep`, `law_init`); `W_p` difference martingale and cost ← `gf_coupling_difference`, `gf_coupling_cost_le`.

## The sorried packets (name; TeX M lines; size)

`gf_ev_grad` (L2026-2045, L2070-2076, L2034-2042; XL) · `gf_ev_mat` (L609-619, L2026-2033; L) · `gf_measurable_ofMeasureDiff` (L2284-2286; S-M) ·
`gf_fluc_continuous` (L521-528; M) · `gf_particle_martingale` (L2285-2293; L) · `gf_pair_identification` (L2447-2451; L) · `gf_mild_identity`
(L2445-2451, L1656-1658; M) · `gf_smooth_mem`, `gf_eval_sub` (S) · `gf_remainder_pointwise` (L2452-2455, L3294-3310; M-L) · `gf_norm_of_pairings`
(L2452-2455; S-M) · `gf_energy_integral_moment` (L556-561, L2452-2455; S-M) · `gf_trace_error` (L2285-2299; L; feeds `gf_trace_moment`, which is the
statement the assembly uses) · `gf_trace_moment` (L2455-2459; M) · `gf_transport_moment` (L2459-2465, L2354-2361; M) · `gf_detCovDensity` (S) ·
`gf_measurable_modification` (S-M) · `gf_init_enlargement` (L2456-2459; L) · `gf_law_identification` (L2456-2459; L-XL) ·
`gf_wasserstein_comparison` (L2457-2459, L2620-2641; L) · `gf_bures2_le_traceNorm` (L2121-2137, L2686; S-M).

## Defects of the first draft found while assembling (all fixed in the statements)

(1) `maximal_estimate_meas` gives `AEMeasurable (Z t)` only: `gf_measurable_modification`.  (2) a.s. integrability/continuity of `∫_0^t 𝓔` and
the `L¹`/`L²` moments: `gf_energy_integral_moment` (with an `AEMeasurable` conjunct).  (3) `transport_noise_coupling_proof` needs
`Measurable (r ↦ covForm γ q ρ_r x y)` for ALL real `r`, false for an arbitrary extension of `ρ_N` off `[0,T]`: `gf_adapted_coupling_transport`
for `covDensT` (zero off `[0,T]`), also with a constant `Ct : ℝ → ℝ` so that it is uniform for `γ = b.γ`.  (4) the packet constants must not depend
on the level `m ∈ [γ, γ+2]` or on `N`: `gf_remainder_pointwise/_bound` quantify `m` after the constants; `gf_stage2` takes `(T,K)` first.
(5) `smooth_path_comparison_proof` needs `Measurable` AND a.s.-continuous `Z`, `R`: modification.  (6) `gf_wasserstein_comparison`
does not need the martingale/covariation data of `M`, only the difference martingale.  (7) the coupling gives the Gaussian
martingale on a SECOND enlargement on which the Brownian structure of `W'` is lost, so `gf_particle_martingale`, `gf_pair_identification`,
`gf_mild_identity`, `gf_remainder_bound` live on the FIRST enlargement only and `Z` is transported by `isStochConv_comp`.

## Review repairs (2nd round)

* `gf_energy_integral_moment` now takes `hMF : S.MFHypM M` (measurability of `r ↦ ρ_N^r`); `gf_wasserstein_comparison` takes measurable `X₀, X₀'`;
  `GFEvo.adjoint` asserts `MemSobolev m (propagator …)` and `gf_remainder_pointwise` takes it as a hypothesis.
* MATRIX CLAUSE: the repaired `AdjointInput` (ISSUES "ADJIN": uniqueness conjunct + `MemSobolev` clauses) supplies uniqueness (cocycle) and the
  `MemSobolev` facts, so `gf_ev_mat` needs only `S.AdjointInput M K` and the `type_of%` tie of the matrix theorem is restored.  Existence at level `γ+2`
  comes from the `γ` clause via `H^{γ+2} ⊂ H^γ`.
* Notes: (N1) `ℱ'_t` for `t < 0` contains `π⁻¹ℱ_t` and the null sets, `η'` only for `t ≥ 0`; (N2) the `Dissipative` core is `E_{γ-2}`; (N3) `GFEvo` is
  unsatisfiable for `m < γ` (harmless).

## Doubts (for the reviewer)

* `gf_ev_grad` for `β_N = ∞` (`invβ = 0`): the adjoint classical solution and the dissipative alternative are claimed uniformly in `β ∈ [0, B_β]`
  (`gradient_energy` is uniform down to `ν = 0`; the classical solvability at `ν = 0` rests on `adjoint_torus`, regimes R1/R2b).
* `gf_pair_identification` needs, qualitatively, `U^{r,t}φ ∈ C¹([0,t]; H^γ)` for smooth `φ` (so `∂_r U^{r,t}φ = -𝓛_r U^{r,t}φ ∈ H^γ`), i.e.
  `U^{r,t}φ ∈ H^{γ+2}`: true by the `C^{γ+2d+12}` regularity of the coefficients but not recorded in `GFEvo.adjoint`.
* `gf_law_identification` uses Lévy's characterisation (continuous Hilbert martingale with deterministic covariation is Gaussian) and the
  stochastic Fubini for `C¹` deterministic integrands; `IsLinearFluctuationSolution` constrains smooth tests only (enough: smooth trigonometric
  polynomials determine the law on the separable `E_m`).
* `gf_init_enlargement` also requires `IsCompleteFiltration` for `ℱ'`: take the `P'`-null sets into `ℱ'_0`.
* `gf_transport_moment` includes the joint measurability of `(r,ω) ↦ W₂(μ_N^r, μ^r)` (continuity in the configuration and, through the norm
  continuity of `r ↦ ρ_r`, in `r`); `gf_trace_error` is the only genuinely new analytic estimate among the packets besides the evolution packets.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS.Uniform

variable {d : ℕ}

/-! ### Real arithmetic for the closing step (PROVED) -/

theorem lin3 {x y z a b c C : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (ha : a ≤ C) (hb : b ≤ C) (hc : c ≤ C) :
    a * x + b * y + c * z ≤ C * (x + y + z) := by
  nlinarith [mul_le_mul_of_nonneg_right ha hx, mul_le_mul_of_nonneg_right hb hy,
    mul_le_mul_of_nonneg_right hc hz]

/-- `√(C q (√E + n²)) ≤ √C √q (E^{1/4} + n)`. -/
theorem sqrt_cost_bound {C q E n : ℝ} (hC : 0 ≤ C) (hq : 0 ≤ q) (hE : 0 ≤ E) (hn : 0 ≤ n) :
    Real.sqrt (C * q * (Real.sqrt E + n * n)) ≤
      Real.sqrt C * Real.sqrt q * (E ^ ((1 : ℝ) / 4) + n) := by
  have h4 : E ^ ((1 : ℝ) / 4) = Real.sqrt (Real.sqrt E) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hE]
    norm_num
  rw [Real.sqrt_mul (mul_nonneg hC hq), Real.sqrt_mul hC, h4]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt (Real.sqrt_nonneg E), Real.sqrt_nonneg (Real.sqrt E),
    mul_nonneg (Real.sqrt_nonneg (Real.sqrt E)) hn]

/-- `√(C q (E^{2e} + n²)) ≤ √C √q (E^e + n)` (the transport version of `sqrt_cost_bound`). -/
theorem sqrt_cost_bound2 {C q E n e : ℝ} (hC : 0 ≤ C) (hq : 0 ≤ q) (hE : 0 ≤ E) (hn : 0 ≤ n) :
    Real.sqrt (C * q * (E ^ (2 * e) + n * n)) ≤ Real.sqrt C * Real.sqrt q * (E ^ e + n) := by
  have hEe : 0 ≤ E ^ e := Real.rpow_nonneg hE e
  have h2 : E ^ (2 * e) = E ^ e * E ^ e := by
    rw [mul_comm, Real.rpow_mul hE, Real.rpow_two, sq]
  rw [h2, Real.sqrt_mul (mul_nonneg hC hq), Real.sqrt_mul hC]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [mul_nonneg hEe hn]

/-- PROVED.  `N^{-2/d} = (N^{-1/d})²`. -/
theorem rpow_neg_two_div (d N : ℕ) (hN : 0 < N) :
    (N : ℝ) ^ (-(2 : ℝ) / d) = (N : ℝ) ^ (-(1 : ℝ) / d) * (N : ℝ) ^ (-(1 : ℝ) / d) := by
  rw [← Real.rpow_add (by exact_mod_cast hN)]
  congr 1
  ring

/-- PROVED.  The energy moments are nonnegative (the completed energy is a.s. nonnegative). -/
theorem energyMoment_nonneg (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (hMF : S.MFHypM M) (N : ℕ)
    (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hX : IsStrongSolution P (S.dynM M N) S.T X₀ W X)
    (hF : ∃ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X)
    (hE : S.EnergyMomentFinite P N X) : 0 ≤ S.energyMoment P N X := by
  have hnn := (gf_energy_integral_moment S M hMF N hN P X₀ W X hX hF hE).1
  unfold GeneralSetup.energyMoment
  refine Real.iSup_nonneg fun t => integral_nonneg_of_ae ?_
  filter_upwards [hnn] with ω hω
  exact hω t.1 t.2

/-- PROVED.  `ε_{N,p} ≥ 0`. -/
theorem initialError_nonneg (S : GeneralSetup d) {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (p : ℝ)
    (X₀ : Ω → Config d N) (η₀ : Ω → NegSobolev d (S.γ : ℝ)) : 0 ≤ S.initialError P N p X₀ η₀ := by
  unfold GeneralSetup.initialError
  exact Real.rpow_nonneg (integral_nonneg fun ω => by positivity) _

set_option maxHeartbeats 1600000 in
/-- **`gf_core`: the three estimates of Theorem 2.1 from the sub-packet statements** (PROVED, conditional on the sorried packets).
Parametrised by the matrix `M`, an extra hypothesis `Hyp` on the setup, the level `μ S ∈ {γ, γ+2}`, the embedding `embedY` of the
initial datum into `E_{μ S}`, and an evolution provider `hev` (`gf_ev_grad` resp. `gf_ev_mat`). -/
theorem gf_core (b : GeneralBounds d) (M : Matrix (Fin d) (Fin d) ℝ) (Hyp : GeneralSetup d → Prop)
    (μ : GeneralSetup d → ℝ) (hμ : ∀ S : GeneralSetup d, (S.γ : ℝ) ≤ μ S)
    (embedY : ∀ S : GeneralSetup d, NegSobolev d (S.γ : ℝ) → NegSobolev d (μ S)) (K : ℝ)
    (hev : ∀ S : GeneralSetup d, S.Within { b with C₀ := S.C₀ } → S.MFHypM M → Hyp S → ∀ N : ℕ,
      ∃ EV : EvolData (NegSobolev d (S.γ : ℝ)) (NegSobolev d (μ S)),
        GFEvo S M N (μ S) K EV ∧ ∀ x, EV.j x = embedY S x) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHypM M → Hyp S →
      ∀ (N : ℕ) (_ : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P]
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
      (X : ℝ≥0 → Ω → Config d N) (_ : IsStrongSolution P (S.dynM M N) S.T X₀ W X)
      (_ : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
        (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X)
      (_ : S.EnergyMomentFinite P N X)
      (η₀ : Ω → NegSobolev d (S.γ : ℝ)) (_ : Measurable η₀)
      (_ : ProbabilityTheory.IndepFun (fun ω => (X₀ ω, η₀ ω)) (fun ω => fun t => W t ω) P)
      (_ : S.InitialErrorFinite P N 1 X₀ η₀)
      (Y : ℝ → Ω → NegSobolev d (μ S))
      (_ : IsLinearFluctuationSolution P (S.dynM M N) (S.ρ N) (μ S) (qN S N) S.T
        (fun ω => AN S N • embedY S (η₀ ω)) Y),
      smoothDist 2 (law P (flucPath (μ S) S.T (sigN S N) X (S.ρ N))) (law P (toPath (μ S) S.T Y)) ≤
          C * (AN S N * S.initialError P N 1 X₀ η₀ + sigN S N * S.energyMoment P N X +
            qN S N * (Real.sqrt (S.energyMoment P N X) + (N : ℝ) ^ (-(2 : ℝ) / d))) ∧
      wassersteinE 1 (law P (flucPath (μ S) S.T (sigN S N) X (S.ρ N))) (law P (toPath (μ S) S.T Y)) ≤
        ENNReal.ofReal (C * (AN S N * S.initialError P N 1 X₀ η₀ + sigN S N * S.energyMoment P N X +
            Real.sqrt (qN S N) * (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d)))) ∧
      (S.EnergyMoment2Finite P N X →
        Integrable (fun ω => ‖flucPath (μ S) S.T (sigN S N) X (S.ρ N) ω‖ ^ 2) P →
        S.InitialErrorFinite P N 2 X₀ η₀ →
        wassersteinE 2 (law P (flucPath (μ S) S.T (sigN S N) X (S.ρ N))) (law P (toPath (μ S) S.T Y)) ≤
          ENNReal.ofReal (C * (AN S N * S.initialError P N 2 X₀ η₀ +
            sigN S N * S.energyMoment2 P N X +
            Real.sqrt (qN S N) * (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d))))) := by
  obtain ⟨C₀a, hs1⟩ := gf_stage1 b M K
  obtain ⟨C₀b, htr⟩ := gf_trace_moment b M
  refine ⟨max C₀a C₀b, fun C₀ hC₀ => ?_⟩
  by_cases hex : ∃ S₀ : GeneralSetup d, S₀.Within { b with C₀ := C₀ }
  swap
  · exact ⟨1, one_pos, fun S hS => absurd ⟨S, hS⟩ hex⟩
  obtain ⟨S₀, hS₀⟩ := hex
  have hbT : 0 ≤ b.T := by rw [← hS₀.2.1]; exact S₀.hT.le
  obtain ⟨Cr, hCr, hs1'⟩ := hs1 C₀ (le_trans (le_max_left _ _) hC₀)
  obtain ⟨Cte, hCte, hte⟩ := htr C₀ (le_trans (le_max_right _ _) hC₀)
  obtain ⟨C2, hC20, hs2⟩ := gf_stage2 b.T K hbT
  set C : ℝ := C2 + Cr * b.T + C2 * Cte + C2 * Real.sqrt Cte + 1 with hCdef
  have hCpos : 0 < C := by
    have : 0 ≤ C2 + Cr * b.T + C2 * Cte + C2 * Real.sqrt Cte := by positivity
    linarith
  refine ⟨C, hCpos, ?_⟩
  intro S hS hMF hHyp N hN Ω mΩ P _ X₀ W X hX hF hE η₀ hη hind hfin1 Y hY
  have hST : S.T = b.T := hS.2.1
  have hT' : 0 ≤ S.T := S.hT.le
  have hSw : S.Within { b with C₀ := S.C₀ } := by
    have hC : S.C₀ = C₀ := hS.2.2.2.2.2.1
    rw [hC]; exact hS
  obtain ⟨EV, hEV, hj⟩ := hev S hSw hMF hHyp N
  have hm := hμ S
  have hembY : Measurable (embedY S) := by
    have : embedY S = EV.j := funext fun x => (hj x).symm
    rw [this]; exact EV.j.continuous.measurable
  set Y₀ : Ω → NegSobolev d (μ S) := fun ω => AN S N • embedY S (η₀ ω) with hY₀def
  have hY₀m : Measurable Y₀ := (hembY.comp hη).const_smul (AN S N)
  have hY₀ : ∀ ω, Y₀ ω = EV.j (AN S N • η₀ ω) := fun ω => by
    simp only [hY₀def]
    rw [map_smul, hj]
  obtain ⟨Ω₁, mΩ₁, P₁, hP₁, π₁, hπ₁, ℱ₁, η', Mart, Z, Bm, hS1, hX₁, hF₁, hE₁, hEeq, hlaw, hinit, hBm1, hBm2⟩ :=
    hs1' S hS hMF N hN (μ S) hm EV hEV P X₀ W X hX hF hE η₀ hη hind Y₀ hY₀m hY₀ Y hY
  set X₁ : ℝ≥0 → Ω₁ → Config d N := fun t ω => X t (π₁ ω) with hX₁def
  have hq0 := qN_nonneg S N
  have hσ0 := sigN_nonneg S N
  have hA0 := AN_nonneg S N
  have hE0 := energyMoment_nonneg S M hMF N hN P X₀ W X hX hF hE
  have hε1 := initialError_nonneg S P 1 X₀ η₀
  have hn0 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / d) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hn2 := rpow_neg_two_div d N (by omega)
  -- the trace-norm coupling and the comparison estimates on the first enlargement
  set Sg : ℝ → Ω₁ → (NegSobolev d (S.γ : ℝ) →L[ℝ] NegSobolev d (S.γ : ℝ) →L[ℝ] ℝ) :=
    fun r ω => covForm (S.γ : ℝ) (qN S N) (empirical (X₁ (Real.toNNReal r) ω)) with hSg
  set Cb := covDensT (S.γ : ℝ) (qN S N) S.T (S.ρ N) with hCb
  have hcpl := gf_adapted_coupling_trace P₁ ℱ₁ S.T hT' ⟨ℱ₁ 0, le_rfl⟩ Mart Sg hS1.mart Cb hS1.det
  have hcostm : AEMeasurable (fun ω => ∫⁻ r in Set.Icc (0 : ℝ) S.T,
      ENNReal.ofReal (traceNormForm (Sg r ω - Cb r))) P₁ :=
    (measurable_trace_integral hS1.mart hS1.det).aemeasurable
  obtain ⟨hsm, hW⟩ := hs2 S hST M hMF N hN (μ S) hm EV hEV P P₁ ℱ₁ X₁ η' Mart Z Bm Y₀ Y hS1
    (fun r ω => traceNormForm (Sg r ω - Cb r)) hcpl hcostm
  rw [hlaw] at hsm hW
  -- the covariance-error moment
  have hte' := hte S hS hMF N hN P₁ (fun ω => X₀ (π₁ ω)) (fun t ω => W t (π₁ ω)) X₁ hX₁ hF₁ hE₁
  rw [hEeq] at hte'
  have hconvc : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T,
      ENNReal.ofReal (traceNormForm (Sg r ω - Cb r))) ∂P₁ =
      ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (traceNormForm
        (covForm (S.γ : ℝ) (qN S N) (empirical (X₁ (Real.toNNReal r) ω)) -
          covForm (S.γ : ℝ) (qN S N) (withDensityReal (S.ρ N r))))) ∂P₁ := by
    refine lintegral_congr fun ω => ?_
    refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    simp only [hSg, hCb, covDensT, if_pos hr]
  have hinit1 : ∫⁻ ω, ‖flucProc (S.γ : ℝ) (sigN S N) X₁ (S.ρ N) 0 ω - AN S N • η' ω‖ₑ ∂P₁ =
      ENNReal.ofReal (AN S N * S.initialError P N 1 X₀ η₀) := by
    have := hinit 1 (Or.inl rfl) hfin1
    simpa using this
  have hcostB : (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (traceNormForm (Sg r ω - Cb r))) ∂P₁) ≤
      ENNReal.ofReal (Cte * qN S N * (Real.sqrt (S.energyMoment P N X) + (N : ℝ) ^ (-(2 : ℝ) / d))) := by
    rw [hconvc]; exact hte'
  refine ⟨?_, ?_, ?_⟩
  · -- the smooth estimate
    have hfin : ENNReal.ofReal (smoothDist 2 (law P (flucPath (μ S) S.T (sigN S N) X (S.ρ N)))
        (law P (toPath (μ S) S.T Y))) ≤ ENNReal.ofReal (C * (AN S N * S.initialError P N 1 X₀ η₀ +
          sigN S N * S.energyMoment P N X +
          qN S N * (Real.sqrt (S.energyMoment P N X) + (N : ℝ) ^ (-(2 : ℝ) / d)))) := by
      refine hsm.trans ?_
      rw [hinit1]
      have h3 : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (traceNormForm
          (covForm (S.γ : ℝ) (qN S N) (empirical (X₁ (Real.toNNReal r) ω)) -
            covForm (S.γ : ℝ) (qN S N) (withDensityReal (S.ρ N r))))) ∂P₁ ≤
          ENNReal.ofReal (Cte * qN S N * (Real.sqrt (S.energyMoment P N X) + (N : ℝ) ^ (-(2 : ℝ) / d))) := hte'
      have hz : 0 ≤ qN S N * (Real.sqrt (S.energyMoment P N X) + (N : ℝ) ^ (-(2 : ℝ) / d)) :=
        mul_nonneg hq0 (add_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg N) _))
      have hx : 0 ≤ AN S N * S.initialError P N 1 X₀ η₀ := mul_nonneg hA0 hε1
      have hy : 0 ≤ sigN S N * S.energyMoment P N X := mul_nonneg hσ0 hE0
      calc _ ≤ ENNReal.ofReal C2 * ENNReal.ofReal (AN S N * S.initialError P N 1 X₀ η₀) +
            ENNReal.ofReal (Cr * sigN S N * (b.T * S.energyMoment P N X)) +
            ENNReal.ofReal C2 * ENNReal.ofReal (Cte * qN S N *
              (Real.sqrt (S.energyMoment P N X) + (N : ℝ) ^ (-(2 : ℝ) / d))) := by
            gcongr
            · rw [← hST]; exact hBm1
        _ = ENNReal.ofReal (C2 * (AN S N * S.initialError P N 1 X₀ η₀) +
            (Cr * S.T) * (sigN S N * S.energyMoment P N X) +
            (C2 * Cte) * (qN S N * (Real.sqrt (S.energyMoment P N X) + (N : ℝ) ^ (-(2 : ℝ) / d)))) := by
            rw [← ENNReal.ofReal_mul hC20, ← ENNReal.ofReal_mul hC20, ← ENNReal.ofReal_add (by positivity)
              (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1
            rw [hST]
            ring
        _ ≤ _ := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [hST]
            have hsq := mul_nonneg hC20 (Real.sqrt_nonneg Cte)
            have hp1 := mul_nonneg hCr.le hbT
            have hp2 := mul_nonneg hC20 hCte.le
            have hCa : C2 ≤ C := by rw [hCdef]; linarith
            have hCb' : Cr * b.T ≤ C := by rw [hCdef]; linarith
            have hCc : C2 * Cte ≤ C := by rw [hCdef]; linarith
            exact lin3 hx hy hz hCa hCb' hCc
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hfin
  · -- the `W₁` estimate
    have hW1 := hW 1 (Or.inl rfl)
    have hinitp := hinit 1 (Or.inl rfl) hfin1
    have hB1 : (∫⁻ ω, Bm ω ^ (1 : ℝ) ∂P₁) ^ (1 / (1 : ℝ)) ≤
        ENNReal.ofReal (Cr * sigN S N * (S.T * S.energyMoment P N X)) := by
      simpa using hBm1
    have hcost' : (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T,
        ENNReal.ofReal (traceNormForm (Sg r ω - Cb r))) ∂P₁) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (Real.sqrt Cte * Real.sqrt (qN S N) *
          (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d))) := by
      calc _ ≤ (ENNReal.ofReal (Cte * qN S N * (Real.sqrt (S.energyMoment P N X) +
              (N : ℝ) ^ (-(2 : ℝ) / d)))) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hcostB (by norm_num)
        _ = ENNReal.ofReal (Real.sqrt (Cte * qN S N * (Real.sqrt (S.energyMoment P N X) +
              (N : ℝ) ^ (-(1 : ℝ) / d) * (N : ℝ) ^ (-(1 : ℝ) / d)))) := by
            rw [← hn2, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
              show (1 / 2 : ℝ) = (1 : ℝ) / 2 from rfl, ← Real.sqrt_eq_rpow]
        _ ≤ _ := ENNReal.ofReal_le_ofReal (sqrt_cost_bound hCte.le hq0 hE0 hn0)
    have hx : 0 ≤ AN S N * S.initialError P N 1 X₀ η₀ := mul_nonneg hA0 hε1
    have hy : 0 ≤ sigN S N * S.energyMoment P N X := mul_nonneg hσ0 hE0
    have hz : 0 ≤ Real.sqrt (qN S N) * (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d)) :=
      mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (Real.rpow_nonneg hE0 _) hn0)
    calc _ ≤ ENNReal.ofReal C2 * ENNReal.ofReal (AN S N * S.initialError P N 1 X₀ η₀) +
          ENNReal.ofReal (Cr * sigN S N * (S.T * S.energyMoment P N X)) +
          ENNReal.ofReal C2 * ENNReal.ofReal (Real.sqrt Cte * Real.sqrt (qN S N) *
            (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d))) := by
          refine hW1.trans ?_
          rw [hinitp]
          gcongr
      _ = ENNReal.ofReal (C2 * (AN S N * S.initialError P N 1 X₀ η₀) +
          (Cr * S.T) * (sigN S N * S.energyMoment P N X) +
          (C2 * Real.sqrt Cte) * (Real.sqrt (qN S N) *
            (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d)))) := by
          rw [← ENNReal.ofReal_mul hC20, ← ENNReal.ofReal_mul hC20, ← ENNReal.ofReal_add (by positivity)
            (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          rw [hST]
          ring
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hST]
          have hsq := mul_nonneg hC20 (Real.sqrt_nonneg Cte)
          have hp1 := mul_nonneg hCr.le hbT
          have hp2 := mul_nonneg hC20 hCte.le
          have hCa : C2 ≤ C := by rw [hCdef]; linarith
          have hCb' : Cr * b.T ≤ C := by rw [hCdef]; linarith
          have hCc : C2 * Real.sqrt Cte ≤ C := by rw [hCdef]; linarith
          exact lin3 hx hy hz hCa hCb' hCc
  · -- the `W₂` estimate
    intro hE2 _ hfin2
    have hW2 := hW 2 (Or.inr rfl)
    have hinitp := hinit 2 (Or.inr rfl) hfin2
    have hB2 := hBm2 hE2
    have hE20 : 0 ≤ S.energyMoment2 P N X := by
      unfold GeneralSetup.energyMoment2
      exact Real.iSup_nonneg fun t => Real.sqrt_nonneg _
    have hε2 := initialError_nonneg S P 2 X₀ η₀
    have hcost' : (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T,
        ENNReal.ofReal (traceNormForm (Sg r ω - Cb r))) ∂P₁) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (Real.sqrt Cte * Real.sqrt (qN S N) *
          (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d))) := by
      calc _ ≤ (ENNReal.ofReal (Cte * qN S N * (Real.sqrt (S.energyMoment P N X) +
              (N : ℝ) ^ (-(2 : ℝ) / d)))) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hcostB (by norm_num)
        _ = ENNReal.ofReal (Real.sqrt (Cte * qN S N * (Real.sqrt (S.energyMoment P N X) +
              (N : ℝ) ^ (-(1 : ℝ) / d) * (N : ℝ) ^ (-(1 : ℝ) / d)))) := by
            rw [← hn2, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
              show (1 / 2 : ℝ) = (1 : ℝ) / 2 from rfl, ← Real.sqrt_eq_rpow]
        _ ≤ _ := ENNReal.ofReal_le_ofReal (sqrt_cost_bound hCte.le hq0 hE0 hn0)
    have hx : 0 ≤ AN S N * S.initialError P N 2 X₀ η₀ := mul_nonneg hA0 hε2
    have hy : 0 ≤ sigN S N * S.energyMoment2 P N X := mul_nonneg hσ0 hE20
    have hz : 0 ≤ Real.sqrt (qN S N) * (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d)) :=
      mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (Real.rpow_nonneg hE0 _) hn0)
    calc _ ≤ ENNReal.ofReal C2 * ENNReal.ofReal (AN S N * S.initialError P N 2 X₀ η₀) +
          ENNReal.ofReal (Cr * sigN S N * (S.T * S.energyMoment2 P N X)) +
          ENNReal.ofReal C2 * ENNReal.ofReal (Real.sqrt Cte * Real.sqrt (qN S N) *
            (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d))) := by
          refine hW2.trans ?_
          rw [hinitp]
          gcongr
      _ = ENNReal.ofReal (C2 * (AN S N * S.initialError P N 2 X₀ η₀) +
          (Cr * S.T) * (sigN S N * S.energyMoment2 P N X) +
          (C2 * Real.sqrt Cte) * (Real.sqrt (qN S N) *
            (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d)))) := by
          rw [← ENNReal.ofReal_mul hC20, ← ENNReal.ofReal_mul hC20, ← ENNReal.ofReal_add (by positivity)
            (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          rw [hST]
          ring
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hST]
          have hsq := mul_nonneg hC20 (Real.sqrt_nonneg Cte)
          have hp1 := mul_nonneg hCr.le hbT
          have hp2 := mul_nonneg hC20 hCte.le
          have hCa : C2 ≤ C := by rw [hCdef]; linarith
          have hCb' : Cr * b.T ≤ C := by rw [hCdef]; linarith
          have hCc : C2 * Real.sqrt Cte ≤ C := by rw [hCdef]; linarith
          exact lin3 hx hy hz hCa hCb' hCc

set_option maxHeartbeats 1600000 in
/-- **`gf_core_transport`: the transport improvement (`W₁`, `W₂` with the transport covariance cost) from the sub-packet statements**
(PROVED, conditional on the sorried packets).  Gradient clause with positive density: stage 2 with the transport coupling
`gf_adapted_coupling_transport` (cost `C q W₂²`) and `gf_transport_moment`. -/
theorem gf_core_transport (b : GeneralBounds d) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHypM (-1) → S.PosDensityWith b.c →
      ∀ (N : ℕ) (_ : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P]
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
      (X : ℝ≥0 → Ω → Config d N) (_ : IsStrongSolution P (S.dynM (-1) N) S.T X₀ W X)
      (_ : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
        (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X)
      (_ : S.EnergyMomentFinite P N X)
      (η₀ : Ω → NegSobolev d (S.γ : ℝ)) (_ : Measurable η₀)
      (_ : ProbabilityTheory.IndepFun (fun ω => (X₀ ω, η₀ ω)) (fun ω => fun t => W t ω) P)
      (_ : S.InitialErrorFinite P N 1 X₀ η₀)
      (Y : ℝ → Ω → NegSobolev d (S.γ : ℝ))
      (_ : IsLinearFluctuationSolution P (S.dynM (-1) N) (S.ρ N) (S.γ : ℝ) (qN S N) S.T
        (fun ω => AN S N • η₀ ω) Y),
      wassersteinE 1 (law P (flucPath (S.γ : ℝ) S.T (sigN S N) X (S.ρ N))) (law P (toPath (S.γ : ℝ) S.T Y)) ≤
        ENNReal.ofReal (C * (AN S N * S.initialError P N 1 X₀ η₀ + sigN S N * S.energyMoment P N X +
            Real.sqrt (qN S N) * (S.energyMoment P N X ^ ((1 : ℝ) / max 2 ((d : ℝ) - S.s)) +
              (N : ℝ) ^ (-(1 : ℝ) / d)))) ∧
      (S.EnergyMoment2Finite P N X →
        Integrable (fun ω => ‖flucPath (S.γ : ℝ) S.T (sigN S N) X (S.ρ N) ω‖ ^ 2) P →
        S.InitialErrorFinite P N 2 X₀ η₀ →
        wassersteinE 2 (law P (flucPath (S.γ : ℝ) S.T (sigN S N) X (S.ρ N))) (law P (toPath (S.γ : ℝ) S.T Y)) ≤
          ENNReal.ofReal (C * (AN S N * S.initialError P N 2 X₀ η₀ +
            sigN S N * S.energyMoment2 P N X +
            Real.sqrt (qN S N) * (S.energyMoment P N X ^ ((1 : ℝ) / max 2 ((d : ℝ) - S.s)) +
              (N : ℝ) ^ (-(1 : ℝ) / d))))) := by
  obtain ⟨K, hK0, hev⟩ := gf_ev_grad b
  obtain ⟨C₀a, hs1⟩ := gf_stage1 b (-1) K
  obtain ⟨C₀c, htm⟩ := gf_transport_moment b
  refine ⟨max C₀a C₀c, fun C₀ hC₀ => ?_⟩
  by_cases hex : ∃ S₀ : GeneralSetup d, S₀.Within { b with C₀ := C₀ }
  swap
  · exact ⟨1, one_pos, fun S hS => absurd ⟨S, hS⟩ hex⟩
  obtain ⟨S₀, hS₀⟩ := hex
  have hbT : 0 ≤ b.T := by rw [← hS₀.2.1]; exact S₀.hT.le
  have hd1 : 1 ≤ d := by have := S₀.hd; omega
  have hγb : (d : ℝ) / 2 + 2 < (b.γ : ℝ) := by
    have h1 : 2 * d + 10 < S₀.γ := S₀.hγ
    have h2 : S₀.γ = b.γ := hS₀.2.2.1
    have h3 : ((2 * d + 10 : ℕ) : ℝ) < (b.γ : ℝ) := by exact_mod_cast (h2 ▸ h1)
    push_cast at h3
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨Cr, hCr, hs1'⟩ := hs1 C₀ (le_trans (le_max_left _ _) hC₀)
  obtain ⟨Ct, hCt, htm'⟩ := htm C₀ (le_trans (le_max_right _ _) hC₀)
  obtain ⟨C2, hC20, hs2⟩ := gf_stage2 b.T K hbT
  obtain ⟨Ctr, hCtr⟩ := gf_adapted_coupling_transport (d := d) hd1
  have hCtrb : 0 < Ctr (b.γ : ℝ) := (hCtr (b.γ : ℝ) hγb).1
  set C : ℝ := C2 + Cr * b.T + C2 * Real.sqrt (Ctr (b.γ : ℝ) * Ct) + 1 with hCdef
  have hCpos : 0 < C := by
    have : 0 ≤ C2 + Cr * b.T + C2 * Real.sqrt (Ctr (b.γ : ℝ) * Ct) := by positivity
    linarith
  refine ⟨C, hCpos, ?_⟩
  intro S hS hMF hPos N hN Ω mΩ P _ X₀ W X hX hF hE η₀ hη hind hfin1 Y hY
  have hST : S.T = b.T := hS.2.1
  have hT' : 0 ≤ S.T := S.hT.le
  have hSw : S.Within { b with C₀ := S.C₀ } := by
    have hC : S.C₀ = C₀ := hS.2.2.2.2.2.1
    rw [hC]; exact hS
  obtain ⟨EV, hEV⟩ := hev S hSw hMF hPos N
  have hm : (S.γ : ℝ) ≤ (S.γ : ℝ) := le_rfl
  have hj : ∀ x, EV.j x = x := fun x => by rw [hEV.j_eq, embed_self]
  set Y₀ : Ω → NegSobolev d (S.γ : ℝ) := fun ω => AN S N • η₀ ω with hY₀def
  have hY₀m : Measurable Y₀ := hη.const_smul (AN S N)
  have hY₀ : ∀ ω, Y₀ ω = EV.j (AN S N • η₀ ω) := fun ω => by rw [hj]
  obtain ⟨Ω₁, mΩ₁, P₁, hP₁, π₁, hπ₁, ℱ₁, η', Mart, Z, Bm, hS1, hX₁, hF₁, hE₁, hEeq, hlaw, hinit, hBm1, hBm2⟩ :=
    hs1' S hS hMF N hN (S.γ : ℝ) hm EV hEV P X₀ W X hX hF hE η₀ hη hind Y₀ hY₀m hY₀ Y hY
  set X₁ : ℝ≥0 → Ω₁ → Config d N := fun t ω => X t (π₁ ω) with hX₁def
  have hq0 := qN_nonneg S N
  have hσ0 := sigN_nonneg S N
  have hA0 := AN_nonneg S N
  have hE0 := energyMoment_nonneg S (-1) hMF N hN P X₀ W X hX hF hE
  have hε1 := initialError_nonneg S P 1 X₀ η₀
  have hn0 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / d) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hn2 := rpow_neg_two_div d N (by omega)
  have hγS : (d : ℝ) / 2 + 2 < (S.γ : ℝ) := by
    have h1 : 2 * d + 10 < S.γ := S.hγ
    have h3 : ((2 * d + 10 : ℕ) : ℝ) < (S.γ : ℝ) := by exact_mod_cast h1
    push_cast at h3
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hCtS : Ctr (S.γ : ℝ) = Ctr (b.γ : ℝ) := by rw [hS.2.2.1]
  have hCtSpos : 0 < Ctr (S.γ : ℝ) := (hCtr (S.γ : ℝ) hγS).1
  set Sg : ℝ → Ω₁ → (NegSobolev d (S.γ : ℝ) →L[ℝ] NegSobolev d (S.γ : ℝ) →L[ℝ] ℝ) :=
    fun r ω => covForm (S.γ : ℝ) (qN S N) (empirical (X₁ (Real.toNNReal r) ω)) with hSg
  set Cb := covDensT (S.γ : ℝ) (qN S N) S.T (S.ρ N) with hCb
  have hdens : ∀ r ∈ Set.Icc (0 : ℝ) S.T, IsProbDensity (S.ρ N r) := fun r hr => (hMF N).1.density r hr
  have hcplT := (hCtr (S.γ : ℝ) hγS).2 P₁ ℱ₁ ⟨ℱ₁ 0, le_rfl⟩ N (by omega) (qN S N) hq0 S.T hT'
    (fun r => X₁ (Real.toNNReal r)) (S.ρ N) hdens hS1.det Mart hS1.mart
  -- the transport moment on the first enlargement
  obtain ⟨hwm, hwmom⟩ := htm' S hS hMF hPos N hN P₁ (fun ω => X₀ (π₁ ω)) (fun t ω => W t (π₁ ω)) X₁ hX₁ hF₁ hE₁
  rw [hEeq] at hwmom
  set wI : Ω₁ → ℝ≥0∞ := fun ω => ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal
    ((torusWassersteinE 2 (empirical (X₁ (Real.toNNReal r) ω)) (withDensityReal (S.ρ N r))).toReal ^ 2) with hwI
  set cT : ℝ := Ctr (S.γ : ℝ) * qN S N with hcT
  have hcT0 : 0 ≤ cT := mul_nonneg hCtSpos.le hq0
  have hcostE : (fun ω => ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (Ctr (S.γ : ℝ) * qN S N *
      (torusWassersteinE 2 (empirical (X₁ (Real.toNNReal r) ω)) (withDensityReal (S.ρ N r))).toReal ^ 2)) =
      fun ω => ENNReal.ofReal cT * wI ω := by
    funext ω
    simp only [hwI]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun r => ?_
    rw [hcT, ENNReal.ofReal_mul hcT0] <;> rfl
  have hcostm : AEMeasurable (fun ω => ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (Ctr (S.γ : ℝ) * qN S N *
      (torusWassersteinE 2 (empirical (X₁ (Real.toNNReal r) ω)) (withDensityReal (S.ρ N r))).toReal ^ 2)) P₁ := by
    rw [hcostE]; exact hwm.const_mul _
  obtain ⟨-, hW⟩ := hs2 S hST (-1) hMF N hN (S.γ : ℝ) hm EV hEV P P₁ ℱ₁ X₁ η' Mart Z Bm Y₀ Y hS1
    (fun r ω => Ctr (S.γ : ℝ) * qN S N *
      (torusWassersteinE 2 (empirical (X₁ (Real.toNNReal r) ω)) (withDensityReal (S.ρ N r))).toReal ^ 2)
    hcplT hcostm
  rw [hlaw] at hW
  have hinit1 : ∫⁻ ω, ‖flucProc (S.γ : ℝ) (sigN S N) X₁ (S.ρ N) 0 ω - AN S N • η' ω‖ₑ ∂P₁ =
      ENNReal.ofReal (AN S N * S.initialError P N 1 X₀ η₀) := by
    have := hinit 1 (Or.inl rfl) hfin1
    simpa using this
  -- the cost integral
  set e : ℝ := (1 : ℝ) / max 2 ((d : ℝ) - S.s) with hedef
  have he0 : 0 ≤ e := by positivity
  have h2e : (2 : ℝ) / max 2 ((d : ℝ) - S.s) = 2 * e := by rw [hedef]; ring
  have hcostB : (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (Ctr (S.γ : ℝ) * qN S N *
      (torusWassersteinE 2 (empirical (X₁ (Real.toNNReal r) ω)) (withDensityReal (S.ρ N r))).toReal ^ 2)) ∂P₁) ^
        (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt (Ctr (b.γ : ℝ) * Ct) * Real.sqrt (qN S N) *
          (S.energyMoment P N X ^ e + (N : ℝ) ^ (-(1 : ℝ) / d))) := by
    rw [hcostE, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have h1 : ENNReal.ofReal cT * ∫⁻ ω, wI ω ∂P₁ ≤ ENNReal.ofReal (cT * (Ct * (S.energyMoment P N X ^ (2 * e) +
        (N : ℝ) ^ (-(1 : ℝ) / d) * (N : ℝ) ^ (-(1 : ℝ) / d)))) := by
      rw [ENNReal.ofReal_mul hcT0]
      have := hwmom
      rw [h2e, hn2] at this
      gcongr
    calc _ ≤ (ENNReal.ofReal (cT * (Ct * (S.energyMoment P N X ^ (2 * e) +
          (N : ℝ) ^ (-(1 : ℝ) / d) * (N : ℝ) ^ (-(1 : ℝ) / d))))) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow h1 (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt (cT * (Ct * (S.energyMoment P N X ^ (2 * e) +
          (N : ℝ) ^ (-(1 : ℝ) / d) * (N : ℝ) ^ (-(1 : ℝ) / d))))) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
            show (1 / 2 : ℝ) = (1 : ℝ) / 2 from rfl, ← Real.sqrt_eq_rpow]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have := sqrt_cost_bound2 (C := Ctr (b.γ : ℝ) * Ct) (q := qN S N) (E := S.energyMoment P N X)
            (n := (N : ℝ) ^ (-(1 : ℝ) / d)) (e := e) (by positivity) hq0 hE0 hn0
          refine le_trans (le_of_eq ?_) this
          rw [hcT, hCtS]
          congr 1
          ring
  refine ⟨?_, ?_⟩
  · -- the `W₁` estimate
    have hW1 := hW 1 (Or.inl rfl)
    have hinitp := hinit 1 (Or.inl rfl) hfin1
    have hB1 : (∫⁻ ω, Bm ω ^ (1 : ℝ) ∂P₁) ^ (1 / (1 : ℝ)) ≤
        ENNReal.ofReal (Cr * sigN S N * (S.T * S.energyMoment P N X)) := by
      simpa using hBm1
    have hx : 0 ≤ AN S N * S.initialError P N 1 X₀ η₀ := mul_nonneg hA0 hε1
    have hy : 0 ≤ sigN S N * S.energyMoment P N X := mul_nonneg hσ0 hE0
    have hz : 0 ≤ Real.sqrt (qN S N) * (S.energyMoment P N X ^ e + (N : ℝ) ^ (-(1 : ℝ) / d)) :=
      mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (Real.rpow_nonneg hE0 _) hn0)
    calc _ ≤ ENNReal.ofReal C2 * ENNReal.ofReal (AN S N * S.initialError P N 1 X₀ η₀) +
          ENNReal.ofReal (Cr * sigN S N * (S.T * S.energyMoment P N X)) +
          ENNReal.ofReal C2 * ENNReal.ofReal (Real.sqrt (Ctr (b.γ : ℝ) * Ct) * Real.sqrt (qN S N) *
            (S.energyMoment P N X ^ e + (N : ℝ) ^ (-(1 : ℝ) / d))) := by
          refine hW1.trans ?_
          rw [hinitp]
          gcongr
      _ = ENNReal.ofReal (C2 * (AN S N * S.initialError P N 1 X₀ η₀) +
          (Cr * S.T) * (sigN S N * S.energyMoment P N X) +
          (C2 * Real.sqrt (Ctr (b.γ : ℝ) * Ct)) * (Real.sqrt (qN S N) *
            (S.energyMoment P N X ^ e + (N : ℝ) ^ (-(1 : ℝ) / d)))) := by
          rw [← ENNReal.ofReal_mul hC20, ← ENNReal.ofReal_mul hC20, ← ENNReal.ofReal_add (by positivity)
            (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          rw [hST]
          ring
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hST]
          have hsq := mul_nonneg hC20 (Real.sqrt_nonneg (Ctr (b.γ : ℝ) * Ct))
          have hp1 := mul_nonneg hCr.le hbT
          have hCa : C2 ≤ C := by rw [hCdef]; linarith
          have hCb' : Cr * b.T ≤ C := by rw [hCdef]; linarith
          have hCc : C2 * Real.sqrt (Ctr (b.γ : ℝ) * Ct) ≤ C := by rw [hCdef]; linarith
          exact lin3 hx hy hz hCa hCb' hCc
  · -- the `W₂` estimate
    intro hE2 _ hfin2
    have hW2 := hW 2 (Or.inr rfl)
    have hinitp := hinit 2 (Or.inr rfl) hfin2
    have hB2 := hBm2 hE2
    have hE20 : 0 ≤ S.energyMoment2 P N X := by
      unfold GeneralSetup.energyMoment2
      exact Real.iSup_nonneg fun t => Real.sqrt_nonneg _
    have hε2 := initialError_nonneg S P 2 X₀ η₀
    have hx : 0 ≤ AN S N * S.initialError P N 2 X₀ η₀ := mul_nonneg hA0 hε2
    have hy : 0 ≤ sigN S N * S.energyMoment2 P N X := mul_nonneg hσ0 hE20
    have hz : 0 ≤ Real.sqrt (qN S N) * (S.energyMoment P N X ^ e + (N : ℝ) ^ (-(1 : ℝ) / d)) :=
      mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (Real.rpow_nonneg hE0 _) hn0)
    calc _ ≤ ENNReal.ofReal C2 * ENNReal.ofReal (AN S N * S.initialError P N 2 X₀ η₀) +
          ENNReal.ofReal (Cr * sigN S N * (S.T * S.energyMoment2 P N X)) +
          ENNReal.ofReal C2 * ENNReal.ofReal (Real.sqrt (Ctr (b.γ : ℝ) * Ct) * Real.sqrt (qN S N) *
            (S.energyMoment P N X ^ e + (N : ℝ) ^ (-(1 : ℝ) / d))) := by
          refine hW2.trans ?_
          rw [hinitp]
          gcongr
      _ = ENNReal.ofReal (C2 * (AN S N * S.initialError P N 2 X₀ η₀) +
          (Cr * S.T) * (sigN S N * S.energyMoment2 P N X) +
          (C2 * Real.sqrt (Ctr (b.γ : ℝ) * Ct)) * (Real.sqrt (qN S N) *
            (S.energyMoment P N X ^ e + (N : ℝ) ^ (-(1 : ℝ) / d)))) := by
          rw [← ENNReal.ofReal_mul hC20, ← ENNReal.ofReal_mul hC20, ← ENNReal.ofReal_add (by positivity)
            (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          rw [hST]
          ring
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hST]
          have hsq := mul_nonneg hC20 (Real.sqrt_nonneg (Ctr (b.γ : ℝ) * Ct))
          have hp1 := mul_nonneg hCr.le hbT
          have hCa : C2 ≤ C := by rw [hCdef]; linarith
          have hCb' : Cr * b.T ≤ C := by rw [hCdef]; linarith
          have hCc : C2 * Real.sqrt (Ctr (b.γ : ℝ) * Ct) ≤ C := by rw [hCdef]; linarith
          exact lin3 hx hy hz hCa hCb' hCc

/-- **`general_fluctuation` (Theorem 2.1, gradient clause) from the sub-packet statements** (PROVED, conditional on the sorried
packets; the type is the frozen statement, checked by the `example` below). -/
theorem gf_general_fluctuation_of_packets (b : GeneralBounds d) :
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
          C * (A * S.initialError P N 1 X₀ η₀ + σ * 𝔈 + q * (Real.sqrt 𝔈 + (N : ℝ) ^ (-(2 : ℝ) / d))) ∧
      wassersteinE 1 Ξ YN ≤ ENNReal.ofReal
          (C * (A * S.initialError P N 1 X₀ η₀ + σ * 𝔈 +
            Real.sqrt q * (𝔈 ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d)))) ∧
      (S.EnergyMoment2Finite P N X →
        Integrable (fun ω => ‖flucPath S.γ S.T σ X (S.ρ N) ω‖ ^ 2) P →
        S.InitialErrorFinite P N 2 X₀ η₀ →
        wassersteinE 2 Ξ YN ≤ ENNReal.ofReal
          (C * (A * S.initialError P N 2 X₀ η₀ + σ * S.energyMoment2 P N X +
            Real.sqrt q * (𝔈 ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d))))) := by
  obtain ⟨K, hK0, hev⟩ := gf_ev_grad b
  obtain ⟨C₀min, hcore⟩ := gf_core b (-1) (fun S => S.PosDensityWith b.c) (fun S => (S.γ : ℝ))
    (fun S => le_rfl) (fun S x => x) K
    (fun S hS hMF hPos N => by
      obtain ⟨EV, hEV⟩ := hev S hS hMF hPos N
      exact ⟨EV, hEV, fun x => by rw [hEV.j_eq, embed_self]⟩)
  refine ⟨C₀min, fun C₀ hC₀ => ?_⟩
  obtain ⟨C, hC, h⟩ := hcore C₀ hC₀
  refine ⟨C, hC, ?_⟩
  intro S hS hMF hPos N hN Ω _ P _ X₀ W hW X hX hF hE η₀ hη hind hfin Y hY
  exact h S hS hMF hPos N hN P X₀ W X hX hF hE η₀ hη hind hfin Y hY

example := (@gf_general_fluctuation_of_packets : type_of% @HRS.GeneralSetup.general_fluctuation)

/-- **`general_fluctuation_matrix` (Theorem 2.1, general-matrix clause) from the sub-packet statements** (PROVED, conditional on the
sorried packets). -/
theorem gf_general_fluctuation_matrix_of_packets (b : GeneralBounds d) (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : Torus.SymNonpos M) (K : ℝ) :
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
          C * (A * S.initialError P N 1 X₀ η₀ + σ * 𝔈 + q * (Real.sqrt 𝔈 + (N : ℝ) ^ (-(2 : ℝ) / d))) ∧
      wassersteinE 1 Ξ YN ≤ ENNReal.ofReal
          (C * (A * S.initialError P N 1 X₀ η₀ + σ * 𝔈 +
            Real.sqrt q * (𝔈 ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d)))) ∧
      (S.EnergyMoment2Finite P N X →
        Integrable (fun ω => ‖flucPath ((S.γ : ℝ) + 2) S.T σ X (S.ρ N) ω‖ ^ 2) P →
        S.InitialErrorFinite P N 2 X₀ η₀ →
        wassersteinE 2 Ξ YN ≤ ENNReal.ofReal
          (C * (A * S.initialError P N 2 X₀ η₀ + σ * S.energyMoment2 P N X +
            Real.sqrt q * (𝔈 ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d))))) := by
  obtain ⟨K', hK0, hev⟩ := gf_ev_mat b M hM K
  obtain ⟨C₀min, hcore⟩ := gf_core b M (fun S => S.AdjointInput M K) (fun S => (S.γ : ℝ) + 2)
    (fun S => by linarith) (fun S => NegSobolev.embed ((S.γ : ℝ) + 2)) K'
    (fun S hS hMF hAdj N => by
      obtain ⟨EV, hEV⟩ := hev S hS hMF hAdj N
      exact ⟨EV, hEV, fun x => hEV.j_eq x⟩)
  refine ⟨C₀min, fun C₀ hC₀ => ?_⟩
  obtain ⟨C, hC, h⟩ := hcore C₀ hC₀
  refine ⟨C, hC, ?_⟩
  intro S hS hMF hAdj N hN Ω _ P _ X₀ W hW X hX hF hE η₀ hη hind hfin Y hY
  exact h S hS hMF hAdj N hN P X₀ W X hX hF hE η₀ hη hind hfin Y hY

example := (@gf_general_fluctuation_matrix_of_packets : type_of% @HRS.GeneralSetup.general_fluctuation_matrix)

/-- **`general_fluctuation_transport` (Theorem 2.1, transport improvement) from the sub-packet statements** (PROVED, conditional on
the sorried packets): the minimum of the trace-norm coupling bound (`gf_core`) and the transport coupling bound (`gf_core_transport`). -/
theorem gf_general_fluctuation_transport_of_packets (b : GeneralBounds d) :
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
      let cov := Real.sqrt q * min (𝔈 ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d))
        (𝔈 ^ ((1 : ℝ) / max 2 ((d : ℝ) - S.s)) + (N : ℝ) ^ (-(1 : ℝ) / d))
      let Ξ := law P (flucPath S.γ S.T σ X (S.ρ N))
      let YN := law P (toPath S.γ S.T Y)
      wassersteinE 1 Ξ YN ≤ ENNReal.ofReal
          (C * (A * S.initialError P N 1 X₀ η₀ + σ * 𝔈 + cov)) ∧
      (S.EnergyMoment2Finite P N X →
        Integrable (fun ω => ‖flucPath S.γ S.T σ X (S.ρ N) ω‖ ^ 2) P →
        S.InitialErrorFinite P N 2 X₀ η₀ →
        wassersteinE 2 Ξ YN ≤ ENNReal.ofReal
          (C * (A * S.initialError P N 2 X₀ η₀ + σ * S.energyMoment2 P N X + cov))) := by
  obtain ⟨K, hK0, hev⟩ := gf_ev_grad b
  obtain ⟨C₀a, hcore⟩ := gf_core b (-1) (fun S => S.PosDensityWith b.c) (fun S => (S.γ : ℝ))
    (fun S => le_rfl) (fun S x => x) K
    (fun S hS hMF hPos N => by
      obtain ⟨EV, hEV⟩ := hev S hS hMF hPos N
      exact ⟨EV, hEV, fun x => by rw [hEV.j_eq, embed_self]⟩)
  obtain ⟨C₀b, hcoreT⟩ := gf_core_transport b
  refine ⟨max C₀a C₀b, fun C₀ hC₀ => ?_⟩
  obtain ⟨C₁, hC₁, h₁⟩ := hcore C₀ (le_trans (le_max_left _ _) hC₀)
  obtain ⟨C₂, hC₂, h₂⟩ := hcoreT C₀ (le_trans (le_max_right _ _) hC₀)
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, ?_⟩
  intro S hS hMF hPos N hN Ω _ P _ X₀ W hW X hX hF hE η₀ hη hind hfin Y hY
  have hq0 := qN_nonneg S N
  have hσ0 := sigN_nonneg S N
  have hA0 := AN_nonneg S N
  have hE0 := energyMoment_nonneg S (-1) hMF N hN P X₀ W X hX hF hE
  have hε1 := initialError_nonneg S P 1 X₀ η₀
  have hn0 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / d) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  obtain ⟨-, hW1a, hW2a⟩ := h₁ S hS hMF hPos N hN P X₀ W X hX hF hE η₀ hη hind hfin Y hY
  obtain ⟨hW1b, hW2b⟩ := h₂ S hS hMF hPos N hN P X₀ W X hX hF hE η₀ hη hind hfin Y hY
  dsimp only
  have hmax1 : C₁ ≤ max C₁ C₂ := le_max_left _ _
  have hmax2 : C₂ ≤ max C₁ C₂ := le_max_right _ _
  refine ⟨?_, fun hE2 hI hfin2 => ?_⟩
  · rcases le_total (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d))
        (S.energyMoment P N X ^ ((1 : ℝ) / max 2 ((d : ℝ) - S.s)) + (N : ℝ) ^ (-(1 : ℝ) / d)) with h | h
    · rw [min_eq_left h]
      refine hW1a.trans (ENNReal.ofReal_le_ofReal ?_)
      have hz : 0 ≤ AN S N * S.initialError P N 1 X₀ η₀ + sigN S N * S.energyMoment P N X +
          Real.sqrt (qN S N) * (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d)) := by
        have := Real.rpow_nonneg hE0 ((1 : ℝ) / 4)
        positivity
      exact mul_le_mul_of_nonneg_right hmax1 hz
    · rw [min_eq_right h]
      refine hW1b.trans (ENNReal.ofReal_le_ofReal ?_)
      have hz : 0 ≤ AN S N * S.initialError P N 1 X₀ η₀ + sigN S N * S.energyMoment P N X +
          Real.sqrt (qN S N) * (S.energyMoment P N X ^ ((1 : ℝ) / max 2 ((d : ℝ) - S.s)) +
            (N : ℝ) ^ (-(1 : ℝ) / d)) := by
        have := Real.rpow_nonneg hE0 ((1 : ℝ) / max 2 ((d : ℝ) - S.s))
        positivity
      exact mul_le_mul_of_nonneg_right hmax2 hz
  · have hE20 : 0 ≤ S.energyMoment2 P N X := by
      unfold GeneralSetup.energyMoment2
      exact Real.iSup_nonneg fun t => Real.sqrt_nonneg _
    have hε2 := initialError_nonneg S P 2 X₀ η₀
    rcases le_total (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d))
        (S.energyMoment P N X ^ ((1 : ℝ) / max 2 ((d : ℝ) - S.s)) + (N : ℝ) ^ (-(1 : ℝ) / d)) with h | h
    · rw [min_eq_left h]
      refine (hW2a hE2 hI hfin2).trans (ENNReal.ofReal_le_ofReal ?_)
      have hz : 0 ≤ AN S N * S.initialError P N 2 X₀ η₀ + sigN S N * S.energyMoment2 P N X +
          Real.sqrt (qN S N) * (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d)) := by
        have := Real.rpow_nonneg hE0 ((1 : ℝ) / 4)
        positivity
      exact mul_le_mul_of_nonneg_right hmax1 hz
    · rw [min_eq_right h]
      refine (hW2b hE2 hI hfin2).trans (ENNReal.ofReal_le_ofReal ?_)
      have hz : 0 ≤ AN S N * S.initialError P N 2 X₀ η₀ + sigN S N * S.energyMoment2 P N X +
          Real.sqrt (qN S N) * (S.energyMoment P N X ^ ((1 : ℝ) / max 2 ((d : ℝ) - S.s)) +
            (N : ℝ) ^ (-(1 : ℝ) / d)) := by
        have := Real.rpow_nonneg hE0 ((1 : ℝ) / max 2 ((d : ℝ) - S.s))
        positivity
      exact mul_le_mul_of_nonneg_right hmax2 hz

example := (@gf_general_fluctuation_transport_of_packets : type_of% @HRS.GeneralSetup.general_fluctuation_transport)

end HRS.GF
