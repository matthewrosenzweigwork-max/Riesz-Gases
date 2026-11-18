import HRS.MH.WpSpec
import HRS.Main.GFFinal4
import HRS.Uniform.Comparison

/-!
# `general_fluctuation_Wp` (Comparison.lean): the remaining packets (statement-only; all `sorry`)

See `HRS/MH/WpPlan.md` for the packet graph, the `EnergyMomentFinite` analysis and the statement checks.
Already proved elsewhere (not repeated): `maximal_estimate_meas_p` (P1, WpP1.lean) and `gff_initial_term_eq_lintegral` (P3a, WpP3a.lean);
their statements are in `HRS/MH/WpSpec.lean`.

Design (summary).  Everything is at the level of `ℝ≥0∞` `lintegral`s; **no hypothesis `S.EnergyMomentFinite` and no real-valued
`energyMoment` is used anywhere**.  The only place where finiteness of `E_ω := ∫_0^T 𝓔_N^t(ω) dt` enters is the pathwise remainder bound,
which needs `r ↦ 𝓔_N(X_r, r)` a.s. integrable on `[0,T]`; this is `E_ω < ∞` a.s., which follows from `En < ∞` (`En^p = ∫⁻ E_ω^p`, `p > 0`)
and the measurability of `ω ↦ E_ω` (packet `gfwp_energy_aux`).  If `En = ∞` the right side of the theorem is `∞` because `σ_N > 0`
(packet `gfwp_sigN_pos`), so the theorem is trivial there (packet `general_fluctuation_Wp_core`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.Wp

open HRS HRS.GF HRS.Uniform HRS.Uniform.Kot

variable {d : ℕ}

/-! ### Small packets -/

/-- **WP-SIGMA** (size S, about 20 lines).  `σ_N > 0`: `σ_N = κ_N > 0` if `β_N⁻¹ = 0`, else `min κ_N √(N/β_N⁻¹)` with `β_N⁻¹ > 0`, `N ≥ 1`.
Route: `unfold sigN sigmaScale; split_ifs`, `S.hκ N`, `S.hinvβ N` (Setup.lean:293, :303), `lt_min`, `Real.sqrt_pos`, `div_pos`, `Nat.cast_pos`.
Existing: `sigN_nonneg` (GFSpec2.lean:135) has the same proof with `≤`; `sigN` is an `abbrev` (GFSpec1.lean:56). -/
theorem gfwp_sigN_pos (S : GeneralSetup d) (N : ℕ) (hN : 1 ≤ N) : 0 < sigN S N := by
  sorry

/-- **WP-ENERGY** (size S, about 80 lines).  The `ℝ≥0∞`-level replacement of `gf_energy_integral_moment_proof` (GFB2Aux1.lean:245), WITHOUT
`EnergyMomentFinite`.  `E_ω := ∫⁻_{[0,T]} ofReal 𝓔_N^r(ω) dr`.  (1) a.s. `𝓔 ≥ 0` on `[0,T]`; (2) `ω ↦ E_ω` is measurable; (3) a.s., if `E_ω < ∞`
then `r ↦ 𝓔_N^r(ω)` is integrable on `[0,T]` and `ofReal (∫ 𝓔) = E_ω`.
Route (all pieces exist; this is the proof of `gf_energy_integral_moment_proof` with `hE` deleted):
(1) = the `hnn` block of GFB2Aux1.lean:262-265 (`S.energy_nonneg` at `hX.no_collision`).
(2) `gfb2_G_meas S M hMF N ℱ X hFil.progressive` (GFB2Aux3.lean:44) gives joint measurability of `gfb2_G`; `gfb2_G_eq` (GFB2Aux3.lean:52) identifies
`gfb2_G S N X r ω = S.energyCompletion N (X (toNNReal r) ω) r` for `r ∈ Icc 0 T`; then `setLIntegral_congr_fun` and
`((ENNReal.measurable_ofReal.comp hGm).comp measurable_swap).lintegral_prod_right'` exactly as `hmeasL` in GFB2Aux1.lean:151-152.
(3) For nonneg `f` with measurable section and `∫⁻ ofReal f < ∞`: `Integrable` (see `hfin`/`HasFiniteIntegral` block, GFB2Aux1.lean:161-166) and
`ofReal_integral_eq_lintegral_ofReal` (GFB2Aux1.lean:130). -/
theorem gfwp_energy_aux (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (hMF : S.MFHypM M) (N : ℕ)
    (hN : 2 ≤ N) {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hX : IsStrongSolution P (S.dynM M N) S.T X₀ W X)
    (hF : ∃ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) :
    (∀ᵐ ω ∂P, ∀ r ∈ Set.Icc (0 : ℝ) S.T, 0 ≤ S.energyCompletion N (X (Real.toNNReal r) ω) r) ∧
    Measurable (fun ω => ∫⁻ r in Set.Icc (0 : ℝ) S.T,
      ENNReal.ofReal (S.energyCompletion N (X (Real.toNNReal r) ω) r)) ∧
    (∀ᵐ ω ∂P, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (S.energyCompletion N (X (Real.toNNReal r) ω) r)) < ⊤ →
      IntegrableOn (fun r => S.energyCompletion N (X (Real.toNNReal r) ω) r) (Set.Icc (0 : ℝ) S.T) ∧
      ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) S.T, S.energyCompletion N (X (Real.toNNReal r) ω) r) =
        ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (S.energyCompletion N (X (Real.toNNReal r) ω) r)) := by
  sorry

/-- **WP-TCOST** (size S, about 50 lines).  Measurability of the transport-cost integrals, WITHOUT `EnergyMomentFinite` (this is the first
conjunct of `gfb2_transport_core`, GFB2Aux5.lean:58, which never used `hE`).  Used (a) to move the cost between `Ω₁` and `Ω`
(`lintegral_comp_mp`, GFSpec5.lean:64) and (b) as the `AEMeasurable` hypothesis of stage 2.
Route: lines GFB2Aux5.lean:77-99 verbatim: `hZ := gfb2_progressive_meas ℱ X hFil.progressive hT` (GFB2Aux1.lean:233), `gfb2_W_meas S M hMF N _`
(GFB2Aux4.lean:194) composed with `hZ.prodMk measurable_fst`, `hWm.ennreal_toReal.pow_const 2`, `ENNReal.measurable_ofReal`,
`setLIntegral_congr_fun` with `Q54c.clampT_of_mem`, `Measurable.lintegral_prod_right'`.  The second conjunct is the same with `hWm.pow_const 2`
and no `toReal`. -/
theorem gfwp_transport_cost_meas (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (hMF : S.MFHypM M) (N : ℕ)
    (hN : 2 ≤ N) {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hX : IsStrongSolution P (S.dynM M N) S.T X₀ W X)
    (hF : ∃ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) :
    Measurable (fun ω => ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal
      ((torusWassersteinE 2 (empirical (X (Real.toNNReal r) ω)) (withDensityReal (S.ρ N r))).toReal ^ 2)) ∧
    Measurable (fun ω => ∫⁻ r in Set.Icc (0 : ℝ) S.T,
      torusWassersteinE 2 (empirical (X (Real.toNNReal r) ω)) (withDensityReal (S.ρ N r)) ^ 2) := by
  sorry

/-- **WP-REM** (size S, about 125 lines, mechanical).  `gff_remainder_bound` (GFFinal1.lean:59) with the hypothesis `S.EnergyMomentFinite P N X`
replaced by the two facts it was used for (and nothing else): a.s. nonnegativity and a.s. time-integrability of the completed energy.
Route: copy GFFinal1.lean:59-195 and replace the single line `obtain ⟨hen0, henI, -, -⟩ := gf_energy_integral_moment_proof ... hE`
(GFFinal1.lean:89) by `hen0 := hnn`, `henI := hint`.  Nothing else in the proof mentions `hE`: the packets `gf_mild_identity_proof` (GFB2Aux6.lean:59),
`gf_pair_identification_proof` (GFB3Tie.lean:13), `gf_remainder_pointwise_proof` (GFB2Aux9.lean:44), `gf_norm_of_pairings_proof` (GFB1Aux2.lean:259),
`gf_smooth_mem_proof` (GFB1Aux1.lean:100) take no energy-moment hypothesis. -/
theorem gff_remainder_bound_ae (b : GeneralBounds d) (M : Matrix (Fin d) (Fin d) ℝ) (K : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHypM M → ∀ N : ℕ, 2 ≤ N →
      ∀ m : ℝ, (S.γ : ℝ) ≤ m →
      ∀ EV : EvolData (NegSobolev d (S.γ : ℝ)) (NegSobolev d m), GFEvo S M N m K EV →
      ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStrongSolution P (S.dynM M N) S.T X₀ W X →
        ∀ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X →
        (∀ᵐ ω ∂P, ∀ r ∈ Set.Icc (0 : ℝ) S.T, 0 ≤ S.energyCompletion N (X (Real.toNNReal r) ω) r) →
        (∀ᵐ ω ∂P, IntegrableOn (fun r => S.energyCompletion N (X (Real.toNNReal r) ω) r) (Set.Icc (0 : ℝ) S.T)) →
        ∀ Mart : ℝ → Ω → NegSobolev d (S.γ : ℝ),
        IsHilbertItoIntegral P ℱ W'
          (noiseIntegrand (S.γ : ℝ) (noiseScale S N) (fun r => X (Real.toNNReal r))) Mart →
        ∀ Z : ℝ → Ω → NegSobolev d m,
        (∀ t ∈ Set.Icc (0 : ℝ) S.T, IsStochConv P EV.VE EV.j Mart 0 t (Z t)) →
        (∀ t ∈ Set.Icc (0 : ℝ) S.T, Measurable (Z t)) →
        (∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 S.T)) →
        (∀ᵐ ω ∂P, Continuous fun t : Set.Icc (0 : ℝ) S.T => flucProc m (sigN S N) X (S.ρ N) t ω) →
        ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) S.T,
          ‖flucProc m (sigN S N) X (S.ρ N) t ω -
              EV.VE t 0 (EV.j (flucProc (S.γ : ℝ) (sigN S N) X (S.ρ N) 0 ω)) - Z t ω‖ ≤
            C * sigN S N * ∫ r in (0 : ℝ)..t, S.energyCompletion N (X (Real.toNNReal r) ω) r := by
  sorry

/-! ### P2: the order-`p` Wasserstein comparison -/

/-- **P2** (size M, about 200 lines).  `gfb4_wasserstein_comparison_meas` (GFB4Aux13.lean:86) for every `p ≥ 2` instead of `p ∈ {1,2}`; the cost term is the
`L^p(P)` norm of `(∫_0^T cost)^{1/2}`, i.e. `(∫⁻ (∫⁻ cost)^{p/2})^{1/p}`.  (For `p = 2` this is `(∫⁻∫⁻ cost)^{1/2}`, the old statement.)
Hypotheses identical to the old statement (so stage 2 supplies them verbatim: `hMG`, `hcost`).
Route: copy GFB4Aux13.lean:86-280 (the `Aux` section lines 24-83 are reused, not copied).  Changes: (i) `maximal_estimate_meas T K hT` ->
`maximal_estimate_meas_p T K p hT hp` (WpSpec.lean, P1; the old one is `Q45.maximal_estimate_meas`); the sup bound `hsup` becomes
`∫⁻ (⨆ ‖Zd t ω‖ₑ)^p ≤ ofReal Cm * ∫⁻ (∫⁻ ofReal (cost r ω))^(p/2)` (same `calc`, with `ENNReal.rpow_le_rpow` for the inner
monotonicity `∫⁻ ofReal‖Sd‖₁ ≤ ∫⁻ ofReal cost`, `p/2 ≥ 0`); (ii) `hcpart` is now
`(∫⁻ c^p)^(1/p) ≤ (ofReal Cm * I)^(1/p) = ofReal Cm ^ (1/p) * I^(1/p) ≤ ofReal C * I^(1/p)`, no `gfb4_lp_le_two` (GFB4Aux12.lean:19) needed; use
`ENNReal.mul_rpow_of_nonneg`, and `Cm ^ (1/p) ≤ max 1 Cm` (`Real.rpow_le_rpow_of_exponent_le`/`Real.rpow_le_one`, or
`ENNReal.ofReal_rpow_of_nonneg`); take the constant `C := max (detConst T K) (max 1 Cm)`; (iii) Minkowski `hMink` is unchanged (uses `1 ≤ p` only,
`ENNReal.lintegral_Lp_add_le`); `hapart` = `gfb4_lp_const_mul` (GFB4Aux12.lean:29), `hp0 : 0 < p`.
Math check: `E sup‖Z_d‖^p ≤ C_p E(∫‖Sd‖₁)^{p/2}` is the Hilbert BDG + dissipative-evolution maximal estimate (P1); the Minkowski step needs `p ≥ 1`. -/
theorem gfwp_wasserstein_comparison (T K p : ℝ) (hT : 0 ≤ T) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℝ mΩ)
        (H E : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
        [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
        [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
        (S : EvolData H E) (_ : S.MaxHyp T K)
        (X₀ X₀' : Ω → H) (_ : Measurable X₀) (_ : Measurable X₀') (M G : ℝ → Ω → H)
        (_ : ∀ t, Measurable (M t)) (_ : ∀ t, Measurable (G t))
        (Sd : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)) (cost : ℝ → Ω → ℝ)
        (_ : IsHilbertMartingaleWithCovariation P ℱ T (fun τ ω => M (min τ T) ω - G (min τ T) ω)
          (fun r ω => if r ≤ T then Sd r ω else 0))
        (_ : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 ≤ r → r ≤ T → traceNormForm (Sd r ω) ≤ cost r ω)
        (Z Zb R : ℝ → Ω → E)
        (_ : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P S.VE S.j M 0 t (Z t))
        (_ : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P S.VE S.j G 0 t (Zb t))
        (_ : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 T))
        (_ : ∀ᵐ ω ∂P, ContinuousOn (fun t => Zb t ω) (Set.Icc 0 T))
        (_ : ∀ᵐ ω ∂P, ContinuousOn (fun t => R t ω) (Set.Icc 0 T))
        (_ : ∀ t, Measurable (Z t)) (_ : ∀ t, Measurable (Zb t)) (_ : ∀ t, Measurable (R t))
        (X Xb : ℝ → Ω → E)
        (_ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ω, X t ω = S.VE t 0 (S.j (X₀ ω)) + Z t ω + R t ω)
        (_ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ω, Xb t ω = S.VE t 0 (S.j (X₀' ω)) + Zb t ω),
        wassersteinE p (law P (windowPath 0 T X)) (law P (windowPath 0 T Xb)) ≤
          ENNReal.ofReal C * (∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ^ p ∂P) ^ (1 / p) +
            (∫⁻ ω, ‖windowPath 0 T R ω‖ₑ ^ p ∂P) ^ (1 / p) +
            ENNReal.ofReal C *
              (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (cost r ω)) ^ (p / 2) ∂P) ^ (1 / p) := by
  sorry

/-! ### P3b: stage 1 at order `p`, without `EnergyMomentFinite` -/

/-- **P3b** (size M, about 200 lines; the packet with the most plumbing).  `gff_stage1` (GFFinal2.lean:64) at order `p > 0`, WITHOUT `hfin`, WITHOUT
`EnergyMomentFinite`, with the finiteness of `E_ω = ∫_0^T 𝓔_N^r(ω) dr` replaced by the a.s. hypothesis `hEfin` (which `En < ∞` gives).  The remainder bound is
the pathwise `Bm_ω = ofReal (Cr σ_N) * E_ω` (an `ℝ≥0∞`-valued bound; `ofReal (Cr σ) * ofReal (∫ 𝓔) = ofReal (Cr σ) * E_ω` on `{E_ω < ∞}`), and the
outputs at order `p` are the initial term (via P3a) and `‖Bm‖_{L^p(P₁)} ≤ Cr σ ‖E‖_{L^p(P)} = Cr σ En`.
Route: copy GFFinal2.lean:64-208 and change:
(a) delete `S.EnergyMomentFinite` binders/outputs and the `energyMoment` equalities (and `hBm2`, `energyMoment2_comp`);
(b) replace `gf_energy_integral_moment_proof ... hE₁` by `gfwp_energy_aux S M hMF N hN P₁ ... hX₁ ⟨ℱ₁,W'₁,hF₁⟩` (P₁-version) giving `hnn`, `hmeasE₁`, `hintE₁`; the a.s.
finiteness on `P₁` is `hπ₁.quasiMeasurePreserving.ae hEfin` (the integrand on `Ω₁` is literally the one on `Ω` composed with `π₁`);
a.s. `IntegrableOn` follows from `hintE₁`;
(c) `gff_remainder_bound` -> `gff_remainder_bound_ae` (WP-REM) with those two a.s. facts; same `Mart`, `Z` (from `Q45.maximal_estimate_meas S.T K hT`, only its
first four conjuncts are used), `gf_measurable_modification_proof`, `gf_fluc_continuous_proof`, `gf_particle_martingale_proof`, `gf_detCovDensity_proof`;
(d) `Bm ω := ENNReal.ofReal (Cr * sigN S N) * ∫⁻ r in Icc 0 T, ofReal (𝓔 (X₁ r ω) r)`; `hbound` on `{E_ω < ∞}`:
`‖R_t‖ₑ = ofReal ‖R_t‖ ≤ ofReal (Cr σ ∫_0^t 𝓔) ≤ ofReal (Cr σ) * ofReal (∫_{Icc} 𝓔) = Bm ω` (`setIntegral_mono_set`, as GFFinal2.lean:144-149, then the
equation of `gfwp_energy_aux` (3)); `bound_meas` = `hmeasE₁.const_mul _`;
(e) the `Bm` output: `gfb4_lp_const_mul` (GFB4Aux12.lean:29) and `lintegral_comp_mp` (GFSpec5.lean:64) with `(hmeasE.pow_const p).aemeasurable`, `hmeasE` from
`gfwp_energy_aux` on `Ω`;
(f) the initial term: `gff_initial_term_eq_lintegral` (WpSpec.lean, P3a) with `hlawI` from `gf_init_enlargement_proof` (GFSpec3Tie.lean:20); no `hfin`.
`gf_init_enlargement_proof`, `isStrongSolution_comp` (GFSpec3.lean:47) are unchanged. -/
theorem gff_stage1_p (b : GeneralBounds d) (M : Matrix (Fin d) (Fin d) ℝ) (K p : ℝ) (hp : 0 < p) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ Cr : ℝ, 0 < Cr ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHypM M → ∀ N : ℕ, 2 ≤ N →
      ∀ m : ℝ, (S.γ : ℝ) ≤ m →
      ∀ EV : EvolData (NegSobolev d (S.γ : ℝ)) (NegSobolev d m), GFEvo S M N m K EV →
      ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStrongSolution P (S.dynM M N) S.T X₀ W X →
        (∃ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        (∀ᵐ ω ∂P, (∫⁻ r in Set.Icc (0 : ℝ) S.T,
          ENNReal.ofReal (S.energyCompletion N (X (Real.toNNReal r) ω) r)) < ⊤) →
        ∀ (η₀ : Ω → NegSobolev d (S.γ : ℝ)), Measurable η₀ →
        IndepFun (fun ω => (X₀ ω, η₀ ω)) (fun ω => fun t => W t ω) P →
        ∀ (Y₀ : Ω → NegSobolev d m), Measurable Y₀ → (∀ ω, Y₀ ω = EV.j (AN S N • η₀ ω)) →
        ∀ Y : ℝ → Ω → NegSobolev d m,
        IsLinearFluctuationSolution P (S.dynM M N) (S.ρ N) m (qN S N) S.T Y₀ Y →
        ∃ (Ω₁ : Type) (mΩ₁ : MeasurableSpace Ω₁) (P₁ : Measure Ω₁) (_ : IsProbabilityMeasure P₁)
          (π₁ : Ω₁ → Ω) (_ : MeasurePreserving π₁ P₁ P) (ℱ₁ : Filtration ℝ mΩ₁)
          (η' : Ω₁ → NegSobolev d (S.γ : ℝ)) (Mart : ℝ → Ω₁ → NegSobolev d (S.γ : ℝ))
          (Z : ℝ → Ω₁ → NegSobolev d m) (Bm : Ω₁ → ℝ≥0∞),
          Stage1 S M N m K EV P P₁ ℱ₁ (fun t ω => X t (π₁ ω)) η' Mart Z Bm Y₀ Y ∧
          IsStrongSolution P₁ (S.dynM M N) S.T (fun ω => X₀ (π₁ ω)) (fun t ω => W t (π₁ ω))
            (fun t ω => X t (π₁ ω)) ∧
          (∃ (ℱ' : Filtration ℝ mΩ₁) (W'' : ℝ≥0 → Ω₁ → (Fin N × Fin d) → ℝ),
            IsFilteredSolution P₁ ℱ' W'' (fun t ω => W t (π₁ ω)) (fun t ω => X t (π₁ ω))) ∧
          law P₁ (flucPath m S.T (sigN S N) (fun t ω => X t (π₁ ω)) (S.ρ N)) =
            law P (flucPath m S.T (sigN S N) X (S.ρ N)) ∧
          (∫⁻ ω, ‖flucProc (S.γ : ℝ) (sigN S N) (fun t ω => X t (π₁ ω)) (S.ρ N) 0 ω -
              AN S N • η' ω‖ₑ ^ p ∂P₁) ^ (1 / p) =
            ENNReal.ofReal (AN S N) * (∫⁻ ω, ‖S.κ N • NegSobolev.ofMeasureDiff (S.γ : ℝ) (empirical (X₀ ω))
              (withDensityReal (S.ρ N 0)) - η₀ ω‖ₑ ^ p ∂P) ^ (1 / p) ∧
          (∫⁻ ω, Bm ω ^ p ∂P₁) ^ (1 / p) ≤
            ENNReal.ofReal (Cr * sigN S N) * (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T,
              ENNReal.ofReal (S.energyCompletion N (X (Real.toNNReal r) ω) r)) ^ p ∂P) ^ (1 / p) := by
  sorry

/-! ### P4: stage 2 at order `p` -/

/-- **P4** (size M, about 230 lines; compile-heavy, use `set_option maxHeartbeats 800000 in` as GFFinal1.lean:162).  The Wasserstein part of `gff_stage2`
(GFFinal1.lean:164) for every `p ≥ 2`, for an arbitrary coupling and cost: `W_p(Law Ξ, Law Y) ≤ C ‖Ξ⁰ - Aη'‖_{L^p} + ‖Bm‖_{L^p} + C ‖(∫ cost)^{1/2}‖_{L^p}`.
Route: copy GFFinal1.lean:164-407 and DELETE everything about `smoothDist` (`smooth_path_comparison_proof`, `hsmooth`, `hI1`-`hI3` and the first conjunct),
keep: second enlargement, `hGb`, `Zb` (via `maximal_estimate_meas` -- the old order-2 one is fine here, only the first four conjuncts are used), `hXform`, `hlaw1`,
`hL`/`hL'` (`gf_law_identification_proof`), `hD`/`hSd` (`gf_coupling_difference`, `gf_coupling_cost_le`, GFSpec4.lean:266, :275).  Replace the single use of
`hwp1`/`hwp2` by `gfwp_wasserstein_comparison T K p hT hp` (P2) and generalise `hconv` (GFFinal1.lean:340-364) to exponent `p`:
the third term transfers with `lintegral_comp_mp hπ (f := fun ω => (∫⁻ r in Icc, ofReal (cost r ω)) ^ (p / 2)) (hcostm.pow_const _)`.
The constant is `Cw` of P2 (one constant, no `max` needed). -/
theorem gff_stage2_p (T K p : ℝ) (hT : 0 ≤ T) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : GeneralSetup d), S.T = T → ∀ (M : Matrix (Fin d) (Fin d) ℝ), S.MFHypM M → ∀ (N : ℕ), 2 ≤ N →
      ∀ (m : ℝ), (S.γ : ℝ) ≤ m →
      ∀ (EV : EvolData (NegSobolev d (S.γ : ℝ)) (NegSobolev d m)), GFEvo S M N m K EV →
      ∀ {Ω Ω₁ : Type} [mΩ : MeasurableSpace Ω] [mΩ₁ : MeasurableSpace Ω₁]
        (P : Measure Ω) [IsProbabilityMeasure P] (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
        (ℱ₁ : Filtration ℝ mΩ₁) (X₁ : ℝ≥0 → Ω₁ → Config d N)
        (η' : Ω₁ → NegSobolev d (S.γ : ℝ)) (Mart : ℝ → Ω₁ → NegSobolev d (S.γ : ℝ))
        (Z : ℝ → Ω₁ → NegSobolev d m) (Bm : Ω₁ → ℝ≥0∞) (Y₀ : Ω → NegSobolev d m)
        (Y : ℝ → Ω → NegSobolev d m),
        Stage1 S M N m K EV P P₁ ℱ₁ X₁ η' Mart Z Bm Y₀ Y →
        ∀ cost : ℝ → Ω₁ → ℝ,
        AdaptedGaussianCoupling P₁ ℱ₁ (ENNReal.ofReal S.T) ⟨ℱ₁ 0, le_rfl⟩ Mart
          (fun r ω => covForm (S.γ : ℝ) (qN S N) (empirical (X₁ (Real.toNNReal r) ω)))
          (covDensT (S.γ : ℝ) (qN S N) S.T (S.ρ N)) (· ≤ ·) cost →
        AEMeasurable (fun ω => ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (cost r ω)) P₁ →
          wassersteinE p (law P₁ (flucPath m S.T (sigN S N) X₁ (S.ρ N))) (law P (toPath m S.T Y)) ≤
            ENNReal.ofReal C * (∫⁻ ω, ‖flucProc (S.γ : ℝ) (sigN S N) X₁ (S.ρ N) 0 ω -
                AN S N • η' ω‖ₑ ^ p ∂P₁) ^ (1 / p) +
              (∫⁻ ω, Bm ω ^ p ∂P₁) ^ (1 / p) +
              ENNReal.ofReal C * (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (cost r ω)) ^ (p / 2) ∂P₁) ^
                (1 / p) := by
  sorry

/-! ### P5a, P5b: the two bounds (under `En < ∞`) -/

/-- **P5a** (size M, about 200 lines).  The first bound of `general_fluctuation_Wp` (trace-norm coupling, `Cv`), under `En ≠ ∞`.
Copy-edit of `gff_core` (GFFinal3.lean:18-262), W₁/W₂ clauses replaced by one clause at order `p`; the setting is the gradient clause (`M = -1`,
`μ S = S.γ`, `EV` from `gf_ev_grad_proof`, GFEVAux26.lean:18, `hj : EV.j x = x` as in GFFinal4.lean:76-79).
Route: `K` and `EV` as in GFFinal4.lean:61-76; `Y₀ := A • η₀` (GFFinal4.lean:76-80); `C₀min` from `gff_stage1_p b (-1) K p _` (P3b); `Cr`;
`C2` from `gff_stage2_p b.T K p hbT hp` (P4); apply P3b with `hEfin` obtained from `En ≠ ⊤` as follows: with `E_ω` the inner integral, `hmeasE` (WP-ENERGY (2)),
`(∫⁻ E^p) = En^p ≠ ⊤` (`ENNReal.rpow_mul`/`ENNReal.rpow_natCast`-free: `En ≠ ⊤ → En ^ p ≠ ⊤` and `(a ^ (1/p)) ^ p = a`), so `E_ω ^ p < ⊤` a.s.
(`ae_lt_top` for the measurable function `E^p`), hence `E_ω < ⊤` (`ENNReal.rpow_lt_top_iff_of_pos`/`ENNReal.lt_top_of_rpow_lt_top`).
Coupling: `gff_adapted_coupling_trace P₁ ℱ₁ S.T hT' ⟨ℱ₁ 0, le_rfl⟩ Mart Sg hS1.mart Cb hS1.det` (GFFinal1.lean:34; cost `‖Sg - Cb‖₁`) and
`hcostm := (measurable_trace_integral hS1.mart hS1.det).aemeasurable` (GFSpec5.lean:78), exactly GFFinal3.lean:107-114; then P4 gives
`W ≤ C2 ‖Ξ⁰-Aη'‖_p + ‖Bm‖_p + C2 (∫⁻ (∫⁻ cost)^{p/2})^{1/p}`; initial term and `Bm` from P3b.
Cost transfer `P₁ → P`: replace `Cb r` by `covForm (withDensityReal (ρ r))` on `Icc` (`covDensT_truncated`/`covDensT`, `if_pos`; GFFinal3.lean:122-129) and
`lintegral_comp_mp hπ₁ (f := fun ω => (∫⁻ r in Icc, ofReal (traceNormForm (covForm .. (empirical (X (toNNReal r) ω)) - covForm .. (withDensityReal (ρ r))))) ^ (p / 2))`
where the `AEMeasurable` on `Ω` comes from `measurable_trace_integral` applied on `P` with the particle martingale of `Ω`
(`gf_particle_martingale_proof S N _ P ℱ W' W X hF`, GFB3Aux7.lean:131, and `gf_detCovDensity_proof`, GFB1Aux3.lean:81), then `.pow_const (p/2)`.
Finish: `ofReal C2 * x ≤ ofReal C * x`, `ofReal (Cr σ) = ofReal Cr * ofReal σ`, `C := C2 + Cr + 1` (constants dominate; ENNReal `gcongr`).
Also needs `WP-ENERGY`, `WP-REM` (inside P3b). The `IsVectorBrownian` hypothesis is unused (as in `gff_core`). -/
theorem gff_core_Wp_trace (b : GeneralBounds d) (p : ℝ) (hp : 2 ≤ p) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHyp → S.PosDensityWith b.c →
      ∀ (N : ℕ) (_ : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P]
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (_ : IsVectorBrownian P W)
      (X : ℝ≥0 → Ω → Config d N) (_ : IsStrongSolution P (S.dyn N) S.T X₀ W X)
      (_ : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
        (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X)
      (η₀ : Ω → NegSobolev d S.γ) (_ : Measurable η₀)
      (_ : ProbabilityTheory.IndepFun (fun ω => (X₀ ω, η₀ ω)) (fun ω => fun t => W t ω) P)
      (Y : ℝ → Ω → NegSobolev d S.γ)
      (_ : IsLinearFluctuationSolution P (S.dyn N) (S.ρ N) S.γ (qScale N (S.κ N) (S.invβ N)) S.T
        (fun ω => Ascale N (S.κ N) (S.invβ N) • η₀ ω) Y),
      let σ := sigmaScale N (S.κ N) (S.invβ N)
      let A := Ascale N (S.κ N) (S.invβ N)
      let q := qScale N (S.κ N) (S.invβ N)
      let Ξ := law P (flucPath S.γ S.T σ X (S.ρ N))
      let YN := law P (toPath S.γ S.T Y)
      let ε : ℝ≥0∞ := (∫⁻ ω, ‖S.κ N • NegSobolev.ofMeasureDiff (S.γ : ℝ) (empirical (X₀ ω))
          (withDensityReal (S.ρ N 0)) - η₀ ω‖ₑ ^ p ∂P) ^ (1 / p)
      let En : ℝ≥0∞ := (∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) S.T,
          ENNReal.ofReal (S.energyCompletion N (X (Real.toNNReal t) ω) t)) ^ p ∂P) ^ (1 / p)
      let Cv : ℝ≥0∞ := (∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) S.T,
          ENNReal.ofReal (traceNormForm
            (covForm (S.γ : ℝ) q (empirical (X (Real.toNNReal t) ω)) -
              covForm (S.γ : ℝ) q (withDensityReal (S.ρ N t))))) ^ (p / 2) ∂P) ^ (1 / p)
      En ≠ ⊤ →
        wassersteinE p Ξ YN ≤ ENNReal.ofReal C * (ENNReal.ofReal A * ε + ENNReal.ofReal σ * En + Cv) := by
  sorry

/-- **P5b** (size M, about 250 lines).  The second bound of `general_fluctuation_Wp` (transport coupling, `Wt`), under `En ≠ ∞`.
Copy-edit of `gff_core_transport` (GFFinal4.lean:18-241) at order `p`; no pointwise `W₂ ≲ 𝓔^a` input and NO moment lemma is used
(`gf_transport_moment_proof` is not needed: `Wt` is on the right side as is).
Route: as P5a for `K`, `EV`, `Y₀`, P3b, P4 (`hcplT := (hCtr (S.γ : ℝ) hγS).2 P₁ ℱ₁ ⟨ℱ₁ 0, le_rfl⟩ N _ (qN S N) hq0 S.T hT' (fun r => X₁ (toNNReal r)) (S.ρ N) hdens hS1.det Mart hS1.mart`
with `⟨Ctr, hCtr⟩ := gf_adapted_coupling_transport hd1`, GFSpec4.lean:99; this is the proved variant of `transport_noise_coupling_proof`
(HRS/Uniform/TransportCoupling.lean:41), GFFinal4.lean:106-122; `hγS : d/2 + 2 < S.γ` from `S.hγ`, GFFinal4.lean:93-98).
Cost `cost r ω = Ctr * q * (torusWassersteinE 2 (empirical (X₁ r ω)) (withDensityReal (ρ r))).toReal ^ 2`; `wI ω := ∫⁻ r in Icc, ofReal (toReal W ^ 2)`;
`∫⁻ cost = ofReal (Ctr q) * wI` (GFFinal4.lean:124-131 `hcostE`).  `AEMeasurable wI` on `P₁`: from `gfwp_transport_cost_meas` (WP-TCOST) on `P` composed with
`hπ₁.quasiMeasurePreserving` (or on `P₁` directly with `hX₁`, `hF₁` from P3b).
Cost term: `(∫⁻_{P₁} (ofReal cT * wI)^{p/2})^{1/p} = ofReal cT ^ (1/2) * (∫⁻_{P₁} wI^{p/2})^{1/p}` (`ENNReal.mul_rpow_of_nonneg`, `lintegral_const_mul'`,
`← ENNReal.rpow_mul`, `(p/2) * (1/p) = 1/2`), `ofReal cT ^ (1/2) = ofReal (√Ctr * √q)` (`ENNReal.ofReal_rpow_of_nonneg`, `Real.sqrt_eq_rpow`, `Real.sqrt_mul`);
then `lintegral_comp_mp` moves `wI^{p/2}` to `P` (AEMeasurable from WP-TCOST (1) `.pow_const`); and finally the pointwise `ofReal (toReal w ^ 2) ≤ w ^ 2`
in `ℝ≥0∞` (true also for `w = ⊤`; `ENNReal.ofReal_toReal_le`, `ENNReal.ofReal_pow`, `ENNReal.rpow_le_rpow`, `lintegral_mono`, `setLIntegral_mono'`) bounds `wI ≤ ∫⁻ W2E^2`
so `(∫⁻ wI^{p/2})^{1/p} ≤ Wt`.  The positive constant `Ctr (S.γ)` is rewritten to `Ctr (b.γ)` by `S.γ = b.γ` (GFFinal4.lean:100-101 `hCtS`).
Finish as P5a with `C := C2 + Cr + C2 * √Ctr + 1`. -/
theorem gff_core_Wp_transport (b : GeneralBounds d) (p : ℝ) (hp : 2 ≤ p) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHyp → S.PosDensityWith b.c →
      ∀ (N : ℕ) (_ : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P]
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (_ : IsVectorBrownian P W)
      (X : ℝ≥0 → Ω → Config d N) (_ : IsStrongSolution P (S.dyn N) S.T X₀ W X)
      (_ : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
        (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X)
      (η₀ : Ω → NegSobolev d S.γ) (_ : Measurable η₀)
      (_ : ProbabilityTheory.IndepFun (fun ω => (X₀ ω, η₀ ω)) (fun ω => fun t => W t ω) P)
      (Y : ℝ → Ω → NegSobolev d S.γ)
      (_ : IsLinearFluctuationSolution P (S.dyn N) (S.ρ N) S.γ (qScale N (S.κ N) (S.invβ N)) S.T
        (fun ω => Ascale N (S.κ N) (S.invβ N) • η₀ ω) Y),
      let σ := sigmaScale N (S.κ N) (S.invβ N)
      let A := Ascale N (S.κ N) (S.invβ N)
      let q := qScale N (S.κ N) (S.invβ N)
      let Ξ := law P (flucPath S.γ S.T σ X (S.ρ N))
      let YN := law P (toPath S.γ S.T Y)
      let ε : ℝ≥0∞ := (∫⁻ ω, ‖S.κ N • NegSobolev.ofMeasureDiff (S.γ : ℝ) (empirical (X₀ ω))
          (withDensityReal (S.ρ N 0)) - η₀ ω‖ₑ ^ p ∂P) ^ (1 / p)
      let En : ℝ≥0∞ := (∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) S.T,
          ENNReal.ofReal (S.energyCompletion N (X (Real.toNNReal t) ω) t)) ^ p ∂P) ^ (1 / p)
      let Wt : ℝ≥0∞ := (∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) S.T,
          torusWassersteinE 2 (empirical (X (Real.toNNReal t) ω)) (withDensityReal (S.ρ N t)) ^ 2)
            ^ (p / 2) ∂P) ^ (1 / p)
      En ≠ ⊤ →
        wassersteinE p Ξ YN ≤ ENNReal.ofReal C * (ENNReal.ofReal A * ε + ENNReal.ofReal σ * En +
            ENNReal.ofReal (Real.sqrt q) * Wt) := by
  sorry

/-! ### P6: the final assembly -/

/-- **P6** (size S, about 70 lines).  The frozen statement `HRS.Uniform.general_fluctuation_Wp` (checked by the `example` below): from P5a, P5b and `gfwp_sigN_pos`.
Route: `C₀min := max C₀a C₀b`; `C := max Ca Cb`; for `S` etc. `by_cases hEn : En = ⊤`: then `ofReal σ * En = ⊤` (`ENNReal.mul_top`, `σ > 0` by `gfwp_sigN_pos`, `ENNReal.ofReal_pos`)
so the right sides are `⊤` (`ENNReal.mul_top` with `ofReal C ≠ 0`, `add_top`/`top_add`) and `le_top` closes both clauses; otherwise apply P5a and P5b and
monotonicity in the constant (`ENNReal.ofReal_le_ofReal`, `mul_le_mul_right'`, `Ca ≤ C`).  (`σ`, `A`, `q` in the frozen statement are `sigmaScale ..`, `Ascale ..`, `qScale ..` which are
`sigN S N`, `AN S N`, `qN S N` by `rfl`/unfolding of the `abbrev`s.) -/
theorem general_fluctuation_Wp_core (b : GeneralBounds d) (p : ℝ) (hp : 2 ≤ p) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHyp → S.PosDensityWith b.c →
      ∀ (N : ℕ) (_ : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P]
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (_ : IsVectorBrownian P W)
      (X : ℝ≥0 → Ω → Config d N) (_ : IsStrongSolution P (S.dyn N) S.T X₀ W X)
      (_ : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
        (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X)
      (η₀ : Ω → NegSobolev d S.γ) (_ : Measurable η₀)
      (_ : ProbabilityTheory.IndepFun (fun ω => (X₀ ω, η₀ ω)) (fun ω => fun t => W t ω) P)
      (Y : ℝ → Ω → NegSobolev d S.γ)
      (_ : IsLinearFluctuationSolution P (S.dyn N) (S.ρ N) S.γ (qScale N (S.κ N) (S.invβ N)) S.T
        (fun ω => Ascale N (S.κ N) (S.invβ N) • η₀ ω) Y),
      let σ := sigmaScale N (S.κ N) (S.invβ N)
      let A := Ascale N (S.κ N) (S.invβ N)
      let q := qScale N (S.κ N) (S.invβ N)
      let Ξ := law P (flucPath S.γ S.T σ X (S.ρ N))
      let YN := law P (toPath S.γ S.T Y)
      let ε : ℝ≥0∞ := (∫⁻ ω, ‖S.κ N • NegSobolev.ofMeasureDiff (S.γ : ℝ) (empirical (X₀ ω))
          (withDensityReal (S.ρ N 0)) - η₀ ω‖ₑ ^ p ∂P) ^ (1 / p)
      let En : ℝ≥0∞ := (∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) S.T,
          ENNReal.ofReal (S.energyCompletion N (X (Real.toNNReal t) ω) t)) ^ p ∂P) ^ (1 / p)
      let Cv : ℝ≥0∞ := (∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) S.T,
          ENNReal.ofReal (traceNormForm
            (covForm (S.γ : ℝ) q (empirical (X (Real.toNNReal t) ω)) -
              covForm (S.γ : ℝ) q (withDensityReal (S.ρ N t))))) ^ (p / 2) ∂P) ^ (1 / p)
      let Wt : ℝ≥0∞ := (∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) S.T,
          torusWassersteinE 2 (empirical (X (Real.toNNReal t) ω)) (withDensityReal (S.ρ N t)) ^ 2)
            ^ (p / 2) ∂P) ^ (1 / p)
      wassersteinE p Ξ YN ≤
          ENNReal.ofReal C * (ENNReal.ofReal A * ε + ENNReal.ofReal σ * En + Cv) ∧
      wassersteinE p Ξ YN ≤
          ENNReal.ofReal C * (ENNReal.ofReal A * ε + ENNReal.ofReal σ * En +
            ENNReal.ofReal (Real.sqrt q) * Wt) := by
  sorry

/-- The tie: the packet `general_fluctuation_Wp_core` has exactly the frozen type, so
`theorem general_fluctuation_Wp_proof : type_of% @HRS.Uniform.general_fluctuation_Wp := @general_fluctuation_Wp_core` (to be placed in the final file). -/
example : type_of% @HRS.Uniform.general_fluctuation_Wp := @general_fluctuation_Wp_core

end HRS.MH.Wp
