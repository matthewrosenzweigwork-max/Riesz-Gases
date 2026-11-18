import HRS.ME.CritDefs
import HRS.MD.EQBurnBurnMain
import HRS.MD.EQBurnWire
import HRS.Uniform.Q48cCov
import HRS.Main.HeadlineEquilibrium

/-!
# Chunk E, row 2.10 path clauses: statements (SPEC ONLY, every proof is `sorry`)

Route.  `critical_centered_path` (frozen, `HRS/Main/HeadlineEquilibrium.lean`) is the critical analogue of `equilibrium_paths_direct`
with the improved rate `N^{-1/2}`.  The burn-in of `HRS/MD/EQBurnBurn*.lean` loses to `N^{-1/4}` because its coupling cost is bounded
through the trace norm `‖Σ_N - C̄‖_{𝔖₁}`, whose expectation is only `b_N ~ N^{-1/2}`; the square root then gives `N^{-1/4}`.  The
adapted coupling of Lemma 3.29 has cost exactly the Bures quantity `𝔟(Σ_N, C̄)²`, and Lemma 3.28's majorant bounds
`E 𝔟(Σ_N, C̄)² ≤ C (N⁻¹ + δ_N²)` (`HRS.Uniform.Q48c.bures2_cov_estimate`), so the `W_2` window estimate (`t25p_wass_core`) gives
`(E ∫ e^{-2c(a-r)_+} 𝔟²)^{1/2} ≲ N^{-1/2}`.  The remainder term needs `(E sup ‖∫ 𝒱 𝓡_stat‖²)^{1/2} ≲ N^{-1/2}`, which is
Proposition 4.17 instead of `eq_rem_integrated` (`C √δ_N`).

| statement | role |
|---|---|
| `crit_stage2` (A1) | the `p = 2` case of `t25p_stage2` with the Bures cost in place of the trace norm |
| `crit_bures2_uniform` (A2) | `E_{ℙ_{N,β}} 𝔟(Σ_N, C̄_β)² ≤ C (N⁻¹ + δ_N²)`, `C` before `β ∈ [βm,βp]` |
| `crit_engine` (A3) | `eqb_engine` with `crit_stage2` |
| `crit_burnin_of_evo` (A4) | `CritBurnConcl` from the evolution package and `CritForcing` |
| `crit_paths_of_forcing` (A5) | the frozen `critical_centered_path` from `CritForcing` for all data |
| `crit_forcing_of_uniform417` (B1) | `CritForcing` from `Uniform417` (bridge `statForcingCoord` to `integratedCenteredForcing`) |

`Uniform417` (B2: Proposition 4.17 with the constant before `β`) is the input not proved here.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.Crit

open HRS HRS.LZ HRS.Uniform HRS.GF HRS.Uniform.Q45 HRS.Uniform.Q54c HRS.Uniform.Q07c HRS.Uniform.Comp28 HRS.T25P HRS.Main
  HRS.MD.EQ29 HRS.MD.EQBurn

variable {d : ℕ}

/-- (A1.)  The `p = 2` case of `HRS.T25P.t25p_stage2` (`HRS/Main/T25PAux13.lean`) with the Bures cost `𝔟(Sg r, Cb r)²` (`HRS.Uniform.bures2`)
in place of `‖Sg r - Cb r‖_{𝔖₁}` in the third term; the smooth conclusion is dropped.  Proof: the body of `t25p_stage2`, with the cost
function `fun r ω' => bures2 (Sg r (π ω')) (Cb r)` handed to `t25p_wass_core` (`hcost` is then the equality of `hcoup.cost`). -/
theorem crit_stage2 {m K c T Cmax : ℝ} (hK : 0 ≤ K) (hc : 0 ≤ c) (hT : 0 < T)
    (V : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (hEv : T25Ev m K c T Cmax V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 ≤ a →
      ∀ (Ω₁ : Type) [mΩ₁ : MeasurableSpace Ω₁] (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
        (ℱ₁ : Filtration ℝ mΩ₁) (X₀ X₀' : Ω₁ → NegSobolev d m),
        Measurable[ℱ₁ 0] X₀ → Measurable[ℱ₁ 0] X₀' →
        ∀ (Mart : ℝ → Ω₁ → NegSobolev d m)
          (Sg : ℝ → Ω₁ → (NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ)),
          IsHilbertMartingaleWithCovariation P₁ ℱ₁ (a + T) Mart Sg →
          ∀ (Cb : ℝ → (NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ)), IsDetCovDensity (a + T) Cb →
          (∀ r : ℝ, a + T < r → Cb r = 0) →
          ∀ (Z Rr Xp : ℝ → Ω₁ → NegSobolev d m),
            (∀ t ∈ Set.Icc (0 : ℝ) (a + T),
              IsStochConv P₁ V (ContinuousLinearMap.id ℝ (NegSobolev d m)) Mart 0 t (Z t)) →
            (∀ᵐ ω ∂P₁, ContinuousOn (fun t => Z t ω) (Set.Icc 0 (a + T))) → (∀ t, Measurable (Z t)) →
            (∀ᵐ ω ∂P₁, ContinuousOn (fun t => Rr t ω) (Set.Icc 0 (a + T))) → (∀ t, Measurable (Rr t)) →
            (∀ t ∈ Set.Icc (0 : ℝ) (a + T), ∀ ω, Xp t ω = V t 0 (X₀ ω) + Z t ω + Rr t ω) →
            ∀ (Bm : Ω₁ → ℝ≥0∞), AEMeasurable Bm P₁ →
            (∀ᵐ ω ∂P₁, ∀ t ∈ Set.Icc a (a + T), ‖Rr t ω‖ₑ ≤ Bm ω) →
            ∀ (Λ : Measure (PathSp T (NegSobolev d m))),
              (∀ (Ω₂ : Type) [mΩ₂ : MeasurableSpace Ω₂] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
                (ℱ₂ : Filtration ℝ mΩ₂) (ξ : Ω₂ → NegSobolev d m) (G : ℝ → Ω₂ → NegSobolev d m),
                Measurable ξ →
                IsHilbertMartingaleWithCovariation P₂ ℱ₂ (a + T) G (fun r _ => Cb r) →
                Indep (MeasurableSpace.comap ξ inferInstance)
                  (⨆ τ ∈ Set.Icc (0 : ℝ) (a + T), MeasurableSpace.comap (G τ) inferInstance) P₂ →
                P₂.map ξ = P₁.map X₀' →
                ∀ Zb : ℝ → Ω₂ → NegSobolev d m,
                  (∀ t ∈ Set.Icc (0 : ℝ) (a + T),
                    IsStochConv P₂ V (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zb t)) →
                  (∀ᵐ ω ∂P₂, ContinuousOn (fun t => Zb t ω) (Set.Icc 0 (a + T))) →
                  (∀ t, Measurable (Zb t)) →
                  Λ = law P₂ (windowPath a T (fun t ω => V t 0 (ξ ω) + Zb t ω))) →
              wassersteinE 2 (law P₁ (windowPath a T Xp)) Λ ≤
                ENNReal.ofReal ((2 * (K ^ 2 + Real.sqrt Cmax) + K + 1) * Real.exp (-c * a)) *
                    (∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ^ (2 : ℝ) ∂P₁) ^ (1 / (2 : ℝ)) +
                  (∫⁻ ω, Bm ω ^ (2 : ℝ) ∂P₁) ^ (1 / (2 : ℝ)) +
                  ENNReal.ofReal (2 * (K ^ 2 + Real.sqrt Cmax) + K + 1) *
                    (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T),
                      ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 * bures2 (Sg r ω) (Cb r))) ∂P₁) ^
                      (1 / (2 : ℝ)) := by
  sorry

/-- (A2.)  `E_{ℙ_{N,β}} 𝔟(Σ_N, C̄_β)² ≤ C (N⁻¹ + δ_N²)`, `Σ_N = covForm m β⁻¹ μ_N`, `C̄_β = covForm m β⁻¹ μ_β`, for `m ≥ d+3`, with `C`
chosen before `β ∈ [βm,βp]` and the thermal density.  Proof: `HRS.Uniform.Q48c.bures2_cov_estimate` (whose threshold is `d+3` and whose constant is
`2 c⁻¹ (16 β⁻¹ d² Kmax S²)` with `c` a lower bound for `ρβ`) with the hypotheses `eq_static_linear_proof` (variance), `equilibrium_marginal_L2_proof` (marginal;
`g = dm_N/dμ`), and the uniform lower bound for the thermal densities (`PDE.MFDecay.exists_thermal_bounds`).  The two lemmas of `Q48cCov.lean` that
carry the constant are used with the constant exposed. -/
theorem crit_bures2_uniform (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (m : ℝ) (hm : (d : ℝ) + 3 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, β ∈ Set.Icc βm βp → ∀ ρβ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) V β ρβ → ∀ N : ℕ, 2 ≤ N →
      ∫⁻ X, ENNReal.ofReal (bures2 (covForm m β⁻¹ (empirical X)) (covForm m β⁻¹ (withDensityReal ρβ)))
          ∂(canonicalGibbs (periodicRiesz d s) V N β) ≤
        ENNReal.ofReal (C * ((N : ℝ)⁻¹ + deltaN d s N ^ 2)) := by
  sorry

/-- (A3.)  `HRS.MD.EQBurnBurn.eqb_engine` with `crit_stage2` in place of `t25p_stage2`: the same enlarged space, filtered flow and initial field
`η'`; the conclusion is the `W_2` inequality with the three terms (initial, remainder `Bm`, Bures cost of the empirical covariance). -/
theorem crit_engine (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    (m : ℝ) (hm : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m)
    {K c T Cmax : ℝ} (hK : 0 < K) (hc : 0 < c) (hT : 0 < T)
    (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (hEv : T25Ev m K c T Cmax Vev)
    (hdual : IsDualEvolution (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) m Vev)
    {a : ℝ} (ha : 0 ≤ a) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hX : IsStationaryGibbsFlow P s hs0 hsd V β hβ (a + T) X₀ W X)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → NegSobolev d m) (hZ : IsStationaryGaussianField P' s β hs0 hsd hβ V ρβ m Z) :
    ∃ (Ω₁ : Type) (mΩ₁ : MeasurableSpace Ω₁) (P₁ : Measure Ω₁) (_ : IsProbabilityMeasure P₁)
      (π : Ω₁ → Ω) (_ : MeasurePreserving π P₁ P) (ℱ₁ : Filtration ℝ mΩ₁)
      (W'' : ℝ≥0 → Ω₁ → (Fin N × Fin d) → ℝ) (η' : Ω₁ → NegSobolev d m),
      IsStationaryGibbsFlow P₁ s hs0 hsd V β hβ (a + T) (fun ω' => X₀ (π ω')) (fun t ω' => W t (π ω'))
        (fun t ω' => X t (π ω')) ∧
      IsFilteredSolution P₁ ℱ₁ W'' (fun t ω' => W t (π ω')) (fun t ω' => X t (π ω')) ∧
      Measurable η' ∧ P₁.map η' = P'.map (Z 0) ∧
      wassersteinE 2 (law P (Main.windowZeta m T a P X)) (law P' (Main.windowPath m T 0 Z)) ≤
        ENNReal.ofReal ((2 * (K ^ 2 + Real.sqrt Cmax) + K + 1) * Real.exp (-c * a)) *
            (∫⁻ ω, ‖zetaE m (P₁.map (fun ω'' => X (0 : ℝ≥0) (π ω''))) (X (0 : ℝ≥0) (π ω)) - η' ω‖ₑ ^ (2 : ℝ) ∂P₁) ^
              (1 / (2 : ℝ)) +
          (∫⁻ ω, (⨆ t ∈ ratTimes a T, (coordEnergy m (fun k => statForcingCoord d hs0 hsd V hβ ρβ
              (fun t ω' => X t (π ω')) k t ω)) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ∂P₁) ^ (1 / (2 : ℝ)) +
          ENNReal.ofReal (2 * (K ^ 2 + Real.sqrt Cmax) + K + 1) *
            (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T),
              ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
                bures2 (covForm m β⁻¹ (empirical (X r.toNNReal (π ω)))) (covForm m β⁻¹ (withDensityReal ρβ)))) ∂P₁) ^
              (1 / (2 : ℝ)) := by
  sorry

/-- (A4.)  The critical burn-in estimate for `T > 0`, from the evolution package (`EvoPkg`, as in `eq_burnin_of_evo`) and the critical forcing
bound `CritForcing`.  Proof: `crit_engine`; initial term by `eq_init_particle_proof`, `eq_init_gauss_proof`; remainder by `CritForcing`; Bures term by
`crit_bures2_uniform`, stationarity of the flow (`md_stat_gibbs_flow_stationary_proof`), Tonelli and `∫_0^{a+T} e^{-2c(a-r)_+} ≤ 1/(2c) + T`;
`δ_N² ≤ 4/N` at `s = d/2` (`δ_N = N⁻¹ log(eN)`). -/
theorem crit_burnin_of_evo (hd : 2 ≤ d) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (m : ℝ) (hm : 24 * (d : ℝ) + 240 ≤ m) (T : ℝ) (hT : 0 < T)
    (K c Cmax : ℝ) (hK : 0 ≤ K) (hc : 0 < c) (hCmax : 0 ≤ Cmax)
    (hevo : EvoPkg d ((d : ℝ) / 2) hs0 hsd V βm βp hβm m K c T Cmax)
    (hforce : CritForcing d hs0 hsd V βm βp hβm m T) :
    CritBurnConcl d hs0 hsd V βm βp hβm m T := by
  sorry

/-- (A5.)  The frozen `HRS.Main.critical_centered_path` from `CritForcing`, supplied for every datum.  Proof: the assembly of
`HRS.MD.EQAsmDirect.eq_direct_assembly_proof` (burn-in at `T`, `eq_path_stationary_proof`, `eq_flow_exists_proof`, `a → ∞`) with `crit_burnin_of_evo`
and the evolution package of `eq_evolution_uniform_proof` (`HRS/MD/EQBurnWire.lean`, `eqbw_evoPkg`); then `wassersteinE_mono` for `1 ≤ p ≤ 2`,
`smoothDist_one_le_wasserstein`, `wassersteinE_one_le_two` and `smoothDist_succ_le` for `d_k`, `k ≥ 1`. -/
theorem crit_paths_of_forcing
    (hforce : ∀ (hd : 2 ≤ d) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d)
      (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
      (m : ℝ) (hm : 24 * (d : ℝ) + 240 ≤ m) (T : ℝ) (hT : 0 < T),
      CritForcing d hs0 hsd V βm βp hβm m T) :
    type_of% (@HRS.Main.critical_centered_path d) := by
  sorry

/-- (B1.)  `CritForcing` from `Uniform417`.  Bridge: `eq_statRemainder_eq_neg_forcing_proof` (`HRS/MD/EQRemBridge.lean`), stationarity of the flow
(`md_stat_gibbs_flow_stationary_proof`), the identification `propagator (mfData ..) (fun _ => ρβ) r t = equilibriumSemigroup .. (t - r)`
(time homogeneity), the smoothness and positivity of the thermal density (`Q41.q41_thermal_regular`), and the sum over `k` that turns `coordEnergy m`
into `∑' k ofReal (integratedCenteredForcing .. m k ..)` (the test function of `integratedCenteredForcing` carries the factor `⟨k⟩^{-m}`). -/
theorem crit_forcing_of_uniform417 (hd : 2 ≤ d) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (m T : ℝ) (hT : 0 < T) (hu : Uniform417 d hs0 hsd V βm βp hβm m T) :
    CritForcing d hs0 hsd V βm βp hβm m T := by
  sorry

end HRS.ME.Crit

end
