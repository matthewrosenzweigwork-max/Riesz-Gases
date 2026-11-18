import HRS.Whole.AppendixBEnergy
import HRS.MH.CommSuperCS10
import HRS.Commutator.Whole.Bridge
import HRS.MS.SuppU15Aux1
import HRS.Whole.Q09BAux3
import HRS.MH.CoercLowerFinal

/-!
# S.B.1 (`mfe_confined_rd_gradient_super/_sub`): per-row plan and Layer-0 packets (part 1)

Worker SB1, 2026-10-24.  Full plan: `docs/SB1_PLAN.md`.  Summary.

## Verdict on the frozen statements (`HRS/Whole/AppendixBEnergy.lean:151,178`; TeX S L11079-11117, proof L11118-11165)

TRUE as stated and non-vacuous modulo the existence of collision-free strong solutions (a hypothesis of `WholeMFEHyp`);
nothing frozen is touched.  Points checked: (T1) at `s = 0` the frozen S.B.5 rows put the log-moment bound `L` before the
constants whereas S.B.1 puts `C₀, C` before `Λ` (and `L ≲ C_dΛ`): resolved here by `sb1_comm_super_free/_sub_free` (L-free
constants, from `compact_case_proof`/`bridge_core`); (T2) S.B.5 covers only the exact kernel, so the TeX sentence "closes by
Gronwall at the regularised level" cannot be run with S.B.5: the whole-space proof must follow the torus entropy route
(moving Gibbs reference `Q_t`, source `R_N`, uniform exponential moment of the source, conditioning on bounded density);
(T3) `d = 1` (super, `s ∈ [0,1)`): S3.1 `euclidean_pressure`/`_pair_entropy` are proved for `2 ≤ d` only (`wr8_core`), so that
route needs a `d = 1` pressure packet; (T4) the row's S4.9 input is not used (one-body Poincaré for the log thermal measure).
Junk-value audit: Bochner `∫ F ∂f` guarded by `MFEFiniteW`; `.toReal` guarded by `relEntropy ≠ ⊤`; `eLpNorm ≤ ofReal F` is a
genuine bound; `Real.log` only of `ρ > 0`; `invβ > 0`; `d ≥ 1` (sub: `d ≥ 3`); `K ≥ 0` automatic; no `tsum`.

## Route and packets

`𝖤_N = (β⁻¹/N)(H(f|Q_t) - log K_t)`; (DISS) `MfeDiss` (the whole-space `mov_mfe_ineq`) + coercivity + commutator + Grönwall
(`sb1_core`, the torus `mfe_uniform_proof`) give both frozen statements (`sb1_super_of_diss`, `sb1_sub_of_diss`).

Layer 0, PROVED (this worker; `MfeConfAux1..4`, propext, Classical.choice, Quot.sound only): SB1-A `sb1_comm_super_free`, `sb1_comm_sub_free`;
SB1-B `sb1_regular_density_bounds`; SB1-C (Aux2) `sb1_fracDeriv_affine`, `sb1_isFracDerivRep_add`, `sb1_transport_add_affine`;
SB1-D (Aux3) `sb1_mfe_ac`; SB1-E (Aux3-4) `sb1_core`, `sb1_super_of_diss`, `sb1_sub_of_diss`.

Layer 1, NOT proved (the whole-space `mov_mfe_ineq` = (DISS); sizes calibrated on the torus chain, ~47k lines of Mov/B15/
TorusFP/WeakReference/Pressure of which ~15k generic stochastic calculus is shared):
F1 `MovTrajW` classical `C¹`-in-t densities (700); F2 `movW_relEntropy_split` (500); F3 `movW_logK_integral` (1.8-2.5k);
F4 truncated kernels + regularised flow `X^M = X` (`p4_kernel_proof`, `p4_regularised_flow_proof`, 800); F5 weak FP and moments
(`p4_flow_hyp_proof`, 300); F6 ε-level moving-reference entropy inequality with signed source (transplant of
`p4_mollified_ineq_proof`, 3-4.5k); F7 ε-uniform exponential moment of the source (pressure for truncated kernels,
`wr8_pressure_abstract`; 2-3k, +2-4k for `d = 1`); F8 MOV-A source decomposition (2k); F9 bounded-density case, conditioning,
lsc (2.5k); F10 spatial cutoff and second moments (1.5-2.5k); F11 assemblies and ties (800).
DAG: A,B,C,D → E ← F11 ← {F2,F3,F9,F10}; F9 ← {F6,F7,F8}; F6 ← {F4,F5}; F7,F3 ← F1; F2,F7 ← S3.1.
Total missing: 18-26k lines (+2-4k if `d = 1` via a new pressure), 3-4 times the 6-12k of the row estimate.

Namespace `HRS.MS.MfeConf`, helper prefix `sb1_`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MfeConf


variable {d : ℕ}

/-! ### SB1-A: S.B.5 with constants independent of the logarithmic moment -/

/-- S.B.5(i) with `C₀, C` independent of the log moment: at `s = 0` only the qualitative integrability of
`log(2+|x|)` is assumed.  From `compact_case_proof` (constants first) and `truncation_limit_proof`
(`L := ∫ log(2+|x|) dμ`). -/
theorem sb1_comm_super_free (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (hsc : (d : ℝ) - 2 ≤ s) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (Λ : ℝ), 1 ≤ Λ → ∀ (N : ℕ), 2 ≤ N →
      ∀ ρ : Euc d → ℝ, Whole.IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      (s = 0 → Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) (Whole.withDensityReal ρ)) →
      ∀ X : Whole.EucConfig d N, Function.Injective X →
      ∀ (v : Euc d → Euc d) (K : ℝ), Whole.HasLipBoundW v K →
        Whole.CommIntegrableW d s v X (Whole.withDensityReal ρ) ∧
        |Whole.commN d s v X (Whole.withDensityReal ρ)| ≤
          C * K * (Whole.rieszModulatedEnergy d s X (Whole.withDensityReal ρ) + oNΛ d s C₀ Λ N) := by
  obtain ⟨C₀, C, hcc⟩ := HRS.MH.CommSuper.compact_case_proof hd hs0 hsc hsd
  have hcc' := hcc
  unfold HRS.MH.CommSuper.CompactCase at hcc'
  refine ⟨C₀, C, hcc'.1, hcc'.2.1, ?_⟩
  intro Λ hΛ N hN ρ hρ hρΛ hlog X hX v K hK
  have hlog' : s = 0 → Whole.HasLogMoment (Whole.withDensityReal ρ)
      (∫ x : Euc d, Real.log (2 + ‖x‖) ∂(Whole.withDensityReal ρ)) := fun h => ⟨hlog h, le_rfl⟩
  exact ⟨(HRS.MH.CommSuper.bdd_integrable_proof hd hs0 hsd hρ hρΛ hlog' X hX v K hK).2.2,
    HRS.MH.CommSuper.truncation_limit_proof hd hs0 hsd hcc _ Λ hΛ N hN ρ hρ hρΛ hlog' X hX v K hK⟩

/-- S.B.5(ii) with `C₀, C` independent of the log moment (the constants depend on `d, s, a`; `bridge_core`
carries the hypothesis `LogIntegrable` and its constants do not see `L`). -/
theorem sb1_comm_sub_free {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (a : ℝ)
    (ha : (d : ℝ) < a ∧ a < (d : ℝ) + 2) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (Λ : ℝ), 1 ≤ Λ → ∀ (N : ℕ), 2 ≤ N →
      ∀ ρ : Euc d → ℝ, Whole.IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      (s = 0 → Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) (Whole.withDensityReal ρ)) →
      ∀ X : Whole.EucConfig d N, Function.Injective X →
      ∀ (v : Euc d → Euc d) (K : ℝ), Whole.HasFracTransportBound (a / 2) (2 * d / (a - 2)) v K →
        Whole.CommIntegrableW d s v X (Whole.withDensityReal ρ) ∧
        |Whole.commN d s v X (Whole.withDensityReal ρ)| ≤
          C * K * (Whole.rieszModulatedEnergy d s X (Whole.withDensityReal ρ) + oNΛ d s C₀ Λ N) := by
  have hd : 3 ≤ d := by
    have h2 : (2 : ℝ) < d := by linarith
    have : 2 < d := by exact_mod_cast h2
    omega
  obtain ⟨C₀, C, hC₀, hC, H⟩ := HRS.Commutator.Whole.bridge_core hd hs0 hsd
  obtain ⟨Ce, hCe, E⟩ := HRS.Commutator.Whole.sobolev_embedding_frac hd hs0 hsd a ha
  refine ⟨C₀, C * Ce, hC₀, by positivity, ?_⟩
  intro Λ hΛ N hN ρ hρ hΛρ hlog X hX v K hv
  obtain ⟨hci, hb⟩ := H Λ hΛ N hN ρ hρ hΛρ
    (fun h0 => HRS.Commutator.Whole.logIntegrable_of_logMoment ρ hρ Λ hΛρ
      (∫ x : Euc d, Real.log (2 + ‖x‖) ∂(Whole.withDensityReal ρ)) ⟨hlog h0, le_rfl⟩)
    X hX v (Ce * K) (E v K hv)
  refine ⟨hci, ?_⟩
  have e : C * (Ce * K) = C * Ce * K := by ring
  rwa [e] at hb

/-! ### SB1-B: consequences of the weighted regularity of one density -/

/-- `Whole.IsRegularDensityW r Λ ρ` and `ρ` a probability density give `⟨x⟩^{d+3} ρ ≤ Λ` pointwise, hence `ρ ≤ Λ`, and a log
moment (with a bound depending only on `d, Λ`). -/
theorem sb1_regular_density_bounds (r : ℕ) (Λ : ℝ) :
    ∃ Lm : ℝ, ∀ ρ : Euc d → ℝ, Whole.IsProbDensity ρ → Whole.IsRegularDensityW r Λ ρ →
      (∀ x, ρ x ≤ max Λ 0) ∧ (∀ x, Whole.jbracket x ^ ((d : ℝ) + 3) * |ρ x| ≤ max Λ 0) ∧
        Whole.HasLogMoment (Whole.withDensityReal ρ) Lm := by
  obtain ⟨Lm, hLm⟩ := HRS.MS.SuppU15.u15_logmoment (d := d) (L := (d : ℝ) + 3) (by linarith) Λ
  refine ⟨Lm, fun ρ hρ hreg => ?_⟩
  have hw : Whole.weightedSupE r ((d : ℝ) + 3) ρ ≤ ENNReal.ofReal Λ :=
    le_trans le_add_self (hreg.2.2)
  have hfin : Whole.weightedSupE r ((d : ℝ) + 3) ρ < ⊤ := lt_of_le_of_lt hw ENNReal.ofReal_lt_top
  have hb : ∀ x, Whole.jbracket x ^ ((d : ℝ) + 3) * |ρ x| ≤ max Λ 0 := by
    intro x
    have h1 := HRS.Whole.Q09B.q09b_jbracket_bound hfin x
    have h2 : (Whole.weightedSupE r ((d : ℝ) + 3) ρ).toReal ≤ max Λ 0 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hw
      rw [ENNReal.toReal_ofReal'] at this
      exact this
    exact h1.trans h2
  exact ⟨fun x => HRS.MS.SuppU15.u15_dens_le (by positivity) hρ.nonneg hb x, hb, hLm ρ hρ hb⟩

end HRS.MS.MfeConf

end
