import HRS.Main.GFSpec3
import HRS.Uniform.Q45Smooth
import HRS.Uniform.Q45Max
import HRS.Uniform.Q54Aux10
import HRS.Uniform.RelativeCoupling
import HRS.Uniform.TransportCoupling

/-!
# Packet GF-SPEC, part 4: proved glue (couplings with `covDensT`, remainder assembly, coupling interface)

PROVED glue between the sorried sub-packet statements of `GFSpec1`-`GFSpec3` and the proved inputs
(`relative_covariance_coupling_proof`, `q14_bures2_W2`, `duality_identity_all` through the packets):

* `embed_self`, `covDensT_truncated`;
* `gf_adapted_coupling_trace` (Lemma 3.29 coupling with cost `‖Sg - Db‖₁`, from `gf_bures2_le_traceNorm`) and
  `gf_adapted_coupling_transport` (Lemma 3.24 coupling with cost `C q W₂²`, for the deterministic covariation `covDensT`);
* `gf_remainder_bound`: the pathwise remainder bound `sup_t ‖R_t‖_{E_m} ≤ C σ_N ∫_0^t 𝓔_N` from GF-MILD, GF-PAIR, GF-REM-ptw,
  GF-REM-norm, GF-EN;
* `gf_coupling_difference`, `gf_coupling_cost_le`, `gf_coupling_indep`: the fields of `IsAdaptedGaussianCoupling` are exactly the
  hypotheses of `gf_wasserstein_comparison` and `gf_law_identification`.

The assembly plan, the hypothesis table, the list of sorried packets and the doubts are in the header of
`HRS/Main/GFSpec7.lean` (the last file).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS.Uniform

variable {d : ℕ}

/-! ### Small PROVED facts -/

/-- PROVED.  The embedding `E_m ↪ E_m` is the identity (the weighted coordinates are unchanged).  Used to identify the gradient
clause's initial datum `A η°` with `A · embed γ η°`. -/
theorem embed_self (m : ℝ) (F : NegSobolev d m) : NegSobolev.embed m F = F := by
  have hc : (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * NegSobolev.fourierCoeff F k) =
      fun k => NegSobolev.coord F k := by
    funext k
    unfold NegSobolev.fourierCoeff
    rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1)]
    simp
  have hmem : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * NegSobolev.fourierCoeff F k) 2 := by
    rw [hc]
    exact (show lp (fun _ : NonzeroLattice d => ℝ) 2 from F).2
  unfold NegSobolev.embed
  have h := NegSobolev.ofSeq_of_mem (m := m) (NegSobolev.fourierCoeff F) hmem
  refine h.trans (Subtype.ext ?_)
  exact hc

/-- PROVED.  The truncation `if ofReal r ≤ ofReal T then · else 0` of the covariation in
`IsAdaptedGaussianCoupling.gaussian` is invisible for `covDensT` (which vanishes outside `[0,T]`). -/
theorem covDensT_truncated {γ q T : ℝ} (hT : 0 ≤ T) (ρ : ℝ → Torus d → ℝ) (r : ℝ) :
    (if ENNReal.ofReal r ≤ ENNReal.ofReal T then covDensT γ q T ρ r else 0) = covDensT γ q T ρ r := by
  by_cases h : r ≤ T
  · rw [if_pos (ENNReal.ofReal_le_ofReal h)]
  · have hr : T < r := not_le.1 h
    have h0 : covDensT γ q T ρ r = 0 := by
      unfold covDensT
      rw [if_neg]
      intro hmem
      exact h hmem.2
    rw [h0]
    simp

/-! ### The two adapted Gaussian couplings, with the deterministic covariation `covDensT` -/

/-- PROVED (modulo `gf_bures2_le_traceNorm`).  The adapted Gaussian coupling of Lemma 3.29 with cost the trace-norm distance
`‖Sg_r - Db_r‖_{𝔖₁}` (`rel = (· ≤ ·)`), from `relative_covariance_coupling_proof` (cost `𝔟²`) and `gf_bures2_le_traceNorm`.
This is the coupling used for the smooth and the (non-transport) Wasserstein estimates. -/
theorem gf_adapted_coupling_trace {Ω : Type} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (ℱ : Filtration ℝ mΩ) (T : ℝ) (hT : 0 ≤ T) (𝒢 : InitialSigma ℱ) (M : ℝ → Ω → H)
    (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)) (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg)
    (Db : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)) (hDb : IsDetCovDensity T Db) :
    AdaptedGaussianCoupling P ℱ (ENNReal.ofReal T) 𝒢 M Sg Db (· ≤ ·)
      (fun r ω => traceNormForm (Sg r ω - Db r)) := by
  obtain ⟨Ω', mΩ', P', π, ℱ', Gb, Sd, h⟩ := relative_covariance_coupling_proof P ℱ T hT 𝒢 M Sg hM Db hDb
  refine ⟨Ω', mΩ', P', π, ℱ', Gb, Sd, ⟨h.preserving, h.filtration, h.martingale, h.gaussian,
    h.difference, h.indep, ?_⟩⟩
  filter_upwards [h.cost, h.preserving.quasiMeasurePreserving.ae hM.sigma_traceClass] with ω' hω' htc r hr0 hrT
  have hrT' : r ≤ T := (ENNReal.ofReal_le_ofReal_iff hT).1 hrT
  have hr : r ∈ Set.Icc (0 : ℝ) T := ⟨hr0, hrT'⟩
  have h1 := hω' r hr0 hrT
  show traceNormForm (Sd r ω') ≤ traceNormForm (Sg r (π ω') - Db r)
  rw [h1]
  exact gf_bures2_le_traceNorm _ _ (htc r hr) (hDb.traceClass r hr)

/-- PROVED.  The transport coupling (Lemma 3.24, `transport_noise_coupling_proof`) restated for the deterministic covariation
`covDensT γ q T ρ` (zero outside `[0,T]`; `IsDetCovDensity` is a hypothesis instead of the global measurability of `r ↦ covForm γ q ρ_r`,
which fails for an arbitrary extension of `ρ_N` outside `[0,T]`).  Same proof as `transport_noise_coupling_proof`, from
`relative_covariance_coupling_proof` and `q14_bures2_W2`. -/
theorem gf_adapted_coupling_transport (hd : 1 ≤ d) :
    ∃ Ct : ℝ → ℝ, ∀ γ : ℝ, (d : ℝ) / 2 + 2 < γ → 0 < Ct γ ∧
      ∀ {Ω : Type} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ mΩ) (𝒢 : InitialSigma ℱ) (N : ℕ) (_ : 1 ≤ N) (q : ℝ) (_ : 0 ≤ q) (T : ℝ)
      (_ : 0 ≤ T) (X : ℝ → Ω → Config d N) (ρ : ℝ → Torus d → ℝ)
      (_ : ∀ r ∈ Set.Icc (0 : ℝ) T, IsProbDensity (ρ r))
      (_ : IsDetCovDensity T (covDensT γ q T ρ)) (M : ℝ → Ω → NegSobolev d γ)
      (_ : IsHilbertMartingaleWithCovariation P ℱ T M
        (fun r ω => covForm γ q (empirical (X r ω)))),
      AdaptedGaussianCoupling P ℱ (ENNReal.ofReal T) 𝒢 M
        (fun r ω => covForm γ q (empirical (X r ω))) (covDensT γ q T ρ) (· ≤ ·)
        (fun r ω => Ct γ * q *
          (torusWassersteinE 2 (empirical (X r ω)) (withDensityReal (ρ r))).toReal ^ 2) := by
  refine ⟨fun γ => 4 * d * Q14.q14S d (γ - 2) + 1, fun γ hγ => ⟨?_, ?_⟩⟩
  · have := Q14.q14S_nonneg d (γ - 2)
    positivity
  have hS₂ := Q14.q14S_nonneg d (γ - 2)
  intro Ω mΩ P _ ℱ 𝒢 N hN q hq T hT X ρ hρ hDb M hM
  have hdens : ∀ r ∈ Set.Icc (0 : ℝ) T, IsProbabilityMeasure (withDensityReal (ρ r)) :=
    fun r hr => q14_isProb_withDensityReal (hρ r hr)
  obtain ⟨Ω', mΩ', P', π, ℱ', Gb, Sd, h⟩ := relative_covariance_coupling_proof P ℱ T hT 𝒢 M _ hM
    _ hDb
  refine ⟨Ω', mΩ', P', π, ℱ', Gb, Sd, ⟨h.preserving, h.filtration, h.martingale, h.gaussian,
    h.difference, h.indep, ?_⟩⟩
  filter_upwards [h.cost] with ω' hω' r hr0 hrT
  have hrT' : r ≤ T := (ENNReal.ofReal_le_ofReal_iff hT).1 hrT
  have hr : r ∈ Set.Icc (0 : ℝ) T := ⟨hr0, hrT'⟩
  have h1 := hω' r hr0 hrT
  show traceNormForm (Sd r ω') ≤ _
  rw [h1]
  have hcd : covDensT γ q T ρ r = covForm γ q (withDensityReal (ρ r)) := by
    unfold covDensT; rw [if_pos hr]
  show Uniform.bures2 (covForm γ q (empirical (X r (π ω')))) (covDensT γ q T ρ r) ≤ _
  rw [hcd]
  haveI := hdens r hr
  haveI := empirical_isProbabilityMeasure (Nat.pos_of_ne_zero (by omega)) (X r (π ω'))
  have h2 := Q14.q14_bures2_W2 hγ hq (empirical (X r (π ω'))) (withDensityReal (ρ r))
  refine h2.trans ?_
  have hW : 0 ≤ (torusWassersteinE 2 (empirical (X r (π ω'))) (withDensityReal (ρ r))).toReal ^ 2 :=
    sq_nonneg _
  nlinarith [mul_nonneg hq hW]

/-! ### The remainder bound, assembled from GF-MILD, GF-PAIR, GF-REM-ptw, GF-REM-norm, GF-EN -/

/-- PROVED.  The pairing with a Sobolev test function is a continuous functional, hence measurable along a measurable `Z`. -/
theorem gf_measurable_eval_pair {Ω : Type*} [MeasurableSpace Ω] {m : ℝ} {Z : Ω → NegSobolev d m}
    (hZ : Measurable Z) {φ : Torus d → ℝ} (hφ : MemSobolev m φ) {P : Measure Ω} :
    AEMeasurable (fun ω => NegSobolev.eval (Z ω) φ) P := by
  have e : (fun ω => NegSobolev.eval (Z ω) φ) = fun ω => inner ℝ (Z ω) (HRS.Uniform.Q54.lpOf m hφ) := by
    funext ω; exact HRS.Uniform.Q54.eval_eq_inner m (Z ω) hφ
  rw [e]
  exact (hZ.inner measurable_const).aemeasurable

/-- **`gf_remainder_bound`** (TeX M L2452-2455, `U:eq:quantitative-drift`: `‖R_N‖_{C_t H^{-γ}} ≤ C σ_N ∫_0^T 𝓔_N^t dt`), PROVED
from the sorried packets `gf_mild_identity`, `gf_pair_identification`, `gf_remainder_pointwise`, `gf_norm_of_pairings`,
`gf_energy_integral_moment`, `gf_smooth_mem`, `gf_eval_sub`.  For any `Z` which is the stochastic convolution of the particle martingale
(in the sense of `IsStochConv`, a.s. continuous), the remainder `R_t = Ξ^t - V(t,0) j Ξ^0 - Z_t` satisfies, almost surely and
simultaneously for all `t ∈ [0,T]`, `‖R_t‖_{E_m} ≤ C σ_N ∫_0^t 𝓔_N^r dr`.  The `C₀`-threshold is that of `gf_remainder_pointwise`.  (Repaired 2026-10-17, ISSUES GFB3: `Z t` is assumed measurable, to
feed `hZm` of `gf_pair_identification`.) -/
theorem gf_remainder_bound (b : GeneralBounds d) (M : Matrix (Fin d) (Fin d) ℝ) (K : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHypM M → ∀ N : ℕ, 2 ≤ N →
      ∀ m : ℝ, (S.γ : ℝ) ≤ m →
      ∀ EV : EvolData (NegSobolev d (S.γ : ℝ)) (NegSobolev d m), GFEvo S M N m K EV →
      ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStrongSolution P (S.dynM M N) S.T X₀ W X →
        ∀ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X →
        S.EnergyMomentFinite P N X →
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
  obtain ⟨C₀min, hC⟩ := gf_remainder_pointwise b M K
  refine ⟨C₀min, fun C₀ hC₀ => ?_⟩
  obtain ⟨C, hCpos, hptw⟩ := hC C₀ hC₀
  refine ⟨C, hCpos, ?_⟩
  intro S hS hMF N hN m hmγ EV hEV Ω mΩ P _ X₀ W X hX ℱ W' hF hE Mart hMart Z hZ hZmeas hZc hΞc
  have hT : 0 ≤ S.T := S.hT.le
  have hσ : 0 ≤ sigN S N := sigN_nonneg S N
  obtain ⟨hen0, henI, -, -⟩ := gf_energy_integral_moment S M hMF N hN P X₀ W X hX ⟨ℱ, W', hF⟩ hE
  set R : ℝ → Ω → NegSobolev d m := fun t ω =>
    flucProc m (sigN S N) X (S.ρ N) t ω -
      EV.VE t 0 (EV.j (flucProc (S.γ : ℝ) (sigN S N) X (S.ρ N) 0 ω)) - Z t ω with hR
  set B : ℝ → Ω → ℝ := fun t ω =>
    C * sigN S N * ∫ r in (0 : ℝ)..t, S.energyCompletion N (X (Real.toNNReal r) ω) r with hB
  have hmain : ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) S.T, ‖R t ω‖ ≤ B t ω := by
    refine gf_norm_of_pairings P m S.T R B ?_ ?_ ?_
    · -- continuity of `R`
      filter_upwards [hZc, hΞc] with ω hz hξ
      have h1 : ContinuousOn (fun t => flucProc m (sigN S N) X (S.ρ N) t ω) (Set.Icc 0 S.T) :=
        continuousOn_iff_continuous_restrict.2 hξ
      have h2 : ContinuousOn (fun t : ℝ => EV.VE t 0
          (EV.j (flucProc (S.γ : ℝ) (sigN S N) X (S.ρ N) 0 ω))) (Set.Icc 0 S.T) := by
        have hc := hEV.maxHyp.1.cont_E (EV.j (flucProc (S.γ : ℝ) (sigN S N) X (S.ρ N) 0 ω))
        refine hc.comp (continuousOn_id.prodMk continuousOn_const) fun t ht => ?_
        exact ⟨le_rfl, ht.1, ht.2⟩
      exact (h1.sub h2).sub hz
    · -- continuity of `B`
      filter_upwards [henI] with ω hω
      have hu : IntegrableOn (fun r => S.energyCompletion N (X (Real.toNNReal r) ω) r)
          (Set.uIcc 0 S.T) := by rwa [Set.uIcc_of_le hT]
      have := intervalIntegral.continuousOn_primitive_interval hu
      rw [Set.uIcc_of_le hT] at this
      exact this.const_smul (C * sigN S N)
    · -- the pairing bound
      intro t ht φ hφ
      obtain ⟨hφ2, hφm⟩ := gf_smooth_mem hφ m
      have h1 := gf_mild_identity S M hMF N hN m K hmγ EV hEV P X₀ W X hX ℱ W' hF t ht φ hφ
      have h2 := gf_pair_identification S M N m K EV hEV P ℱ W' W X hF Mart hMart t ht (Z t) (hZ t ht) φ hφ
        (gf_measurable_eval_pair (hZmeas t ht) (gf_smooth_mem hφ m).2)
      filter_upwards [h1, h2, hen0, henI, hX.no_collision] with ω hm1 hm2 hnn hint hnc
      have hev : NegSobolev.eval (R t ω) φ =
          sigN S N * ∫ r in (0 : ℝ)..t, flucInteraction (S.dynM M N)
            (propagator (S.dynM M N) (S.ρ N) r t φ) (X (Real.toNNReal r) ω) (S.ρ N r) := by
        simp only [hR]
        rw [gf_eval_sub _ _ hφ, gf_eval_sub _ _ hφ, hm1, hm2]
        ring
      rw [hev, abs_mul, abs_of_nonneg hσ]
      have hbd : |∫ r in (0 : ℝ)..t, flucInteraction (S.dynM M N)
            (propagator (S.dynM M N) (S.ρ N) r t φ) (X (Real.toNNReal r) ω) (S.ρ N r)| ≤
          C * sobolevNorm m φ * ∫ r in (0 : ℝ)..t, S.energyCompletion N (X (Real.toNNReal r) ω) r := by
        have hint' : IntervalIntegrable (fun r => S.energyCompletion N (X (Real.toNNReal r) ω) r)
            MeasureTheory.volume 0 t := by
          rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht.1]
          exact hint.mono_set (Set.Icc_subset_Icc le_rfl ht.2)
        rw [← Real.norm_eq_abs, ← intervalIntegral.integral_const_mul]
        refine intervalIntegral.norm_integral_le_of_norm_le ht.1 ?_
          (hint'.const_mul (C * sobolevNorm m φ))
        refine Filter.Eventually.of_forall fun r hr => ?_
        have hrT : r ∈ Set.Icc (0 : ℝ) S.T := ⟨hr.1.le, hr.2.trans ht.2⟩
        have hnc' := hnc (Real.toNNReal r) (by rw [Real.coe_toNNReal _ hr.1.le]; exact hrT.2)
        rw [Real.norm_eq_abs]
        exact hptw S hS hMF N hN m hmγ r t hr.1.le hr.2 ht.2 φ hφ2 hφm
          ((hEV.adjoint r t hr.1.le hr.2 ht.2 φ hφ2 hφm).2.1)
          ((hEV.adjoint r t hr.1.le hr.2 ht.2 φ hφ2 hφm).2.2) (X (Real.toNNReal r) ω) hnc'
      calc sigN S N * |∫ r in (0 : ℝ)..t, flucInteraction (S.dynM M N)
              (propagator (S.dynM M N) (S.ρ N) r t φ) (X (Real.toNNReal r) ω) (S.ρ N r)|
          ≤ sigN S N * (C * sobolevNorm m φ *
              ∫ r in (0 : ℝ)..t, S.energyCompletion N (X (Real.toNNReal r) ω) r) :=
            mul_le_mul_of_nonneg_left hbd hσ
        _ = B t ω * sobolevNorm m φ := by simp only [hB]; ring
  filter_upwards [hmain] with ω hω t ht
  exact hω t ht

/-! ### Interface checks: the coupling fields feed GF-WP and GF-LAW (PROVED) -/

section CouplingInterface

variable {Ω Ω' : Type} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω}
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  {ℱ : Filtration ℝ mΩ} {T : ℝ} {𝒢 : InitialSigma ℱ} {M : ℝ → Ω → H}
  {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)} {Db : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)}
  {rel : ℝ → ℝ → Prop} {cost : ℝ → Ω → ℝ} {P' : ProbabilityMeasure Ω'} {π : Ω' → Ω}
  {ℱ' : Filtration ℝ mΩ'} {Gb : ℝ → Ω' → H} {Sd : ℝ → Ω' → (H →L[ℝ] H →L[ℝ] ℝ)}

/-- PROVED.  The `difference` field of the coupling at horizon `T` is exactly the difference-martingale hypothesis of
`gf_wasserstein_comparison` (for `M ∘ π` and `Gb`). -/
theorem gf_coupling_difference
    (h : IsAdaptedGaussianCoupling P ℱ (ENNReal.ofReal T) 𝒢 M Sg Db rel cost P' π ℱ' Gb Sd) (hT : 0 ≤ T) :
    IsHilbertMartingaleWithCovariation (P' : Measure Ω') ℱ' T
      (fun τ ω' => (fun τ' ω'' => M τ' (π ω'')) (min τ T) ω' - Gb (min τ T) ω')
      (fun r ω' => if r ≤ T then Sd r ω' else 0) :=
  h.difference T hT le_rfl

/-- PROVED.  The `cost` field with `rel = (· ≤ ·)` is the cost hypothesis of `gf_wasserstein_comparison`
(with `cost ∘ π`). -/
theorem gf_coupling_cost_le (h : IsAdaptedGaussianCoupling P ℱ (ENNReal.ofReal T) 𝒢 M Sg Db (· ≤ ·) cost
      P' π ℱ' Gb Sd) (hT : 0 ≤ T) :
    ∀ᵐ ω' ∂(P' : Measure Ω'), ∀ r : ℝ, 0 ≤ r → r ≤ T → traceNormForm (Sd r ω') ≤ cost r (π ω') := by
  filter_upwards [h.cost] with ω' hω' r hr0 hrT
  exact hω' r hr0 (ENNReal.ofReal_le_ofReal hrT)

/-- PROVED.  The `indep` field of the coupling gives the independence hypothesis `hGind` of `gf_law_identification` for every
`𝒢`-measurable initial datum `ξ` (composed with `π`). -/
theorem gf_coupling_indep
    (h : IsAdaptedGaussianCoupling P ℱ (ENNReal.ofReal T) 𝒢 M Sg Db rel cost P' π ℱ' Gb Sd) (hT : 0 ≤ T)
    {E' : Type} [mE : MeasurableSpace E'] (ξ : Ω → E') (hξ : Measurable[𝒢.1] ξ) :
    Indep (MeasurableSpace.comap (fun ω' => ξ (π ω')) inferInstance)
      (⨆ τ ∈ Set.Icc (0 : ℝ) T, MeasurableSpace.comap (Gb τ) inferInstance) (P' : Measure Ω') := by
  have h1 : MeasurableSpace.comap (fun ω' => ξ (π ω')) mE ≤ 𝒢.1.comap π := by
    rw [show (fun ω' => ξ (π ω')) = ξ ∘ π from rfl, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hξ.comap_le
  have hset : Set.Icc (0 : ℝ) T = {τ : ℝ | 0 ≤ τ ∧ ENNReal.ofReal τ ≤ ENNReal.ofReal T} := by
    ext τ
    simp only [Set.mem_Icc, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h0, h1⟩; exact ⟨h0, ENNReal.ofReal_le_ofReal h1⟩
    · rintro ⟨h0, h1⟩; exact ⟨h0, (ENNReal.ofReal_le_ofReal_iff hT).1 h1⟩
  rw [hset]
  exact indep_of_indep_of_le_left h.indep h1

end CouplingInterface

end HRS.GF
