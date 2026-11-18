import HRS.MD.EQMild1
import HRS.MD.EQMild2
import HRS.MD.EQMild3
import HRS.MD.Stat
import HRS.Sections.AdjKEFinal

/-!
# EQ-MILD, part 4: `eq_mild_stationary_proof`

Relocated proof of `HRS.MD.EQ29.eq_mild_stationary` (statement verbatim; tie in `HRS/MD/EQMildTie.lean`).

Route.  `T > 0`: the constant path `ρ^t ≡ ρ_β` is an `IsSmoothPositiveTrajectory` (`Q48b`), the stationary flow is a particle system, and B3
(`adjk_mild_decomposition_proof`) gives the identity for `η_N = ζ_N + c`, `c = √N(m_N - μ_β)` deterministic.  Subtracting `c` gives the
`ζ`-identity with the evolving forcing and the extra constant `γ = (Vev(t,0)c - c)(e_k)`.  By `eqmild_forcing_split` the stationary forcing is the
evolving forcing plus a deterministic `E`; taking expectations of the `ζ`-identity (`E ζ = 0` by stationarity, `E Z = 0` for a stochastic
convolution, `E ev = -E`) shows `γ = E`.  `T = 0`: `Z_0 = 0` a.s., `Vev(0,0) = id`, empty interval integral.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MD.EQMild

open HRS HRS.LZ HRS.Uniform HRS.Main HRS.MD.EQ29 HRS.MD.EQRem HRS.Quad

variable {d : ℕ}

theorem eqmild_fourierCoeff_add {M : ℝ} (a b : NegSobolev d M) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (a + b) k = NegSobolev.fourierCoeff a k + NegSobolev.fourierCoeff b k := by
  rw [← eqmild_fc_apply, ← eqmild_fc_apply, ← eqmild_fc_apply, map_add]

/-- The `η`-identity at one point implies the `ζ`-identity with the deterministic correction `γ`. -/
theorem eqmild_alg {M : ℝ} (hM : (d : ℝ) < 2 * M) {N : ℕ} (hN : 1 ≤ N) (G : Measure (Config d N))
    [IsProbabilityMeasure G] (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (Vt : NegSobolev d M →L[ℝ] NegSobolev d M) (Y0 Yt : Config d N) (z : NegSobolev d M)
    (k : NonzeroLattice d) (ev : ℝ)
    (h : NegSobolev.fourierCoeff (etaE M Yt μ) k =
      NegSobolev.fourierCoeff (Vt (etaE M Y0 μ)) k + NegSobolev.fourierCoeff z k + ev) :
    NegSobolev.fourierCoeff (zetaE M G Yt) k =
      NegSobolev.fourierCoeff (Vt (zetaE M G Y0)) k + NegSobolev.fourierCoeff z k + ev +
        (NegSobolev.fourierCoeff (Vt (Real.sqrt N • NegSobolev.ofMeasureDiff M (meanEmpirical G) μ)) k -
          NegSobolev.fourierCoeff (Real.sqrt N • NegSobolev.ofMeasureDiff M (meanEmpirical G) μ) k) := by
  rw [eqmild_eta_eq hM hN G μ, eqmild_eta_eq hM hN G μ] at h
  simp only [map_add, eqmild_fourierCoeff_add] at h
  linarith

/-- Taking expectations of the `ζ`-identity forces the constant to equal `E`. -/
theorem eqmild_expect {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (a b z e : Ω → ℝ) (γ E : ℝ) (ha : Integrable a P) (hb : Integrable b P) (hz : Integrable z P)
    (he : Integrable e P) (ha0 : ∫ ω, a ω ∂P = 0) (hb0 : ∫ ω, b ω ∂P = 0) (hz0 : ∫ ω, z ω ∂P = 0)
    (he0 : ∫ ω, e ω ∂P = -E) (heq : ∀ᵐ ω ∂P, a ω = b ω + z ω + e ω + γ) : γ = E := by
  have h1 : ∫ ω, a ω ∂P = ∫ ω, (b ω + z ω + e ω + γ) ∂P := integral_congr_ae heq
  have i0 : Integrable (fun ω => b ω + z ω) P := hb.add hz
  have i1 : Integrable (fun ω => b ω + z ω + e ω) P := i0.add he
  have h2 : ∫ ω, (b ω + z ω + e ω + γ) ∂P = ∫ ω, (b ω + z ω + e ω) ∂P + γ := by
    rw [integral_add i1 (integrable_const γ)]; simp
  have h3 : ∫ ω, (b ω + z ω + e ω) ∂P = ∫ ω, b ω ∂P + ∫ ω, z ω ∂P + ∫ ω, e ω ∂P := by
    rw [integral_add i0 he, integral_add hb hz]
  rw [h2, h3, ha0, hb0, hz0, he0] at h1
  linarith

theorem eq_mild_stationary_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (M : ℝ) (hM : (d : ℝ) / 2 + 2 < M)
    (T : ℝ) (hT : 0 ≤ T) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hX : IsStationaryGibbsFlow P s hs0 hsd V β hβ T X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsFilteredSolution P ℱ W' W X)
    (Mart : ℝ → Ω → NegSobolev d M)
    (hMart : IsHilbertMartingaleWithCovariation P ℱ T Mart
      (fun r ω => covForm M β⁻¹ (empirical (X r.toNNReal ω))))
    (hMid : ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
      NegSobolev.eval (Mart t ω) φ =
        Real.sqrt N * empiricalMartingale P ℱ W' (PDE.mfData d s hs0 hsd V β hβ) T (fun _ => φ) X t ω)
    (Vev : ℝ → ℝ → NegSobolev d M →L[ℝ] NegSobolev d M)
    (hVev : IsDualEvolution (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) M Vev)
    (Z : ℝ → Ω → NegSobolev d M)
    (hZ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d M)) Mart 0 t (Z t))
    (hZm : ∀ t ∈ Set.Icc (0 : ℝ) T, AEMeasurable (Z t) P)
    (hZc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 T)) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k : NonzeroLattice d,
      NegSobolev.fourierCoeff (zetaE M (P.map (X t.toNNReal)) (X t.toNNReal ω)) k =
        NegSobolev.fourierCoeff (Vev t 0 (zetaE M (P.map (X 0)) (X 0 ω))) k +
          NegSobolev.fourierCoeff (Z t ω) k +
          statForcingCoord d hs0 hsd V hβ ρβ X k t ω := by
  
  classical
  have hN1 : 1 ≤ N := by omega
  have hMd : (d : ℝ) < 2 * M := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  haveI hGprob : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) :=
    eqrem_gibbs_prob hd hs0 hsd V hV hβ hρβ (by omega)
  haveI hμprob : IsProbabilityMeasure (withDensityReal ρβ) := isProb_withDensityReal hρβ.1
  have hstat : ∀ r : ℝ≥0, (r : ℝ) ≤ T → P.map (X r) = canonicalGibbs (periodicRiesz d s) V N β :=
    MD.Stat.md_stat_gibbs_flow_stationary_proof hd hs0 hsd V hV β hβ T hN P X₀ W X hX
  set G := canonicalGibbs (periodicRiesz d s) V N β with hG
  have hmapt : ∀ t ∈ Set.Icc (0 : ℝ) T, P.map (X t.toNNReal) = G := fun t ht =>
    hstat t.toNNReal (by rw [Real.coe_toNNReal _ ht.1]; exact ht.2)
  have hmap0 : P.map (X 0) = G := hstat 0 (by rw [NNReal.coe_zero]; exact hT)
  have hXmeas : ∀ r : ℝ≥0, Measurable (X r) := fun r => (hF.adapted r).mono (ℱ.le r) le_rfl
  have hX0m : AEMeasurable (X 0) P := (hXmeas 0).aemeasurable
  obtain ⟨hρs, -, -, -, -⟩ := eqrem_setup hd hs0 hsd V hV hβ hρβ
  rcases hT.eq_or_lt with h0 | hpos
  · -- T = 0
    subst h0
    have hcoef : ∀ k : NonzeroLattice d, ∀ Y : NegSobolev d M,
        NegSobolev.fourierCoeff (Vev 0 0 Y) k = NegSobolev.fourierCoeff Y k := by
      intro k Y
      rw [eqrem_prop_dual (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) Vev hVev le_rfl le_rfl k Y]
      have hKf := PDE.ClassicalAux.convKernelFacts (by omega : 1 ≤ d) (PDE.mfData d s hs0 hsd V β hβ)
      have hp0 : propagator (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) 0 0 (Torus.realMode k) =
          Torus.realMode k :=
        PDE.MFSemigroup.propagator_zero _ hKf (mova_isCk_one_of_two (mova_isCk_two_of_smooth hV)) _
          (mova_isCk_one_of_two (mova_isCk_two_of_smooth hρs.smooth))
          (mova_isCk_two_of_smooth (eqrem_isSmooth_realMode k))
      rw [hp0, eqrem_eval_realMode]
    have hZ0 : ∀ᵐ ω ∂P, Z 0 ω = 0 := by
      have h := hZ 0 ⟨le_rfl, le_rfl⟩
      have hI : ∫⁻ ω, ‖Z 0 ω‖ₑ ^ 2 ∂P ≤ 0 := by
        refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
        obtain ⟨δ, hδ, hp⟩ := h (ε : ℝ) (by exact_mod_cast hε)
        have := hp 0 (fun _ => 0) rfl rfl (fun _ _ _ => le_rfl) (fun i => i.elim0)
        simp only [riemannSum, Finset.univ_eq_empty, Finset.sum_empty, sub_zero] at this
        simpa using this.le
      have hzero : ∫⁻ ω, ‖Z 0 ω‖ₑ ^ 2 ∂P = 0 := le_antisymm hI bot_le
      have := (lintegral_eq_zero_iff' ((hZm 0 ⟨le_rfl, le_rfl⟩).enorm.pow_const 2)).1 hzero
      filter_upwards [this] with ω hω
      simpa using hω
    filter_upwards [hZ0] with ω hz t ht k
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst ht0
    have hs0' : statForcingCoord d hs0 hsd V hβ ρβ X k 0 ω = 0 := by simp [statForcingCoord]
    have hz' : NegSobolev.fourierCoeff (Z 0 ω) k = 0 := by
      rw [hz, ← eqmild_fc_apply, map_zero]
    simp only [Real.toNNReal_zero]
    rw [hs0', hz', hcoef k]
    ring
  · -- T > 0
    have htr : IsSmoothPositiveTrajectory d s β V ρβ (fun _ => ρβ) :=
      { hs0 := hs0, hsd := hsd, hβ := hβ, V_smooth := hV, init := hρs,
        global := fun K _ => ⟨fun _ => PDE.coeffOf ρβ,
          HRS.Uniform.Q48b.q48b_isMFSolutionHK (by omega) s hs0 hsd β hβ V hV ρβ hρβ hρs.smooth
            hρs.pos K,
          fun t _ => congrFun (HRS.Uniform.Q48b.q48b_mfPath_const ρβ hρs.smooth) t⟩ }
    have hPS : IsParticleSystem P htr.dyn T X₀ W X := by
      refine ⟨hX.flow.brownian, hX.flow.indep, ?_⟩
      rcases hX.flow.flow with ⟨hsol, -⟩ | ⟨h1, -⟩
      · exact hsol
      · omega
    have hB3 := HRS.AdjK.adjk_mild_decomposition_proof hd htr M hM T hpos hN P X₀ W X hPS ℱ W' hF
      Mart hMart hMid Vev hVev Z hZ hZm hZc
    have hInt := (HRS.AdjK.adjk_forcing_intervalIntegrable_proof hd htr hN P X₀ W X T hT hPS
      ⟨ℱ, W', hF⟩).1
    set μ : Measure (Torus d) := withDensityReal ρβ with hμ
    set c : NegSobolev d M :=
      Real.sqrt N • NegSobolev.ofMeasureDiff M (meanEmpirical G) μ with hc
    have hkey : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k : NonzeroLattice d, ∃ E : ℝ,
        (∀ ω : Ω, IntervalIntegrable (fun r =>
          Real.sqrt N * modulatedEnergy
            (commKernel (periodicRieszGrad d htr.dyn.s)
              (Torus.grad (propagator htr.dyn (fun _ => ρβ) r t (Torus.realMode k))))
            (X r.toNNReal ω) (withDensityReal ((fun _ => ρβ) r))) volume 0 t →
          statForcingCoord d hs0 hsd V hβ ρβ X k t ω =
            evolvingForcingCoord htr.dyn (fun _ => ρβ) X k t ω + E) ∧
        NegSobolev.fourierCoeff (Vev t 0 c) k - NegSobolev.fourierCoeff c k = E := by
      intro t ht k
      obtain ⟨E, hE1, hEi, hEint⟩ := eqmild_forcing_split hd hs0 hsd hV hβ hρβ htr hT hN P X₀ W X
        hPS ⟨ℱ, W', hF⟩ hstat ht k
      refine ⟨E, hE1, ?_⟩
      obtain ⟨ha, ha0⟩ := eqmild_zeta_integral hMd hN1 G P (X t.toNNReal)
        (hXmeas _).aemeasurable (hmapt t ht) (eqmild_fc M k)
      obtain ⟨hb, hb0⟩ := eqmild_zeta_integral hMd hN1 G P (X 0) hX0m hmap0
        ((eqmild_fc M k).comp (Vev t 0))
      obtain ⟨hz, hz0⟩ := eqmild_conv_mean P ℱ T Mart _ hMart Vev ht.1 ht.2 (Z t) (hZ t ht)
        (hZm t ht) (eqmild_fc M k)
      refine eqmild_expect P _ _ _ _ _ E ha hb hz hEi ha0 hb0 hz0 hEint ?_
      filter_upwards [hB3] with ω h
      have h' : NegSobolev.fourierCoeff (etaE M (X t.toNNReal ω) μ) k =
          NegSobolev.fourierCoeff (Vev t 0 (etaE M (X 0 ω) μ)) k +
            NegSobolev.fourierCoeff (Z t ω) k +
            evolvingForcingCoord htr.dyn (fun _ => ρβ) X k t ω := h t ht k
      have := eqmild_alg hMd hN1 G μ (Vev t 0) (X 0 ω) (X t.toNNReal ω) (Z t ω) k _ h'
      simp only [ContinuousLinearMap.comp_apply, eqmild_fc_apply]
      exact this
    filter_upwards [hB3, hInt] with ω hω hint t ht k
    obtain ⟨E, hE1, hE2⟩ := hkey t ht k
    rw [hmapt t ht, hmap0, hE1 ω (hint t ht k)]
    have h' : NegSobolev.fourierCoeff (etaE M (X t.toNNReal ω) μ) k =
        NegSobolev.fourierCoeff (Vev t 0 (etaE M (X 0 ω) μ)) k +
          NegSobolev.fourierCoeff (Z t ω) k +
          evolvingForcingCoord htr.dyn (fun _ => ρβ) X k t ω := hω t ht k
    have := eqmild_alg hMd hN1 G μ (Vev t 0) (X 0 ω) (X t.toNNReal ω) (Z t ω) k _ h'
    rw [← hc] at this
    linarith

end HRS.MD.EQMild

end
