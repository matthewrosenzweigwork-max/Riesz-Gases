import HRS.Main.A8PAux3
import HRS.Main.A8PAux7
import HRS.Main.GFB2Aux2
import HRS.Sections.AdjKDFinal

/-!
# Packet MPFLUC: a.s. path continuity and `AEMeasurable` of `flucPath` for `MainData`

Transcription of `gf_fluc_continuous_proof` (GFB2Aux2) and `adjkd_flucPath_aemeasurable` (AdjKDAux1)
to the torus standing hypotheses `TorusStanding` (`MainData`, `Realization`).  The particle path comes from
`a8p_flow_facts` (`IsContactStrongSolution`), the mean-field path from `a8p_rho_cont_time`, `a8p_rho_le`
and the weak continuity field of `a8p_coeffHyp`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MP.FlucPath

open HRS HRS.GF HRS.Uniform

variable {d : ℕ}

/-- Weak time continuity of `t ↦ ∫ ψ ρ_N(t)` on `[0,T]` under the standing hypotheses. -/
theorem mpf_weak {S : HRS.Main.MainData d} {R : ∀ N, HRS.Main.Realization d N} {Rg : HRS.PDE.Regime}
    {ν₀ MB Λ VB C₀ Cc : ℝ} {𝔈 : ℕ → ℝ}
    (hS : HRS.Main.TorusStanding S R Rg ν₀ MB Λ VB (HRS.PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N)
    (ψ : Torus d → ℝ) (hψ : Continuous ψ) :
    ContinuousOn (fun t => ∫ x, ψ x * S.ρ N t x) (Set.Icc 0 S.T) :=
  (HRS.Main.A8P.a8p_coeffHyp hS hN).cont ψ hψ

/-- Path continuity of the rescaled fluctuation field for a continuous particle path (`MainData` version
of `gfb2_fluc_cont_path`), with `d < 2q`. -/
theorem mpf_fluc_cont_path {S : HRS.Main.MainData d} {R : ∀ N, HRS.Main.Realization d N}
    {Rg : HRS.PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ} {𝔈 : ℕ → ℝ}
    (hS : HRS.Main.TorusStanding S R Rg ν₀ MB Λ VB (HRS.PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N)
    (q : ℝ) (hq : (d : ℝ) < 2 * q) {Ω : Type*} (X : ℝ≥0 → Ω → Config d N) (σ : ℝ) (ω : Ω)
    (hc : ∀ i, Continuous fun t : ℝ≥0 => X t ω i) :
    Continuous fun t : Set.Icc (0 : ℝ) S.T => flucProc q σ X (S.ρ N) t ω := by
  have hm2 := hq
  have hweak := mpf_weak hS hN
  have hMFN := hS.mean_field.solution N hN
  have hprob : ∀ t : Set.Icc (0 : ℝ) S.T, IsProbabilityMeasure (withDensityReal (S.ρ N t)) :=
    fun t => isProb_withDensityReal (hMFN.density t.1 t.2)
  have hb : Summable fun k : NonzeroLattice d => σ ^ 2 * (8 * Lattice.jp k.1 ^ (-(2 * q))) :=
    ((summable_jp_rpow (d := d) q hm2).mul_left 8).mul_left (σ ^ 2)
  have hcoord : ∀ (t : Set.Icc (0 : ℝ) S.T) (k : NonzeroLattice d),
      NegSobolev.coord (flucProc q σ X (S.ρ N) t ω) k =
        σ * (Lattice.jp k.1 ^ (-q) * ((N : ℝ)⁻¹ * ∑ i, Torus.realMode k (X (Real.toNNReal t) ω i) -
          ∫ x, Torus.realMode k x * S.ρ N t x)) := by
    intro t k
    haveI := hprob t
    unfold flucProc
    have h1 : NegSobolev.coord (σ • NegSobolev.ofMeasureDiff q (empirical (X (Real.toNNReal t) ω))
        (withDensityReal (S.ρ N t))) k =
        σ * NegSobolev.coord (NegSobolev.ofMeasureDiff q (empirical (X (Real.toNNReal t) ω))
        (withDensityReal (S.ρ N t))) k := rfl
    rw [h1, coord_ofMeasureDiff hm2]
    congr 2
    congr 1
    · unfold Torus.measureRealCoeff
      exact integral_empirical _ (continuous_realMode' k)
    · unfold Torus.measureRealCoeff
      rw [integral_withDensityReal_eq _ (hMFN.density t.1 t.2).measurable (hMFN.density t.1 t.2).nonneg]
      exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  refine gfb2_continuous_of_coords _ _ hb (fun t k => ?_) (fun k => ?_)
  · haveI := hprob t
    haveI : IsFiniteMeasure (empirical (X (Real.toNNReal t) ω)) := inferInstance
    have := gfb2_coord_sq_le (m := q) hm2 (empirical (X (Real.toNNReal t) ω)) (withDensityReal (S.ρ N t))
      (by
        have := gfb2_empirical_mass (X (Real.toNNReal t) ω)
        have h2 := ENNReal.toReal_mono ENNReal.one_ne_top this
        simpa using h2)
      (by simp) k
    have e : NegSobolev.coord (flucProc q σ X (S.ρ N) t ω) k =
        σ * NegSobolev.coord (NegSobolev.ofMeasureDiff q (empirical (X (Real.toNNReal t) ω))
          (withDensityReal (S.ρ N t))) k := rfl
    rw [e, mul_pow]
    exact mul_le_mul_of_nonneg_left this (sq_nonneg σ)
  · simp only [hcoord]
    refine continuous_const.mul (continuous_const.mul (Continuous.sub ?_ ?_))
    · refine continuous_const.mul (continuous_finset_sum _ fun i _ => ?_)
      exact (continuous_realMode' k).comp ((hc i).comp (continuous_real_toNNReal.comp continuous_subtype_val))
    · exact (hweak (Torus.realMode k) (continuous_realMode' k)).comp_continuous continuous_subtype_val
        (fun t => t.2)

/-- **MPFLUC A.11-form statement** for `MainData` (transcription of `gf_fluc_continuous_proof`): for each
`N ≥ 1` and `d < 2q`, the rescaled fluctuation field has a.s. continuous paths in `E_q` and `flucPath` is
`AEMeasurable`. -/
theorem mpf_fluc_cont_meas {S : HRS.Main.MainData d} {R : ∀ N, HRS.Main.Realization d N}
    {Rg : HRS.PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ} {𝔈 : ℕ → ℝ}
    (hS : HRS.Main.TorusStanding S R Rg ν₀ MB Λ VB (HRS.PDE.mStar d) C₀ Cc 𝔈)
    {N : ℕ} (hN : 1 ≤ N) (q : ℝ) (hq : (d : ℝ) < 2 * q) :
    (∀ᵐ ω ∂(R N).P, Continuous fun t : Set.Icc (0 : ℝ) S.T =>
        S.sigma N • NegSobolev.ofMeasureDiff q (HRS.empirical ((R N).X (Real.toNNReal t) ω))
          (HRS.withDensityReal (S.ρ N t))) ∧
    AEMeasurable (HRS.flucPath q S.T (S.sigma N) (R N).X (S.ρ N)) (R N).P := by
  classical
  have hX := (HRS.Main.A8P.a8p_flow_facts hS hN).1
  have hcont : ∀ᵐ ω ∂(R N).P, Continuous fun t : Set.Icc (0 : ℝ) S.T =>
      flucProc q (S.sigma N) (R N).X (S.ρ N) t ω := by
    filter_upwards [hX.cont] with ω hω using mpf_fluc_cont_path hS hN q hq (R N).X (S.sigma N) ω hω
  refine ⟨hcont, ?_⟩
  obtain ⟨Nn, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hcont)
  let g : (R N).Ω → PathSpace d q S.T := fun ω =>
    if ω ∈ Nn then 0 else HRS.flucPath q S.T (S.sigma N) (R N).X (S.ρ N) ω
  have hmeas : ∀ s : ℝ, Measurable fun ω => flucProc q (S.sigma N) (R N).X (S.ρ N) s ω := by
    intro s
    unfold flucProc
    refine (measurable_const_smul (S.sigma N)).comp ?_
    exact (gf_measurable_ofMeasureDiff_proof (N := N) q (by linarith) _).comp (hX.adapted _)
  have hg : Measurable g := by
    refine ContinuousMap.measurable_iff_eval.2 fun s => ?_
    have hfun : (fun ω => (show C(Set.Icc (0 : ℝ) S.T, NegSobolev d q) from g ω) s) =
        fun ω => if ω ∈ Nn then 0 else flucProc q (S.sigma N) (R N).X (S.ρ N) s ω := by
      funext ω
      by_cases hω : ω ∈ Nn
      · simp [g, hω]
        rfl
      · have hc : Continuous fun t : Set.Icc (0 : ℝ) S.T =>
            flucProc q (S.sigma N) (R N).X (S.ρ N) t ω := by
          by_contra hnc
          exact hω (hNsub hnc)
        simp only [g, hω, if_false]
        have e : HRS.flucPath q S.T (S.sigma N) (R N).X (S.ρ N) ω =
            (show PathSpace d q S.T from
              (⟨fun t : Set.Icc (0 : ℝ) S.T => S.sigma N • NegSobolev.ofMeasureDiff q
                (empirical ((R N).X (Real.toNNReal t) ω)) (withDensityReal (S.ρ N t)), hc⟩ :
                C(Set.Icc (0 : ℝ) S.T, NegSobolev d q))) := by
          unfold HRS.flucPath
          exact dif_pos hc
        rw [e]
        rfl
    rw [hfun]
    exact Measurable.ite hNm measurable_const (hmeas s)
  refine ⟨g, hg, ?_⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
  simp [g, hω]

/-- **MPFLUC Y-side**: a continuous linear fluctuation solution has `AEMeasurable` path `toPath`
(instance of `adjk_toPath_aemeasurable_proof`). -/
theorem mpf_toPath_aemeasurable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P' : Measure Ω}
    {D : HRS.DynData d} {ρ : ℝ → Torus d → ℝ} {m q T : ℝ} {Y₀ : Ω → NegSobolev d m}
    {Y : ℝ → Ω → NegSobolev d m} (hY : HRS.IsLinearFluctuationSolution P' D ρ m q T Y₀ Y) :
    AEMeasurable (HRS.toPath m T Y) P' :=
  HRS.AdjK.adjk_toPath_aemeasurable_proof P' m T Y hY.meas hY.cont

end HRS.MP.FlucPath
