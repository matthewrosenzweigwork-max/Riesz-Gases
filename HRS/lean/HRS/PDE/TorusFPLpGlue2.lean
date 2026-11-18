import HRS.PDE.TorusFPLpSpec
import HRS.PDE.MovBAux5

/-!
# D3PHI glue, part 2: the `ε`-level bridge (smooth `V`): D2 + `d3phi_lp_bound`

Models `movb_reg_ineq_smooth` (`MovBAux3`): the law of the level-`M` regularised SDE is the `D1WeakSolution` of the torus
Fokker-Planck equation (D2: `b15e_law_eq_fp`, `d1_fp_exists_proof`), the moving reference `Q^M_r` is the Gibbs measure of the
tilted potential (`movb_gibbs_eq`), the exact source is `movT_srcReg` (`movb_source_eq`); everything is transported by the
measurable equivalence `d1_configEquiv`.  Uses the sorried packet `d3phi_lp_bound` only.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

theorem d3phi_eLpNorm_rnDeriv_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (e : α ≃ᵐ β)
    (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] (p : ℝ≥0∞) :
    eLpNorm ((μ.map e).rnDeriv (ν.map e)) p (ν.map e) = eLpNorm (μ.rnDeriv ν) p ν := by
  have hm : AEStronglyMeasurable ((μ.map e).rnDeriv (ν.map e)) (ν.map e) :=
    (Measure.measurable_rnDeriv _ _).aestronglyMeasurable
  rw [eLpNorm_map_measure hm e.measurable.aemeasurable]
  exact eLpNorm_congr_ae (e.measurableEmbedding.rnDeriv_map μ ν)

theorem d3phi_ac_map_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (e : α ≃ᵐ β)
    (μ ν : Measure α) : μ.map e ≪ ν.map e ↔ μ ≪ ν := by
  refine ⟨fun h => ?_, fun h => h.map e.measurable⟩
  have := h.map e.symm.measurable
  rwa [Measure.map_map e.symm.measurable e.measurable, Measure.map_map e.symm.measurable e.measurable,
    show (e.symm : β → α) ∘ e = id from funext e.symm_apply_apply, Measure.map_id, Measure.map_id] at this


theorem movT_lp_reg_bound_smooth_of_d3phi (hNd : 1 ≤ N * d) (hN : 0 < N) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    (D : DynData d) (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ)) (hκ : 0 < D.invβ)
    (hV : Torus.IsSmooth D.V) {T : ℝ} (hT : 0 < T) {ρ ρt : ℝ → Torus d → ℝ}
    (hρt : IsC12Test T ρ ρt) (hdens : ∀ r ∈ Set.Icc (0 : ℝ) T, IsProbDensity (ρ r))
    (hpos : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 < ρ r x) (M : ℝ) {Y₀ : Ω → Fin N → Euc d}
    (hY₀ : ∀ t : ℝ, Measurable[ℱ t] Y₀) {Y : ℝ → Ω → (Fin N → Euc d)}
    (hY : IsAdditiveSDESolution P ℱ W' (fun _ => b15c_liftedDriftReg D M) (liftedNoise D) Y₀
      (fun _ => ⊤) Y)
    {c Cs ℓ : ℝ} (hc : 0 < c) (hℓ : 0 < ℓ) {L : ℝ → ℝ} (hL : ∀ r ∈ Set.Icc 0 T, ℓ ≤ L r)
    (hLi : IntegrableOn L (Set.Icc 0 T))
    (hexp : ∀ r ∈ Set.Icc 0 T, ∫⁻ X : Config d N,
      ENNReal.ofReal (Real.exp (c * |movT_srcReg D N M ρ ρt r X| / L r))
        ∂(movT_Q (b15c_gReg d D.s M) D N ρ r) ≤ ENNReal.ofReal (Real.exp Cs))
    {p : ℝ → ℝ} (hp : D3phiPath c L p T)
    (hac : selectedLaw P (b15c_regProcess Y) 0 ≪ movT_Q (b15c_gReg d D.s M) D N ρ 0)
    (hfin : eLpNorm ((selectedLaw P (b15c_regProcess Y) 0).rnDeriv
        (movT_Q (b15c_gReg d D.s M) D N ρ 0)) (ENNReal.ofReal (p 0))
        (movT_Q (b15c_gReg d D.s M) D N ρ 0) < ⊤) :
    ∀ t ∈ Set.Icc 0 T,
      selectedLaw P (b15c_regProcess Y) t ≪ movT_Q (b15c_gReg d D.s M) D N ρ t ∧
      eLpNorm ((selectedLaw P (b15c_regProcess Y) t).rnDeriv (movT_Q (b15c_gReg d D.s M) D N ρ t))
          (ENNReal.ofReal (p t)) (movT_Q (b15c_gReg d D.s M) D N ρ t) ≤
        eLpNorm ((selectedLaw P (b15c_regProcess Y) 0).rnDeriv (movT_Q (b15c_gReg d D.s M) D N ρ 0))
            (ENNReal.ofReal (p 0)) (movT_Q (b15c_gReg d D.s M) D N ρ 0) *
          ENNReal.ofReal (Real.exp (d3phi_gain c Cs L p t)) := by
  have hV2 : Torus.IsCk 2 D.V := b15e_isCk_of_isSmooth hV
  have hU := b15d_U_isSmooth_proof (N := N) D hV M
  set e := d1_configEquiv d N with he
  set ψ : ℝ → Torus (N * d) → ℝ := fun r => mova_bigPsi (N := N) (movT_phi D M ρ r) with hψdef
  set ψt : ℝ → Torus (N * d) → ℝ := fun r => mova_bigPsi (N := N) (movT_phit D M ρ ρt r) with hψtdef
  have hψ : IsC12Test T ψ ψt :=
    movb_isC12Test_bigPsi (movb_phi_isC12Test D hV2 M hρt hpos)
  have hρ2 : ∀ r ∈ Set.Icc (0 : ℝ) T, Torus.IsCk 2 (ρ r) := hρt.c2
  have hρc : ∀ r ∈ Set.Icc (0 : ℝ) T, Continuous (ρ r) := fun r hr =>
    mova_continuous_of_isCk (hρ2 r hr)
  have hφ2 : ∀ r ∈ Set.Icc (0 : ℝ) T, Torus.IsCk 2 (movT_phi D M ρ r) := fun r hr =>
    mova_phi_isCk_two D M (hρ2 r hr) (hpos r hr) hV2
  have hgib : ∀ r ∈ Set.Icc (0 : ℝ) T,
      d1_gibbsMeasure D.invβ (d3_tiltPot D.invβ (b15d_U (N := N) D M) (ψ r)) =
        (movT_Q (b15c_gReg d D.s M) D N ρ r).map e := fun r hr =>
    movb_gibbs_eq hN D hκ hV2 M (hdens r hr) (hρc r hr) (hpos r hr)
      (mova_continuous_of_isCk (hφ2 r hr)) (fun x => rfl)
  have hlaw : ∀ r : ℝ, 0 ≤ r → d1_lawOf P Y r = selectedLaw P (b15c_regProcess Y) r :=
    fun r hr => b15e_lawOf_eq_selectedLaw P Y hr
  have hprob : ∀ r : ℝ, IsProbabilityMeasure (selectedLaw P (b15c_regProcess Y) r) := fun r =>
    b15b_selectedLaw_isProb (fun s => b15c_regProcess_measurable hY s) r
  have hQprob : ∀ r ∈ Set.Icc (0 : ℝ) T,
      IsProbabilityMeasure (movT_Q (b15c_gReg d D.s M) D N ρ r) := fun r hr => by
    haveI : IsProbabilityMeasure (withDensityReal (ρ r)) := isProb_withDensityReal (hdens r hr)
    have hg : Continuous (b15c_gReg d D.s M) :=
      b15c_isSmooth_continuous (b15c_gReg_isSmooth (b15_one_le_d D) D.hs0 D.hsd M)
    exact modulatedGibbs_prob_of_continuous hg _ _
  haveI : IsProbabilityMeasure (d1_lawOf P Y 0) :=
    d1_lawOf_isProbabilityMeasure (P := P) (Y := Y) ((hY.adapted 0).mono (ℱ.le 0) le_rfl)
  haveI : IsProbabilityMeasure ((d1_lawOf P Y 0).map e) :=
    (Measure.isProbabilityMeasure_map_iff e.measurable.aemeasurable).2 inferInstance
  obtain ⟨μ, hμ, h0⟩ := d1_fp_exists_proof hNd hκ hU hT ((d1_lawOf P Y 0).map e)
  have heq := b15e_law_eq_fp hNd D hκ rfl hM hV M hW' hY₀ hY hμ h0
  haveI : IsProbabilityMeasure (μ 0) := by rw [h0]; infer_instance
  have h0T : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  -- μ r is the pushforward of the selected law
  have hμe : ∀ r ∈ Set.Icc (0 : ℝ) T, μ r = (selectedLaw P (b15c_regProcess Y) r).map e := fun r hr => by
    rw [← heq r hr, hlaw r hr.1]
  have hqe : ∀ r ∈ Set.Icc (0 : ℝ) T, d3phi_q D.invβ (b15d_U (N := N) D M) ψ r =
      (movT_Q (b15c_gReg d D.s M) D N ρ r).map e := fun r hr => hgib r hr
  have hexp' : ∀ r ∈ Set.Icc 0 T, ∫⁻ x, ENNReal.ofReal (Real.exp (c *
      |d3phi_src D.invβ (b15d_U (N := N) D M) ψ ψt r x| / L r))
      ∂(d3phi_q D.invβ (b15d_U (N := N) D M) ψ r) ≤ ENNReal.ofReal (Real.exp Cs) := by
    intro r hr
    have hrT : r ∈ Set.Icc (0 : ℝ) T := hr
    rw [hqe r hrT, lintegral_map_equiv]
    refine le_trans (le_of_eq ?_) (hexp r hr)
    refine lintegral_congr fun X => ?_
    have := movb_source_eq hN D hM hκ hV2 M (ρt := ρt) (hdens r hrT) (hρc r hrT) (hpos r hrT) (hφ2 r hrT) X
    unfold d3phi_src d3phi_q
    rw [show d3_source D.invβ (b15d_U (N := N) D M) ψ ψt r (e X) +
      ∫ y, ψt r y ∂(d1_gibbsMeasure D.invβ (d3_tiltPot D.invβ (b15d_U (N := N) D M) (ψ r))) =
        movT_srcReg D N M ρ ρt r X from this]
  have hac' : μ 0 ≪ d3phi_q D.invβ (b15d_U (N := N) D M) ψ 0 := by
    rw [hμe 0 h0T, hqe 0 h0T]
    exact (d3phi_ac_map_equiv e _ _).2 hac
  have hfin' : eLpNorm ((μ 0).rnDeriv (d3phi_q D.invβ (b15d_U (N := N) D M) ψ 0))
      (ENNReal.ofReal (p 0)) (d3phi_q D.invβ (b15d_U (N := N) D M) ψ 0) < ⊤ := by
    haveI := hQprob 0 h0T
    haveI := hprob 0
    rw [hμe 0 h0T, hqe 0 h0T, d3phi_eLpNorm_rnDeriv_map]
    exact hfin
  have key := d3phi_lp_bound hNd hκ hU hT hμ hψ hc hℓ hL hLi hexp' hp hac' hfin'
  intro t ht
  obtain ⟨k1, k2⟩ := key t ht
  rw [hμe t ht, hqe t ht, d3phi_ac_map_equiv] at k1
  haveI := hQprob 0 h0T
  haveI := hprob 0
  haveI := hQprob t ht
  haveI := hprob t
  rw [hμe t ht, hqe t ht, d3phi_eLpNorm_rnDeriv_map, hμe 0 h0T, hqe 0 h0T,
    d3phi_eLpNorm_rnDeriv_map] at k2
  exact ⟨k1, k2⟩

end HRS
