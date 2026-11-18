import HRS.PDE.MovBAux2

/-!
# MOVB, part 3: the level-`k` inequality (smooth `V`): D2 + D3 in the `selectedLaw`/`movT_Q` language

`movb_reg_ineq_smooth`: for `V` smooth, any `C^{1,2}` positive probability density path `ρ` (no mean-field equation), the law of
the level-`M` regularised SDE satisfies the moving-reference inequality with source `movT_srcReg` (Fisher term dropped).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

theorem movb_isCk_of_smooth' {V : Torus d → ℝ} (h : Torus.IsSmooth V) : Torus.IsCk 2 V :=
  b15e_isCk_of_isSmooth h

theorem movb_reg_ineq_smooth (hNd : 1 ≤ N * d) (hN : 0 < N) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    (D : DynData d) (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ)) (hκ : 0 < D.invβ)
    (hV : Torus.IsSmooth D.V) {T : ℝ} (hT : 0 < T) {ρ ρt : ℝ → Torus d → ℝ}
    (hρt : IsC12Test T ρ ρt) (hdens : ∀ r ∈ Set.Icc (0 : ℝ) T, IsProbDensity (ρ r))
    (hpos : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 < ρ r x) (M : ℝ) {Y₀ : Ω → Fin N → Euc d}
    (hY₀ : ∀ t : ℝ, Measurable[ℱ t] Y₀) {Y : ℝ → Ω → (Fin N → Euc d)}
    (hY : IsAdditiveSDESolution P ℱ W' (fun _ => b15c_liftedDriftReg D M) (liftedNoise D) Y₀
      (fun _ => ⊤) Y)
    (hfin : relEntropy (selectedLaw P (b15c_regProcess Y) 0)
      (movT_Q (b15c_gReg d D.s M) D N ρ 0) ≠ ⊤) :
    ∀ t ∈ Set.Icc 0 T,
      relEntropy (selectedLaw P (b15c_regProcess Y) t) (movT_Q (b15c_gReg d D.s M) D N ρ t) ≠ ⊤ ∧
      (relEntropy (selectedLaw P (b15c_regProcess Y) t) (movT_Q (b15c_gReg d D.s M) D N ρ t)).toReal ≤
        (relEntropy (selectedLaw P (b15c_regProcess Y) 0) (movT_Q (b15c_gReg d D.s M) D N ρ 0)).toReal +
        ∫ r in Set.Icc 0 t, ∫ Z, movT_srcReg D N M ρ ρt r Z ∂(selectedLaw P (b15c_regProcess Y) r) := by
  have hV2 : Torus.IsCk 2 D.V := movb_isCk_of_smooth' hV
  have hU := b15d_U_isSmooth_proof (N := N) D hV M
  set e := d1_configEquiv d N with he
  -- the tilt
  set ψ : ℝ → Torus (N * d) → ℝ := fun r => mova_bigPsi (N := N) (movT_phi D M ρ r) with hψdef
  set ψt : ℝ → Torus (N * d) → ℝ := fun r => mova_bigPsi (N := N) (movT_phit D M ρ ρt r) with hψtdef
  have hψ : IsC12Test T ψ ψt :=
    movb_isC12Test_bigPsi (movb_phi_isC12Test D hV2 M hρt hpos)
  -- slice facts
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
  have hprob : ∀ r : ℝ, IsProbabilityMeasure (selectedLaw P (b15c_regProcess Y) r) := fun r =>
    b15b_selectedLaw_isProb (fun s => b15c_regProcess_measurable hY s) r
  have hQprob : ∀ r ∈ Set.Icc (0 : ℝ) T,
      IsProbabilityMeasure (movT_Q (b15c_gReg d D.s M) D N ρ r) := fun r hr => by
    haveI : IsProbabilityMeasure (withDensityReal (ρ r)) := isProb_withDensityReal (hdens r hr)
    have hg : Continuous (b15c_gReg d D.s M) :=
      b15c_isSmooth_continuous (b15c_gReg_isSmooth (b15_one_le_d D) D.hs0 D.hsd M)
    exact modulatedGibbs_prob_of_continuous hg _ _
  have hlaw : ∀ r : ℝ, 0 ≤ r → d1_lawOf P Y r = selectedLaw P (b15c_regProcess Y) r :=
    fun r hr => b15e_lawOf_eq_selectedLaw P Y hr
  -- entropies agree
  have hent : ∀ r ∈ Set.Icc (0 : ℝ) T,
      relEntropy ((d1_lawOf P Y r).map e) (d1_gibbsMeasure D.invβ (d3_tiltPot D.invβ (b15d_U (N := N) D M) (ψ r))) =
        relEntropy (selectedLaw P (b15c_regProcess Y) r) (movT_Q (b15c_gReg d D.s M) D N ρ r) := by
    intro r hr
    haveI := hprob r
    haveI := hQprob r hr
    rw [hgib r hr, hlaw r hr.1]
    unfold relEntropy
    exact b15e_klDiv_map_equiv e _ _
  -- the FP solution
  haveI : IsProbabilityMeasure (d1_lawOf P Y 0) :=
    d1_lawOf_isProbabilityMeasure (P := P) (Y := Y) ((hY.adapted 0).mono (ℱ.le 0) le_rfl)
  haveI : IsProbabilityMeasure ((d1_lawOf P Y 0).map e) :=
    (Measure.isProbabilityMeasure_map_iff e.measurable.aemeasurable).2 inferInstance
  obtain ⟨μ, hμ, h0⟩ := d1_fp_exists_proof hNd hκ hU hT ((d1_lawOf P Y 0).map e)
  have heq := b15e_law_eq_fp hNd D hκ rfl hM hV M hW' hY₀ hY hμ h0
  haveI : IsProbabilityMeasure (μ 0) := by rw [h0]; infer_instance
  have h0T : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  have hfin' : relEntropy (μ 0) (d1_gibbsMeasure D.invβ (d3_tiltPot D.invβ (b15d_U (N := N) D M) (ψ 0))) ≠ ⊤ := by
    rw [h0, hent 0 h0T]; exact hfin
  intro t ht
  obtain ⟨h1, h2, h3⟩ := d3_entropy_moving_proof hNd hκ hU hT hμ hψ hfin' t ht
  rw [← heq t ht, hent t ht] at h1
  refine ⟨h1, ?_⟩
  rw [← heq t ht, hent t ht, h0, hent 0 h0T] at h3
  have hI : 0 ≤ D.invβ * (∫⁻ r in Set.Icc 0 t, d1_fisherInfo D.invβ
      (d3_tiltPot D.invβ (b15d_U (N := N) D M) (ψ r)) (μ r)).toReal :=
    mul_nonneg hκ.le ENNReal.toReal_nonneg
  have h3' := le_trans (le_add_of_nonneg_right hI) h3
  refine h3'.trans (le_of_eq ?_)
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
  have hrT : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans ht.2⟩
  rw [← heq r hrT, hlaw r hr.1, integral_map_equiv]
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  exact movb_source_eq hN D hM hκ hV2 M (hdens r hrT) (hρc r hrT) (hpos r hrT) (hφ2 r hrT) X

end HRS
