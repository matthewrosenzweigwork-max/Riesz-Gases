import HRS.MS.Fp81S21InitialTransport2
import HRS.MS.Fp81S21InitRecon

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.GenPath

/-- The sequence-space residual from the actual-law expansion: empirical
centering uses the actual first marginal, and the cubic correction has its
stated `1/6` coefficient. -/
def fp81s21_staticResidual {p : Parameters} {δ : ℝ}
    (R : Trajectory p δ) (N : ℕ) (a : ℝ)
    (G : Measure SeqL2) (F : SeqL2 → ℝ) : ℝ :=
  Real.sqrt N *
    ((∫ X, F (featureVec (r26t3_qwin R a) (r26t3_marg R N) X)
        ∂(r26t3_Q R N)) - ∫ z, F z ∂G) -
    (1 / 6) * ∫ z, ∫ x,
      iteratedFDeriv ℝ 3 F z
        ![fp81s21_initial_ellv R (r26t3_qwin R a) x,
          fp81s21_initial_ellv R (r26t3_qwin R a) x,
          fp81s21_initial_ellv R (r26t3_qwin R a) x]
      ∂(r26t3_mu R 0) ∂G

/-- The signed initial remainder is exactly the sequence-space static
residual after pulling the heat test back along the initial Gaussian
synthesis. -/
theorem fp81s21_initial_remainder_eq_staticResidual (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        (0 < p.γ ∨ p.γ = 0) →
        ∀ [IsProbabilityMeasure (r26t3_mu R 0)],
        ∀ future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d) H),
          ((∀ H v, IsProbabilityMeasure (future H v)) ∧
            ∀ H : ℝ, 0 < H → ∀ v ∈ Set.Icc (0 : ℝ) H,
              IsR2FutureGaussian (r26t3_coeff R) (wholeSpaceIndex p.d) H v
                (future H v)) →
          ∀ a : ℝ, ∀ ha : 0 ≤ a,
          ∀ (G : Measure SeqL2) [IsProbabilityMeasure G],
            IsCenteredGaussianSeq G (fun i j =>
              HRS.Whole.susceptibilityCov (rieszKernel p.d p.s)
                (r26t3_mu R 0) p.γ
                (r26t3_qwin R a i) (r26t3_qwin R a j)) →
            ∀ G0 : GaussianRealization R, ∀ N : ℕ, 2 ≤ N →
              ∀ Φ : Window p → ℝ, Φ ∈ CbUnitBall (Window p) 5 →
                initialRemainder R future N G0 a ha Φ =
                  fp81s21_staticResidual R N a G
                    (fun z => initialHeat future a ha Φ 0
                      (fp81s21_initGauss_synthesis p z)) := by
  obtain ⟨δlaw, hlaw0, hlawHalf, hlaw⟩ :=
    fp81s21_initial_future_window_law p
  obtain ⟨δtransport, htransport0, htransportHalf, htransport⟩ :=
    fp81s21_initial_heat_cubic_transport p
  obtain ⟨δrecon, hrecon0, hreconHalf, hrecon⟩ :=
    fp81s21_initRecon_path p
  let δ0 := min δlaw (min δtransport δrecon)
  have hδ0 : 0 < δ0 := by
    dsimp [δ0]
    exact lt_min hlaw0 (lt_min htransport0 hrecon0)
  have hδ0Half : δ0 ≤ 1 / 2 := by
    dsimp [δ0]
    exact (min_le_left _ _).trans hlawHalf
  refine ⟨δ0, hδ0, hδ0Half, ?_⟩
  intro δ hδ hδle R hγ hμ future hf a ha G hGprob hG G0 N hN Φ hΦ
  have hδlaw : δ ≤ δlaw := hδle.trans (by
    dsimp [δ0]
    exact min_le_left _ _)
  have hδtransport : δ ≤ δtransport := hδle.trans (by
    dsimp [δ0]
    exact (min_le_right _ _).trans (min_le_left _ _))
  have hδrecon : δ ≤ δrecon := hδle.trans (by
    dsimp [δ0]
    exact (min_le_right _ _).trans (min_le_right _ _))
  have hδHalf : δ ≤ 1 / 2 := hδle.trans hδ0Half
  haveI : IsProbabilityMeasure (r26t3_mu R 0) := hμ
  haveI : IsProbabilityMeasure G := hGprob
  have hLaw := hlaw δ hδ hδlaw R future hf a ha G hG G0
  have hCubic := htransport δ hδ hδtransport R hγ future hf a ha G hG G0 Φ hΦ
  let S : SeqL2 →L[ℝ] Window p := fp81s21_initGauss_synthesis p
  let F : SeqL2 → ℝ := fun z => initialHeat future a ha Φ 0 (S z)
  let ν : Measure (Window p) := windowFuture future a ha 0
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν, windowFuture]
    exact (Measure.isProbabilityMeasure_map_iff
      (HRS.MS.ProClosureS111.physicalWindowRestriction
        (d := p.d) (m := wholeSpaceIndex p.d) (T := p.T)
        (H := a + p.T) ha le_rfl).continuous.aemeasurable).2
      (hf.1 (a + p.T) 0)
  let GS : Measure (Window p) := Measure.map S G
  haveI : IsProbabilityMeasure GS := by
    dsimp [GS]
    exact (Measure.isProbabilityMeasure_map_iff S.continuous.aemeasurable).2 inferInstance
  have hPhiBound : ∀ y : Window p, ‖Φ y‖ ≤ 1 := by
    intro y
    simpa using HRS.MC.E213U6.u6_norm_iteratedFDeriv_le
      (j := 0) hΦ (by norm_num) y
  have hHeatMean :
      (∫ z, F z ∂G) = ∫ z, ∫ w, Φ (S z + w) ∂ν ∂G := by
    apply integral_congr_ae
    filter_upwards with z
    change initialHeat future a ha Φ 0 (S z) =
      ∫ w, Φ (S z + w) ∂ν
    rfl
  have hsourceInt : Integrable
      (fun yw : SeqL2 × Window p => Φ (S yw.1 + yw.2)) (G.prod ν) := by
    apply Integrable.of_bound (C := 1)
    · exact (hΦ.1.continuous.comp
        ((S.continuous.comp continuous_fst).add continuous_snd)).aestronglyMeasurable
    · filter_upwards with yw
      simpa using hPhiBound (S yw.1 + yw.2)
  have htargetInt : Integrable
      (fun yw : Window p × Window p => Φ (yw.1 + yw.2)) (GS.prod ν) := by
    apply Integrable.of_bound (C := 1)
    · exact (hΦ.1.continuous.comp (continuous_fst.add continuous_snd)).aestronglyMeasurable
    · filter_upwards with yw
      simpa using hPhiBound (yw.1 + yw.2)
  have hmapProd : GS.prod ν =
      Measure.map (Prod.map S id) (G.prod ν) := by
    simpa [GS] using
      (Measure.map_prod_map G ν (f := S) (g := id)
        S.continuous.measurable measurable_id)
  have hproduct :
      (∫ yw : SeqL2 × Window p, Φ (S yw.1 + yw.2) ∂(G.prod ν)) =
      ∫ yw : Window p × Window p, Φ (yw.1 + yw.2) ∂(GS.prod ν) := by
    rw [hmapProd]
    exact (integral_map
      (S.continuous.measurable.prodMap measurable_id).aemeasurable
      ((hΦ.1.continuous.comp (continuous_fst.add continuous_snd)).aestronglyMeasurable)).symm
  have hproductIter :
      (∫ z, ∫ w, Φ (S z + w) ∂ν ∂G) =
        ∫ yw : Window p × Window p, Φ (yw.1 + yw.2) ∂(GS.prod ν) := by
    calc
      (∫ z, ∫ w, Φ (S z + w) ∂ν ∂G) =
          ∫ yw : SeqL2 × Window p, Φ (S yw.1 + yw.2) ∂(G.prod ν) :=
            (integral_prod _ hsourceInt).symm
      _ = ∫ yw : Window p × Window p, Φ (yw.1 + yw.2) ∂(GS.prod ν) := hproduct
  have haddMeas : Measurable (fun yw : Window p × Window p => yw.1 + yw.2) :=
    (continuous_fst.add continuous_snd).measurable
  have hsumIntegral :
      (∫ yw : Window p × Window p, Φ (yw.1 + yw.2) ∂(GS.prod ν)) =
        ∫ z, Φ z ∂law G0.P (r26t3_Zpath G0 a) := by
    calc
      (∫ yw : Window p × Window p, Φ (yw.1 + yw.2) ∂(GS.prod ν)) =
          ∫ z, Φ z ∂Measure.map (fun yw : Window p × Window p => yw.1 + yw.2)
            (GS.prod ν) := (integral_map haddMeas.aemeasurable
              hΦ.1.continuous.aestronglyMeasurable).symm
      _ = ∫ z, Φ z ∂law G0.P (r26t3_Zpath G0 a) := by rw [hLaw]
  let Y0 : ℝ → G0.Ω → OscDual p.d (wholeSpaceIndex p.d) :=
    fun t w => G0.Z (a + t) w
  have hcontG0 : ∀ᵐ w ∂G0.P,
      ContinuousOn (fun t : ℝ => G0.Z (a + t) w) (Set.Icc (0 : ℝ) p.T) := by
    have hHorizon : 0 ≤ a + p.T := by linarith [ha, p.hT.le]
    filter_upwards [(G0.evolution (a + p.T)).cont] with w hw
    exact hw.comp (continuousOn_const.add continuousOn_id) fun t ht =>
      ⟨by linarith [ha, ht.1], by linarith [ht.2]⟩
  have hIdMeas : Measurable
      (fun z : HRS.Uniform.PathSp p.T (OscDual p.d (wholeSpaceIndex p.d)) =>
        (z : Window p)) := continuous_id.measurable
  have hpathMeas : AEMeasurable (r26t3_Zpath G0 a) G0.P := by
    have hHorizon : 0 ≤ a + p.T := by linarith [ha, p.hT.le]
    have hUniform := HRS.GF.gfb4_aemeasurable_windowPath G0.P p.hT.le Y0
      (fun t _ => (G0.evolution (a + p.T)).meas (a + t)) hcontG0
    have hUniformOsc : AEMeasurable
        (fun w => (HRS.Uniform.windowPath 0 p.T Y0 w : Window p)) G0.P :=
      hIdMeas.comp_aemeasurable hUniform
    have hshift : r26t3_Zpath G0 a =
        (fun w => (HRS.Uniform.windowPath 0 p.T Y0 w : Window p)) := by
      simpa only [processWindow] using
        (show r26t3_Zpath G0 a = processWindow (wholeSpaceIndex p.d)
          p.T 0 Y0 from by
          funext w
          simpa [r26t3_Zpath, Y0] using
            (HRS.Whole.S79.s79p_processWindow_shift p.T a G0.Z w)).trans
          (s56_wpo_eq_windowPath Y0)
    rw [hshift]
    exact hUniformOsc
  have hpathMean :
      (∫ z, Φ z ∂law G0.P (r26t3_Zpath G0 a)) =
        ∫ w, Φ (r26t3_Zpath G0 a w) ∂G0.P := by
    rw [HRS.law]
    exact integral_map hpathMeas hΦ.1.continuous.aestronglyMeasurable
  have hmean :
      (∫ z, F z ∂G) = ∫ w, Φ (r26t3_Zpath G0 a w) ∂G0.P := by
    calc
      (∫ z, F z ∂G) = ∫ z, ∫ w, Φ (S z + w) ∂ν ∂G := hHeatMean
      _ = ∫ yw : Window p × Window p, Φ (yw.1 + yw.2) ∂(GS.prod ν) := hproductIter
      _ = ∫ z, Φ z ∂law G0.P (r26t3_Zpath G0 a) := hsumIntegral
      _ = ∫ w, Φ (r26t3_Zpath G0 a w) ∂G0.P := hpathMean
  have hRecon : ∀ X : EucConfig p.d N,
      initialWindow R N a X =
        S (featureVec (r26t3_qwin R a) (r26t3_marg R N) X) := by
    intro X
    have h := hrecon δ hδ hδrecon R hγ N hN a ha X
    change S (r26t3_W R (r26t3_qwin R a) N X) = initialWindow R N a X at h
    rw [r26t3_W] at h
    exact h.symm
  have hParticle :
      (∫ X, initialHeat future a ha Φ 0 (initialWindow R N a X)
          ∂(r26t3_Q R N)) =
        ∫ X, F (featureVec (r26t3_qwin R a) (r26t3_marg R N) X)
          ∂(r26t3_Q R N) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun X => by
      simpa [F] using congrArg (fun y => initialHeat future a ha Φ 0 y)
        (hRecon X)
  unfold initialRemainder fp81s21_staticResidual
  rw [hParticle, hmean, hCubic]

#print axioms fp81s21_initial_remainder_eq_staticResidual

end HRS.Fp81.S21

end
