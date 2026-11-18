import HRS.MS.Fp81S21InitialTransport
import HRS.MS.Fp81S21RespIid3
import HRS.MS.Fp81S21InitialFutureLaw6
import HRS.MS.Fp81S21GaussLaw2
import HRS.MS.GenPathAux36
import HRS.Main.GFB4Aux13

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S21E HRS.MS.GenPath

/-- Transport the cubic derivative of the heat test through the initial
Gaussian synthesis and the independent initial/future sum law.  The three
response slots are all pushed by the synthesis map. -/
theorem fp81s21_initial_heat_cubic_transport (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        (0 < p.γ ∨ p.γ = 0) →
        ∀ [IsProbabilityMeasure (r26t3_mu R 0)] ,
        ∀ future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d) H),
          ((∀ H v, IsProbabilityMeasure (future H v)) ∧
            ∀ H : ℝ, 0 < H → ∀ v ∈ Set.Icc (0 : ℝ) H,
              IsR2FutureGaussian (r26t3_coeff R) (wholeSpaceIndex p.d) H v
                (future H v)) →
          ∀ a : ℝ, ∀ ha : 0 ≤ a,
          ∀ (G : Measure SeqL2) [IsProbabilityMeasure G],
            (hG : IsCenteredGaussianSeq G (fun i j =>
              HRS.Whole.susceptibilityCov (rieszKernel p.d p.s)
                (r26t3_mu R 0) p.γ
                (r26t3_qwin R a i) (r26t3_qwin R a j))) →
            ∀ G0 : GaussianRealization R, ∀ Φ : Window p → ℝ,
              Φ ∈ CbUnitBall (Window p) 5 →
              ∫ z, ∫ x,
                  iteratedFDeriv ℝ 3
                    (fun y => initialHeat future a ha Φ 0
                      (fp81s21_initGauss_synthesis p y)) z
                    ![fp81s21_initial_ellv R (r26t3_qwin R a) x,
                      fp81s21_initial_ellv R (r26t3_qwin R a) x,
                      fp81s21_initial_ellv R (r26t3_qwin R a) x]
                  ∂(r26t3_mu R 0) ∂G =
                (∫ w, initialKappa R a
                  (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath G0 a w)) ∂G0.P) := by
  obtain ⟨δlaw, hlaw0, hlawHalf, hlaw⟩ :=
    fp81s21_initial_future_window_law p
  obtain ⟨δresp, hresp0, hrespHalf, hresp⟩ :=
    fp81s21_respIid_initialKappa_common p
  obtain ⟨δq, hq0, hqHalf, hqwin⟩ := fp81s21_qwin_uniform p
  let δ0 := min δlaw (min δresp δq)
  have hδ0 : 0 < δ0 := by
    dsimp [δ0]
    exact lt_min hlaw0 (lt_min hresp0 hq0)
  have hδ0Half : δ0 ≤ 1 / 2 := by
    dsimp [δ0]
    exact (min_le_left _ _).trans hlawHalf
  refine ⟨δ0, hδ0, hδ0Half, ?_⟩
  intro δ hδ hδle R hγ hμ future hf a ha G hGprob hG G0 Φ hΦ
  have hδlaw : δ ≤ δlaw := hδle.trans (by
    dsimp [δ0]
    exact min_le_left _ _)
  have hδresp : δ ≤ δresp := hδle.trans (by
    dsimp [δ0]
    exact (min_le_right _ _).trans (min_le_left _ _))
  have hδq : δ ≤ δq := hδle.trans (by
    dsimp [δ0]
    exact (min_le_right _ _).trans (min_le_right _ _))
  have hδHalf : δ ≤ 1 / 2 := hδle.trans hδ0Half
  haveI : IsProbabilityMeasure (r26t3_mu R 0) := hμ
  haveI : IsProbabilityMeasure G := hGprob
  obtain ⟨_, _, hqfamily⟩ := hqwin δ hδ hδq R
  have hq : IsSummableFeatureFamily (r26t3_J p.d) (r26t3_qwin R a) :=
    (hqfamily a ha).1
  have hLaw := hlaw δ hδ hδlaw R future hf a ha G hG G0
  have hResp := hresp δ hδ hδresp R hγ a ha
  let μ : Measure (Euc p.d) := r26t3_mu R 0
  let S : SeqL2 →L[ℝ] Window p := fp81s21_initGauss_synthesis p
  let ell : Euc p.d → SeqL2 := fp81s21_initial_ellv R (r26t3_qwin R a)
  let K : TensorDual SeqL2 3 := s21eKappa0 μ ell
  let ν : Measure (Window p) := windowFuture future a ha 0
  let H : Window p → ℝ := initialHeat future a ha Φ 0
  let F : SeqL2 → ℝ := fun z => H (S z)
  let κ : TensorDual (Window p) 3 := initialKappa R a
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν, windowFuture]
    exact (Measure.isProbabilityMeasure_map_iff
      (HRS.MS.ProClosureS111.physicalWindowRestriction
        (d := p.d) (m := wholeSpaceIndex p.d) (T := p.T)
        (H := a + p.T) ha le_rfl).continuous.aemeasurable).2
      (hf.1 (a + p.T) 0)
  have hEllMeas : AEStronglyMeasurable ell μ := by
    rcases hγ with hγpos | hγzero
    · have hs := r26t3_static_tensor hδ hδHalf R hγpos
        (r26t3_qwin R a) hq
      have heq : r26t3_ell R (r26t3_qwin R a) = ell := by rfl
      rw [← heq]
      exact hs.1.aestronglyMeasurable
    · have hr := fp81s21_respIid_vector_regular hδ hδHalf R hγzero a ha hq
      simpa [ell, μ] using hr.1.aestronglyMeasurable
  have hEllCube : Integrable (fun x => ‖ell x‖ * ‖ell x‖ * ‖ell x‖) μ := by
    rcases hγ with hγpos | hγzero
    · have hs := r26t3_static_tensor hδ hδHalf R hγpos
        (r26t3_qwin R a) hq
      have heq : r26t3_ell R (r26t3_qwin R a) = ell := by rfl
      have hc : Integrable (fun x => ‖r26t3_ell R (r26t3_qwin R a) x‖ ^ 3) μ :=
        hs.2.2.1
      have hc2 : Integrable (fun x => ‖r26t3_ell R (r26t3_qwin R a) x‖ *
          ‖r26t3_ell R (r26t3_qwin R a) x‖ *
          ‖r26t3_ell R (r26t3_qwin R a) x‖) μ := by
        simpa [pow_succ, mul_assoc] using hc
      rw [← heq]
      exact hc2
    · have hr := fp81s21_respIid_vector_regular hδ hδHalf R hγzero a ha hq
      simpa [ell, μ, pow_succ, mul_assoc] using hr.2
  have hKmem : K ∈ projTensor SeqL2 3 :=
    s21e_kappa0_mem μ hEllMeas hEllCube
  have hHeat := r26t3_heat_bounds (P := ν) (Γ := id)
    (hΓ := aestronglyMeasurable_id) Φ hΦ
  have hHeatEq : r26t3_heat ν id Φ = H := by
    funext y
    rfl
  have hH : H ∈ CbUnitBall (Window p) 5 := hHeatEq ▸ hHeat.1
  have hpush := r26t3_push_static S G ⟨K, hKmem⟩ H hH
  obtain ⟨A, hApos, hAbound, hFnorm, hpush⟩ := hpush
  have hD3int : ∀ y : Window p,
      Integrable (fun w => iteratedFDeriv ℝ 3 Φ (y + w)) ν := by
    intro y
    apply Integrable.of_bound (C := 1)
    · exact (hΦ.1.continuous_iteratedFDeriv (by norm_num)).comp
        (continuous_const.add continuous_id) |>.aestronglyMeasurable
    · filter_upwards with w
      have hb := HRS.MC.E213U6.u6_norm_iteratedFDeriv_le (j := 3) hΦ (by norm_num)
        (y + w)
      simpa using hb
  have hHeatD3 : ∀ y : Window p,
      iteratedFDeriv ℝ 3 H y =
        ∫ w, iteratedFDeriv ℝ 3 Φ (y + w) ∂ν := by
    intro y
    rw [← hHeatEq]
    exact hHeat.2 3 (by norm_num) y
  have hpoint : ∀ y : Window p,
      κ (iteratedFDeriv ℝ 3 H y) =
        ∫ w, κ (iteratedFDeriv ℝ 3 Φ (y + w)) ∂ν := by
    intro y
    rw [hHeatD3 y]
    exact (ContinuousLinearMap.integral_comp_comm κ (hD3int y)).symm
  have hpushPoint : ∀ z : SeqL2,
      K (iteratedFDeriv ℝ 3 F z) = κ (iteratedFDeriv ℝ 3 H (S z)) := by
    intro z
    calc
      K (iteratedFDeriv ℝ 3 F z) =
          (HRS.MC.E213O.tensorPow' 3 S (K : TensorDual SeqL2 3))
            (iteratedFDeriv ℝ 3 H (S z)) := (hpush z).symm
      _ = κ (iteratedFDeriv ℝ 3 H (S z)) := by
        simpa [S, K, κ, fp81s21_initGauss_synthesis] using
          congrArg (fun T : TensorDual (Window p) 3 =>
            T (iteratedFDeriv ℝ 3 H (S z))) hResp
  have hinner : ∀ z : SeqL2,
      ∫ x, iteratedFDeriv ℝ 3 F z ![ell x, ell x, ell x] ∂μ =
        K (iteratedFDeriv ℝ 3 F z) := by
    intro z
    exact (s21e_kappa0_apply μ hEllMeas hEllCube
      (iteratedFDeriv ℝ 3 F z)).symm
  let ψ : Window p → ℝ := fun y => κ (iteratedFDeriv ℝ 3 Φ y)
  have hψcont : Continuous ψ := by
    exact κ.continuous.comp (hΦ.1.continuous_iteratedFDeriv (by norm_num))
  have hψbound : ∀ y, ‖ψ y‖ ≤ ‖κ‖ := by
    intro y
    dsimp [ψ]
    calc
      ‖κ (iteratedFDeriv ℝ 3 Φ y)‖ ≤
          ‖κ‖ * ‖iteratedFDeriv ℝ 3 Φ y‖ := κ.le_opNorm _
      _ ≤ ‖κ‖ * 1 := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg κ)
        exact HRS.MC.E213U6.u6_norm_iteratedFDeriv_le (j := 3) hΦ (by norm_num) y
      _ = ‖κ‖ := mul_one _
  have hsourceInt : Integrable
      (fun yw : SeqL2 × Window p => ψ (S yw.1 + yw.2)) (G.prod ν) := by
    apply Integrable.of_bound (C := ‖κ‖)
    · exact (hψcont.comp ((S.continuous.comp continuous_fst).add continuous_snd)).aestronglyMeasurable
    · filter_upwards with yw
      exact hψbound _
  let GS : Measure (Window p) := Measure.map S G
  haveI : IsProbabilityMeasure GS := by
    dsimp [GS]
    exact (Measure.isProbabilityMeasure_map_iff S.continuous.aemeasurable).2 inferInstance
  have htargetInt : Integrable
      (fun yw : Window p × Window p => ψ (yw.1 + yw.2)) (GS.prod ν) := by
    apply Integrable.of_bound (C := ‖κ‖)
    · exact (hψcont.comp (continuous_fst.add continuous_snd)).aestronglyMeasurable
    · filter_upwards with yw
      exact hψbound _
  have hmapProd : GS.prod ν =
      Measure.map (Prod.map S id) (G.prod ν) := by
    simpa [GS] using
      (Measure.map_prod_map G ν (f := S) (g := id) S.continuous.measurable measurable_id)
  have hproduct :
      (∫ yw : SeqL2 × Window p, ψ (S yw.1 + yw.2) ∂(G.prod ν)) =
      ∫ yw : Window p × Window p, ψ (yw.1 + yw.2) ∂(GS.prod ν) := by
    rw [hmapProd]
    exact (integral_map
      (S.continuous.measurable.prodMap measurable_id).aemeasurable
      ((hψcont.comp (continuous_fst.add continuous_snd)).aestronglyMeasurable)).symm
  have hproductIter :
      (∫ z, ∫ w, ψ (S z + w) ∂ν ∂G) =
      ∫ yw : Window p × Window p, ψ (yw.1 + yw.2) ∂(GS.prod ν) := by
    calc
      (∫ z, ∫ w, ψ (S z + w) ∂ν ∂G) =
          ∫ yw : SeqL2 × Window p, ψ (S yw.1 + yw.2) ∂(G.prod ν) :=
            (integral_prod _ hsourceInt).symm
      _ = ∫ yw : Window p × Window p, ψ (yw.1 + yw.2) ∂(GS.prod ν) := hproduct
  have haddMeas : Measurable (fun yw : Window p × Window p => yw.1 + yw.2) :=
    (continuous_fst.add continuous_snd).measurable
  have hsumLaw := hLaw
  have hsumIntegral :
      (∫ yw : Window p × Window p, ψ (yw.1 + yw.2) ∂(GS.prod ν)) =
      ∫ z, ψ z ∂law G0.P (r26t3_Zpath G0 a) := by
    calc
      (∫ yw : Window p × Window p, ψ (yw.1 + yw.2) ∂(GS.prod ν)) =
          ∫ z, ψ z ∂Measure.map (fun yw : Window p × Window p => yw.1 + yw.2)
            (GS.prod ν) := (integral_map haddMeas.aemeasurable
              hψcont.aestronglyMeasurable).symm
      _ = ∫ z, ψ z ∂law G0.P (r26t3_Zpath G0 a) := by rw [hsumLaw]
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
  have hpathIntegral :
      (∫ z, ψ z ∂law G0.P (r26t3_Zpath G0 a)) =
        ∫ w, ψ (r26t3_Zpath G0 a w) ∂G0.P := by
    rw [HRS.law]
    exact integral_map hpathMeas hψcont.aestronglyMeasurable
  calc
    ∫ z, ∫ x,
        iteratedFDeriv ℝ 3 F z ![ell x, ell x, ell x] ∂μ ∂G =
      ∫ z, K (iteratedFDeriv ℝ 3 F z) ∂G := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hinner
    _ = ∫ z, κ (iteratedFDeriv ℝ 3 H (S z)) ∂G := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpushPoint
    _ = ∫ z, ∫ w, ψ (S z + w) ∂ν ∂G := by
        apply integral_congr_ae
        filter_upwards with z
        simpa [ψ] using hpoint (S z)
    _ = ∫ yw : Window p × Window p, ψ (yw.1 + yw.2) ∂(GS.prod ν) := hproductIter
    _ = ∫ z, ψ z ∂law G0.P (r26t3_Zpath G0 a) := hsumIntegral
    _ = ∫ w, initialKappa R a
          (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath G0 a w)) ∂G0.P := by
        rw [hpathIntegral]

#print axioms fp81s21_initial_heat_cubic_transport

end HRS.Fp81.S21

end
