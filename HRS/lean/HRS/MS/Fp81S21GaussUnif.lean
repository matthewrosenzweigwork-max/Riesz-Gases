import HRS.MS.Fp81S21GaussIncrFull5
import HRS.MS.Fp81S21RawGauss

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.R26T3 HRS.MS.S111X2 HRS.MS.ProClosureS111

/-- A supplied Gaussian realization has the same one-time coordinate second
moments as the combined feature. -/
private theorem fp81s21_gauss_unif_eval_second
    (p : Parameters) {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (R : Trajectory p δ) [IsProbabilityMeasure (r26t3_mu R 0)]
    {Mg : ℝ} {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ]
      Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg)
    (G : GaussianRealization R) (t : ℝ) (ht : 0 ≤ t)
    (φ : Euc p.d → ℝ) (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ) :
    Integrable (fun ω => OscDual.eval (G.Z t ω) φ ^ 2) G.P ∧
      (∫ ω, OscDual.eval (G.Z t ω) φ ^ 2 ∂G.P) =
        ‖fp81s21_combinedFeature p R hK t φ‖ ^ 2 := by
  let T : ℝ := t + 1
  let times : Fin 2 → ℝ := fun _ => t
  let X : G.Ω → ℝ := fun ω => OscDual.eval (G.Z t ω) φ
  let V : G.Ω → EuclideanSpace ℝ (Fin 2) := fun ω =>
    WithLp.toLp 2 fun i => OscDual.eval (G.Z (times i) ω) φ
  let S : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j =>
    HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ
      (times i) (times j) φ φ
  let μ : Measure (EuclideanSpace ℝ (Fin 2)) := multivariateGaussian 0 S
  have hT : 0 < T := by dsimp [T]; linarith
  have htimes : ∀ i : Fin 2, times i ∈ Icc (0 : ℝ) T := by
    intro i
    simp only [times]
    exact ⟨ht, by dsimp [T]; linarith⟩
  have hφs : ∀ i : Fin 2, IsOscTest (wholeSpaceIndex p.d : ℝ) φ := fun _ => hφ
  have hZU := G.evolution T
  have hLaw : G.P.map V = μ := by
    simpa [V, μ, S, times, HRS.MS.S21E.s21eCov,
      HRS.Whole.linearGaussianCov, r26t3_coeff, r26t3_mu] using
        hZU.gaussian 2 times (fun _ => φ) htimes hφs
  have hgram : ∀ i j : Fin 2,
      inner ℝ (fp81s21_combinedFeature p R hK (times i) φ)
        (fp81s21_combinedFeature p R hK (times j) φ) = S i j := by
    intro i j
    simpa [S, times] using fp81s21_combinedFeature_gram p hδ hδhalf R hK
      ht ht hφ hφ
  let F : Fin 2 → Fp81S21GaussFeatureHilbert p R := fun i =>
    fp81s21_combinedFeature p R hK (times i) φ
  have hSgram : S = Matrix.gram ℝ F := by
    ext i j
    simpa [S, F, Matrix.gram] using (hgram i j).symm
  have hS : S.PosSemidef := by
    rw [hSgram]
    exact Matrix.posSemidef_gram ℝ F
  have hXmeas : Measurable X := by
    have heq : X = gaussianOscEval
        (⟨φ, hφ⟩ : HRS.MS.S111X1.oscSub p.d (wholeSpaceIndex p.d : ℝ)) ∘ G.Z t := by
      funext ω
      exact (gaussianOscEval_apply
        (⟨φ, hφ⟩ : HRS.MS.S111X1.oscSub p.d (wholeSpaceIndex p.d : ℝ))
        (G.Z t ω)).symm
    rw [heq]
    exact (gaussianOscEval
      (⟨φ, hφ⟩ : HRS.MS.S111X1.oscSub p.d (wholeSpaceIndex p.d : ℝ))).continuous.measurable.comp
        (hZU.meas t)
  have hVmeas : Measurable V := by
    apply (WithLp.measurable_toLp 2 (Fin 2 → ℝ)).comp
    exact measurable_pi_iff.2 fun i => by
      simpa [V, X, times] using hXmeas
  have hcoordμ : MemLp
      (fun z : EuclideanSpace ℝ (Fin 2) => z 0) 2 μ :=
    HRS.MS.R26T3.s21k2_p07_coord_memLp μ 0
  have hcoordAes : AEStronglyMeasurable
      (fun z : EuclideanSpace ℝ (Fin 2) => z 0) (G.P.map V) := by
    exact Measurable.aestronglyMeasurable
      ((EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous.measurable)
  have hcoordMap : MemLp
      (fun z : EuclideanSpace ℝ (Fin 2) => z 0) 2 (G.P.map V) := by
    rw [hLaw]
    exact hcoordμ
  have hXmem : MemLp X 2 G.P := by
    have h := (memLp_map_measure_iff hcoordAes hVmeas.aemeasurable).1 hcoordMap
    have heq : (fun ω => (V ω).ofLp 0) = X := by
      funext ω
      simp [V, X, times]
    change MemLp (fun ω => (V ω).ofLp 0) 2 G.P at h
    rw [← heq]
    exact h
  have hXint : Integrable (fun ω => X ω * X ω) G.P := hXmem.integrable_mul hXmem
  have hmix : ∫ z : EuclideanSpace ℝ (Fin 2), z 0 * z 0 ∂μ = S 0 0 :=
    HRS.MS.S111X2.s111x2_gauss_mixed S hS 0 0
  have hMapMoment :
      (∫ z : EuclideanSpace ℝ (Fin 2), z 0 * z 0 ∂μ) =
        ∫ ω, X ω * X ω ∂G.P := by
    rw [← hLaw]
    exact integral_map hVmeas.aemeasurable
      (show AEStronglyMeasurable
        (fun z : EuclideanSpace ℝ (Fin 2) => z 0 * z 0) (G.P.map V) from
          (by fun_prop : Continuous
            (fun z : EuclideanSpace ℝ (Fin 2) => z 0 * z 0)).aestronglyMeasurable)
  have hsecond : (∫ ω, X ω ^ 2 ∂G.P) =
      ‖fp81s21_combinedFeature p R hK t φ‖ ^ 2 := by
    calc
      _ = S 0 0 := by
        rw [show (fun ω => X ω ^ 2) = (fun ω => X ω * X ω) by funext ω; ring]
        rw [← hMapMoment, hmix]
      _ = ‖fp81s21_combinedFeature p R hK t φ‖ ^ 2 := by
        rw [← hgram 0 0]
        simp [times, real_inner_self_eq_norm_sq]
  refine ⟨?_, hsecond⟩
  simpa [X, pow_two] using hXint

/-- Uniform one-time coordinate trace for every supplied Gaussian realization.
The trace constant is fixed before the time and the realization. -/
theorem fp81s21_gauss_unif_trace (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ V : ℝ, 0 ≤ V ∧
          ∀ t : ℝ, 0 ≤ t → ∀ G : GaussianRealization R,
            Summable (fun α : MultiIndex p.d =>
              ∫ ω, (OscDual.coord (G.Z t ω) α) ^ 2 ∂G.P) ∧
            (∑' α : MultiIndex p.d,
              ∫ ω, (OscDual.coord (G.Z t ω) α) ^ 2 ∂G.P) ≤ V := by
  obtain ⟨δT, hδT, hδThalf, hTrace⟩ := fp81s21_combinedFeature_trace p
  refine ⟨δT, hδT, hδThalf, ?_⟩
  intro δ hδ hδle R
  letI : IsProbabilityMeasure (r26t3_mu R 0) :=
    fp81s21_initialMeasure_isProbability p R
  obtain ⟨Mg, K, hK, V, hV, hTraceR⟩ := hTrace δ hδ hδle R
  refine ⟨V, hV, ?_⟩
  intro t ht G
  have hsecond : ∀ α : MultiIndex p.d,
      (∫ ω, (OscDual.coord (G.Z t ω) α) ^ 2 ∂G.P) =
        ‖fp81s21_combinedFeature p R hK t
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α)‖ ^ 2 := by
    intro α
    have hφ : IsOscTest (wholeSpaceIndex p.d : ℝ)
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α) :=
      HRS.MS.GenPath.s56_isOscTest _ α
    have h := fp81s21_gauss_unif_eval_second p hδ (hδle.trans hδThalf)
      R hK G t ht (oscTestFun (wholeSpaceIndex p.d : ℝ) α) hφ
    have heval : ∀ ω,
        OscDual.coord (G.Z t ω) α =
          OscDual.eval (G.Z t ω) (oscTestFun (wholeSpaceIndex p.d : ℝ) α) :=
      fun ω => (OscDual.eval_oscTestFun (G.Z t ω) α).symm
    have hcoordSecond :
        (∫ ω, (OscDual.coord (G.Z t ω) α) ^ 2 ∂G.P) =
          ∫ ω, (OscDual.eval (G.Z t ω)
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) ^ 2 ∂G.P := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω =>
        congrArg (fun x : ℝ => x ^ 2) (heval ω)
    calc
      _ = ∫ ω, (OscDual.eval (G.Z t ω)
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) ^ 2 ∂G.P := hcoordSecond
      _ = _ := h.2
  have hsum : Summable (fun α : MultiIndex p.d =>
      ∫ ω, (OscDual.coord (G.Z t ω) α) ^ 2 ∂G.P) := by
    apply (hTraceR t ht).1.congr
    intro α
    rw [hsecond α]
  refine ⟨hsum, ?_⟩
  calc
    _ = ∑' α : MultiIndex p.d,
        ‖fp81s21_combinedFeature p R hK t
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α)‖ ^ 2 := by
      exact tsum_congr hsecond
    _ ≤ V := (hTraceR t ht).2

#print axioms fp81s21_gauss_unif_eval_second
#print axioms fp81s21_gauss_unif_trace

end HRS.Fp81.S21

end
