import HRS.MS.Fp81S21IidIndexed
import HRS.MS.Fp81S21IidIndexed2
import HRS.MS.Fp81S21IidGaussUniq
import HRS.MS.Fp81S21InitGaussIid
import HRS.MS.Fp81S21RespIid
import HRS.MS.Fp81S21QwinUniform

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45
open HRS.Whole
open HRS (Euc cbNorm)
open HRS.MS.R26T3

theorem fp81s21_iid_gaussian_endpoint (p : Parameters) (hγ : p.γ = 0) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
          ∀ N : ℕ, N0 ≤ N → 2 ≤ N →
            ∀ a : ℝ, 0 ≤ a →
              ∀ G : Measure SeqL2, IsProbabilityMeasure G →
                IsCenteredGaussianSeq G (fun i j =>
                  HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
                    (r26t3_qwin R a i) (r26t3_qwin R a j)) →
                ∀ Φ : SeqL2 → ℝ, Φ ∈ CbUnitBall SeqL2 5 →
                  |Real.sqrt N *
                      ((∫ X, Φ (featureVec (r26t3_qwin R a)
                          (r26t3_marg R N) X) ∂(r26t3_Q R N)) -
                        ∫ z, Φ z ∂G) -
                    (1 / 6) * ∫ z, ∫ x,
                      iteratedFDeriv ℝ 3 Φ z
                        ![fp81s21_initial_ellv R (r26t3_qwin R a) x,
                          fp81s21_initial_ellv R (r26t3_qwin R a) x,
                          fp81s21_initial_ellv R (r26t3_qwin R a) x]
                        ∂(r26t3_mu R 0) ∂G| ≤ ε := by
  classical
  obtain ⟨δI, hδI, hδIhalf, hiid⟩ := fp81s21_iid_indexed_qwin p hγ
  obtain ⟨δG, hδG, hδGhalf, hendpoint⟩ := fp81s21_initGaussIid_endpoint p
  obtain ⟨δQ, hδQ, hδQhalf, hquniform⟩ := fp81s21_qwin_uniform p
  let δ0 : ℝ := min δI (min δG δQ)
  have hδ0 : 0 < δ0 := by
    dsimp [δ0]
    positivity
  have hδ0half : δ0 ≤ 1 / 2 := by
    dsimp [δ0]
    exact (min_le_left _ _).trans hδIhalf
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R ε hε
  have hδIle : δ ≤ δI := hδle.trans (by
    dsimp [δ0]
    exact min_le_left _ _)
  have hδGle : δ ≤ δG := hδle.trans (by
    dsimp [δ0]
    exact (min_le_right _ _).trans (min_le_left _ _))
  have hδQle : δ ≤ δQ := hδle.trans (by
    dsimp [δ0]
    exact (min_le_right _ _).trans (min_le_right _ _))
  have hδhalf : δ ≤ 1 / 2 := hδle.trans hδ0half
  obtain ⟨_, _, hqfamily⟩ := hquniform δ hδ hδQle R
  let ι := {a : ℝ // 0 ≤ a}
  have hchoose : ∀ a : ι, ∃ G : Measure SeqL2,
      IsProbabilityMeasure G ∧
        IsCenteredGaussianSeq G (fun i j =>
          HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
            (r26t3_qwin R a.1 i) (r26t3_qwin R a.1 j)) := by
    intro a
    obtain ⟨G, hGp, hGseq, _⟩ := hendpoint δ hδ hδGle R hγ a.1 a.2
    exact ⟨G, hGp, hGseq⟩
  let G0 : ι → Measure SeqL2 := fun a => Classical.choose (hchoose a)
  have hG0spec (a : ι) : IsProbabilityMeasure (G0 a) ∧
      IsCenteredGaussianSeq (G0 a) (fun i j =>
        HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
          (r26t3_qwin R a.1 i) (r26t3_qwin R a.1 j)) := by
    simpa [G0] using Classical.choose_spec (hchoose a)
  have hG0prob : ∀ a : ι, IsProbabilityMeasure (G0 a) :=
    fun a => (hG0spec a).1
  have hG0seq : ∀ a : ι, IsCenteredGaussianSeq (G0 a) (fun i j =>
      HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
        (r26t3_qwin R a.1 i) (r26t3_qwin R a.1 j)) :=
    fun a => (hG0spec a).2
  have hG0gauss : ∀ a : ι, IsCenteredGaussian (G0 a) :=
    fun a => (hG0seq a).1
  have hcovRef : ∀ (a : ι) (x y : SeqL2),
      covarianceBilin (G0 a) x y = covarianceBilin
        ((r26t3_mu R 0).map
          (s21h2_Y (r26t3_qwin R a.1) (r26t3_mu R 0))) x y := by
    intro a x y
    letI : IsProbabilityMeasure (G0 a) := hG0prob a
    exact fp81s21_iid_gaussian_covariance_match hδ hδhalf R hγ a.1 a.2
      (hqfamily a.1 a.2).1 (hG0seq a) x y
  have hIndexed := hiid δ hδ hδIle R G0 hG0prob hG0gauss hcovRef
  obtain ⟨N0, hN0⟩ := hIndexed ε hε
  refine ⟨N0, ?_⟩
  intro N hN0le hN2 a ha G hGprob hGseq Φ hΦ
  let aidx : ι := ⟨a, ha⟩
  letI : IsProbabilityMeasure G := hGprob
  letI : IsProbabilityMeasure (G0 aidx) := hG0prob aidx
  have hsame : G = G0 aidx :=
    fp81s21_initial_iid_gaussian_ext hGseq (hG0seq aidx)
  have hqa : IsSummableFeatureFamily (r26t3_J p.d) (r26t3_qwin R a) :=
    (hqfamily a ha).1
  have hresp (x : Euc p.d) :
      fp81s21_initial_ellv R (r26t3_qwin R a) x =
        s21h2_Y (r26t3_qwin R a) (r26t3_mu R 0) x :=
    fp81s21_respIid_vector_eq_centered hδ hδhalf R hγ a ha x hqa
  have hthird :
      (∫ z, ∫ x, iteratedFDeriv ℝ 3 Φ z
        ![fp81s21_initial_ellv R (r26t3_qwin R a) x,
          fp81s21_initial_ellv R (r26t3_qwin R a) x,
          fp81s21_initial_ellv R (r26t3_qwin R a) x]
        ∂(r26t3_mu R 0) ∂(G0 aidx)) =
      (∫ z, ∫ x, iteratedFDeriv ℝ 3 Φ z
        ![s21h2_Y (r26t3_qwin R a) (r26t3_mu R 0) x,
          s21h2_Y (r26t3_qwin R a) (r26t3_mu R 0) x,
          s21h2_Y (r26t3_qwin R a) (r26t3_mu R 0) x]
        ∂(r26t3_mu R 0) ∂(G0 aidx)) := by
    apply integral_congr_ae
    filter_upwards [] with z
    apply integral_congr_ae
    filter_upwards [] with x
    simp [hresp x]
  have hbase := hN0 N hN0le hN2 aidx Φ hΦ
  have hrewrite :
      (Real.sqrt N *
        ((∫ X, Φ (featureVec (r26t3_qwin R a)
            (r26t3_marg R N) X) ∂(r26t3_Q R N)) - ∫ z, Φ z ∂G) -
        (1 / 6) * ∫ z, ∫ x, iteratedFDeriv ℝ 3 Φ z
          ![fp81s21_initial_ellv R (r26t3_qwin R a) x,
            fp81s21_initial_ellv R (r26t3_qwin R a) x,
            fp81s21_initial_ellv R (r26t3_qwin R a) x]
          ∂(r26t3_mu R 0) ∂G) =
      (Real.sqrt N *
        ((∫ X, Φ (featureVec (r26t3_qwin R aidx.1)
            (r26t3_marg R N) X) ∂(r26t3_Q R N)) - ∫ z, Φ z ∂(G0 aidx)) -
        (1 / 6) * ∫ z, ∫ x, iteratedFDeriv ℝ 3 Φ z
          ![s21h2_Y (r26t3_qwin R aidx.1) (r26t3_mu R 0) x,
            s21h2_Y (r26t3_qwin R aidx.1) (r26t3_mu R 0) x,
            s21h2_Y (r26t3_qwin R aidx.1) (r26t3_mu R 0) x]
          ∂(r26t3_mu R 0) ∂(G0 aidx)) := by
    rw [hsame, hthird]
  rw [hrewrite]
  exact hbase

#print axioms fp81s21_iid_gaussian_endpoint

end HRS.Fp81.S21

end
