import HRS.MS.Fp81S21WickFam7
import HRS.MS.S21G2_S12F

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Set
namespace HRS.Fp81.S21
open HRS (Euc)
open HRS.Whole HRS.MS.R26T3

/-- Any two-time increment of a supplied oscillator observation has a
centered Gaussian law. -/
theorem fp81s21_wickFam_two_time_increment_gaussian
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (G : GaussianRealization R) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (φ : Euc p.d → ℝ) (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ) :
    HRS.IsCenteredGaussian (G.P.map fun ω =>
      OscDual.eval (G.Z t ω) φ - OscDual.eval (G.Z s ω) φ) := by
  let H : ℝ := max s t + 1
  let times : Fin 2 → ℝ := fun i => if i = 0 then t else s
  let V : G.Ω → EuclideanSpace ℝ (Fin 2) := fun ω =>
    WithLp.toLp 2 (fun i => OscDual.eval (G.Z (times i) ω) φ)
  let S : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j =>
    linearGaussianCov (r26t3_coeff R) p.β⁻¹
      (HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ)
      (times i) (times j) φ φ
  have htimes : ∀ i : Fin 2, times i ∈ Icc (0 : ℝ) H := by
    intro i
    fin_cases i
    · simp only [times, if_true, mem_Icc]; exact ⟨ht, by dsimp [H]; linarith [le_max_right s t]⟩
    · simp only [times, Fin.isValue, OfNat.ofNat_ne_zero, if_false, mem_Icc]
      exact ⟨hs, by dsimp [H]; linarith [le_max_left s t]⟩
  have hVlaw : G.P.map V = multivariateGaussian 0 S := by
    simpa [V, S, linearGaussianCov] using
      (G.evolution H).gaussian 2 times (fun _ => φ) htimes (fun _ => hφ)
  have hVm : Measurable V := by
    apply (WithLp.measurable_toLp 2 (Fin 2 → ℝ)).comp
    apply measurable_pi_iff.2
    intro i
    have heval : Measurable (fun ω => OscDual.eval (G.Z (times i) ω) φ) := by
      have heq : (fun ω => OscDual.eval (G.Z (times i) ω) φ) =
          fun ω => HRS.MS.ProClosureS111.gaussianOscEval
            (⟨φ, hφ⟩ : HRS.MS.S111X1.oscSub p.d (wholeSpaceIndex p.d : ℝ))
            (G.Z (times i) ω) := by
        funext ω
        exact (HRS.MS.ProClosureS111.gaussianOscEval_apply ⟨φ, hφ⟩ _).symm
      rw [heq]
      exact (HRS.MS.ProClosureS111.gaussianOscEval ⟨φ, hφ⟩).continuous.measurable.comp
        ((G.evolution H).meas (times i))
    exact heval
  let ell : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
    EuclideanSpace.proj 0 - EuclideanSpace.proj 1
  have hc : HRS.IsCenteredGaussian (G.P.map V) := by
    rw [hVlaw]
    exact HRS.MS.S111BD.s111_isCenteredGaussian_mvg 2 S
  have hmap : G.P.map (fun ω => ell (V ω)) = (G.P.map V).map ell := by
    rw [Measure.map_map ell.continuous.measurable hVm]
    rfl
  have hinc : HRS.IsCenteredGaussian (G.P.map fun ω => ell (V ω)) := by
    rw [hmap]
    exact s21g2_s12_cg_map hc ell
  simpa [ell, V, times] using hinc

#print axioms fp81s21_wickFam_two_time_increment_gaussian
end HRS.Fp81.S21
end
