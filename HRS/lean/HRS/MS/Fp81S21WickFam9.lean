import HRS.MS.Fp81S21WickFam8

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS (Euc)
open HRS.Whole HRS.MS.R26T3

/-- Fourth moments of a supplied oscillator increment are controlled by its
second moment, uniformly over the two nonnegative times. -/
theorem fp81s21_wickFam_increment_L4_bound
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (G : GaussianRealization R) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (φ : Euc p.d → ℝ) (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ) :
    let D : G.Ω → ℝ := fun ω =>
      OscDual.eval (G.Z t ω) φ - OscDual.eval (G.Z s ω) φ
    MemLp D 4 G.P ∧ eLpNorm D 4 G.P ≤
      HRS.Contr.gK ^ (1 / 4 : ℝ) * eLpNorm D 2 G.P := by
  dsimp only
  have hm (u : ℝ) : Measurable (fun ω => OscDual.eval (G.Z u ω) φ) := by
    have h := (HRS.MS.ProClosureS111.gaussianOscEval
      (⟨φ, hφ⟩ : HRS.MS.S111X1.oscSub p.d (wholeSpaceIndex p.d : ℝ))).continuous.measurable.comp
        ((G.evolution (max s t + 1)).meas u)
    simpa only [Function.comp_def, HRS.MS.ProClosureS111.gaussianOscEval_apply] using h
  have hmeas : AEMeasurable (fun ω =>
      OscDual.eval (G.Z t ω) φ - OscDual.eval (G.Z s ω) φ) G.P :=
    ((hm t).sub (hm s)).aemeasurable
  have hg := fp81s21_wickFam_two_time_increment_gaussian p R G s t hs ht φ hφ
  have hLaw : HasGaussianLaw (fun ω =>
      OscDual.eval (G.Z t ω) φ - OscDual.eval (G.Z s ω) φ) G.P := ⟨hmeas, hg.1⟩
  exact ⟨hLaw.memLp (by norm_num), HRS.Contr.le_of_pow4_le (HRS.Contr.gauss_N4_le hmeas hg).2⟩

#print axioms fp81s21_wickFam_increment_L4_bound
end HRS.Fp81.S21
end
