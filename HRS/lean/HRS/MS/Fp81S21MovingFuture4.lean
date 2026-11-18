import HRS.MS.Fp81S21MovingFuture3

/-!
# S2.1(iii), SOL39 packet 3: actual Gaussian future laws

For every admissible trajectory, positive horizon, and cutoff in that
horizon, select the continuous-path marginal proved in the preceding files.
The family consists only of marginal laws indexed by `(H,u)`; it does not
claim a common adapted field as the cutoff varies. Outside the valid domain
the family is defined using a Dirac measure.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory ProbabilityTheory
open Set
open scoped ENNReal NNReal

namespace HRS.Fp81.S21

open HRS.Whole
open HRS.MS.R26T3

theorem fp81s21_movingFuture_exists (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ future : (H : ℝ) → ℝ →
            Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H),
          (∀ H u, IsProbabilityMeasure (future H u)) ∧
          (∀ H : ℝ, 0 < H → ∀ u ∈ Icc (0 : ℝ) H,
            IsR2FutureGaussian (r26t3_coeff R)
              (wholeSpaceIndex p.d : ℝ) H u (future H u)) := by
  obtain ⟨δ0, hδ0, hδ0half, hpaths⟩ :=
    fp81s21_movingFuture_pathLaw p
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  have hvalid : ∀ H : ℝ, 0 < H → ∀ u : ℝ, u ∈ Icc (0 : ℝ) H →
      ∃ γ : Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H),
        IsProbabilityMeasure γ ∧
          IsR2FutureGaussian (r26t3_coeff R)
            (wholeSpaceIndex p.d : ℝ) H u γ := by
    intro H hH u hu
    obtain ⟨γ, hγ, hLaw⟩ := hpaths δ hδ hδle R H hH u hu
    exact ⟨γ, hγ,
      fp81s21_movingFuture_pathLaw_isR2 p R hδ
        (le_trans hδle hδ0half) hH hu γ hγ hLaw⟩
  let future : (H : ℝ) → ℝ →
      Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) :=
    fun H u => if hH : 0 < H then
      if hu : u ∈ Icc (0 : ℝ) H then Classical.choose (hvalid H hH u hu)
      else Measure.dirac 0
    else Measure.dirac 0
  refine ⟨future, ?_, ?_⟩
  · intro H u
    dsimp [future]
    by_cases hH : 0 < H
    · rw [dif_pos hH]
      by_cases hu : u ∈ Icc (0 : ℝ) H
      · rw [dif_pos hu]
        exact (Classical.choose_spec (hvalid H hH u hu)).1
      · rw [dif_neg hu]
        infer_instance
    · rw [dif_neg hH]
      infer_instance
  · intro H hH u hu
    dsimp [future]
    rw [dif_pos hH, dif_pos hu]
    exact (Classical.choose_spec (hvalid H hH u hu)).2

#print axioms fp81s21_movingFuture_exists

end HRS.Fp81.S21

end
