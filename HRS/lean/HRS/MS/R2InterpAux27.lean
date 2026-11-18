import HRS.MS.R2InterpAux26

/-!
# S10.2 (worker S102), part 27 (packet B1): point derivatives are admissible functionals

`f ↦ ∂_a f(x)` is additive, homogeneous and bounded by `C ⟨x⟩^P ‖f‖_{E_{r,P}}` on the tests of `E_{r,P}` (`d/2 + 1 < r`): the local Sobolev
embedding `s102_embed_Cr` with `α = 1`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MP.RdInit HRS.MS.Who

variable {d : ℕ}

theorem s102_gradient_apply (f : Euc d → ℝ) (x : Euc d) (a : Fin d) :
    gradient f x a = fderiv ℝ f x (EuclideanSpace.single a (1 : ℝ)) :=
  HRS.Whole.AppendixA.q09_gradient_apply f x a

/-- Bound of a point derivative on `E_{r,P}`. -/
theorem s102_eval_bound1 (hd : 1 ≤ d) {P : ℝ} (hP0 : 0 ≤ P) (r : ℕ) (hr : (d : ℝ) / 2 + 1 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : Euc d) (a : Fin d) (f : Euc d → ℝ), ContDiff ℝ r f → weightedSobolevE r P f < ⊤ →
      |gradient f x a| ≤ C * jbracket x ^ P * (weightedSobolevE r P f).toReal := by
  obtain ⟨C, hC, h⟩ := s102_embed_Cr hd hP0 r 1 (by exact_mod_cast hr)
  refine ⟨C, hC, fun x a f hf hE => ?_⟩
  have h1 := h (fun _ => a) x f hf
  have h2 : partialDeriv (fun _ : Fin 1 => a) f x = gradient f x a := by
    rw [s102_gradient_apply]
    simp [partialDeriv, iteratedFDeriv_one_apply]
  rw [h2] at h1
  have hjb : 0 ≤ C * jbracket x ^ P := mul_nonneg hC.le (Real.rpow_nonneg (who_jb_pos x).le P)
  have h3 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE.ne) h1
  rw [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul, ENNReal.toReal_ofReal hjb] at h3
  simpa [mul_assoc] using h3

/-- The point derivative is an admissible functional. -/
theorem s102_Z_gradient (hd : 1 ≤ d) {P : ℝ} (hP0 : 0 ≤ P) (r : ℕ) (hr : (d : ℝ) / 2 + 1 < r)
    (x : Euc d) (a : Fin d) :
    S102Z r P (fun f => gradient f x a) := by
  obtain ⟨C, hC, hb⟩ := s102_eval_bound1 hd hP0 r hr
  have hr1 : 1 ≤ r := by
    have : (1 : ℝ) ≤ r := by
      have := Nat.cast_nonneg (α := ℝ) d
      linarith
    exact_mod_cast this
  have hdiff : ∀ f : Euc d → ℝ, IsR2WeightedTest r P f → DifferentiableAt ℝ f x := fun f hf =>
    (hf.1.differentiable (by exact_mod_cast (by omega : r ≠ 0))) x
  refine ⟨fun f g hf hg => ?_, fun c f hf => ?_, ⟨C * jbracket x ^ P, fun f hf => hb x a f hf.1 hf.2⟩⟩
  · show gradient (f + g) x a = gradient f x a + gradient g x a
    unfold gradient
    rw [fderiv_add (hdiff f hf) (hdiff g hg)]
    simp
  · show gradient (c • f) x a = c * gradient f x a
    unfold gradient
    rw [fderiv_const_smul (hdiff f hf)]
    simp

end HRS.MS.R2Interp

end
