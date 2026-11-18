import HRS.Commutator.Torus.NRSTAux18

/-!
# NRS-T, part 19: the base case in the exceptional (integer `α`) case
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal

namespace HRS.Commutator.TorusNote.NRST

open HRS HRS.Commutator

variable {d : ℕ} {s : ℝ}

lemma norm_ev_dd_le_of_lip (V : Fin d → TPA d) (hVr : ∀ j x, (ev (V j) x).im = 0) {L : ℝ}
    (hL0 : 0 ≤ L) (hLip : IsLipschitzVF L (vOf V)) (a c : Fin d) (x : Torus d) :
    ‖ev (dd a (V c)) x‖ ≤ L := by
  refine norm_ev_dd_le (V c) hL0 (fun x y => ?_) a x
  have h := isLip_scalar V hLip c x y
  have e : ev (V c) x - ev (V c) y = (((ev (V c) x).re - (ev (V c) y).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hVr c x, hVr c y]
  rw [e, Complex.norm_real, Real.norm_eq_abs]
  exact h

/-- The base case `α' = 0`. -/
lemma base_exceptional (V : Fin d → TPA d) (hVr : ∀ j x, (ev (V j) x).im = 0) {L : ℝ}
    (hL0 : 0 ≤ L) (hLip : IsLipschitzVF L (vOf V)) (h : TPA d) :
    ‖Jf V (2 * (0 : ℝ)) h‖ ≤ ((d : ℝ) / 2) * L * hom 0 h := by
  have := base_zero V hL0 (fun c x => norm_ev_dd_le_of_lip V hVr hL0 hLip c c x) h
  rw [mul_zero]
  calc ‖Jf V 0 h‖ ≤ ((d : ℝ) * L / 2) * hom 0 h := this
    _ = ((d : ℝ) / 2) * L * hom 0 h := by ring

end HRS.Commutator.TorusNote.NRST
