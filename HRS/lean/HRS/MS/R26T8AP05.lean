import HRS.MS.R26T8AP05g

/-!
# S8.2 local Newton layer, packet T8A.P05: comparable annulus
Moves the relative derivatives to the annular source (convolution), bounded by `r26t8a_conv_bound` (parts a-g).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_p05 (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (nu M sigma : ℝ)
    (hnu : 0 < nu) (hM : 0 ≤ M) (hsigma : 0 ≤ sigma) (hsd : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 0 ≤ A → ∀ F : Euc d → Euc d → ℝ,
      Conormal k b M sigma A F → ∀ R : ℝ, 0 < R → R ≤ 1 → ∀ X z,
      z ≠ 0 → R/4 ≤ ‖z‖ ∧ ‖z‖ ≤ 4*R → ∀ p q : ℕ, p+q ≤ k →
        ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
          (r26t8a_annularNewton nu chi R F Y) z) X‖ ≤
          C*A*jbracket X^(2*M) * (R^(2-sigma-q)) *
          (1+|Real.log R|)^b *
          (if d=2 ∧ q=0 then 1+|Real.log R|+|Real.log ‖z‖| else 1) := by
  obtain ⟨C, hC0, hC⟩ := r26t8a_conv_bound hd (k := k) (b := b) hM hsigma hchi nu
  refine ⟨C, hC0, fun A hA F hF R hR hR1 X z hz hRz p q hpq => ?_⟩
  refine (hC A hA F hF R hR hR1 z hRz.2 p q hpq X).trans ?_
  have hif : (if d = 2 ∧ q = 0 then 1 + |Real.log R| else (1 : ℝ)) ≤
      (if d = 2 ∧ q = 0 then 1 + |Real.log R| + |Real.log ‖z‖| else 1) := by
    split_ifs
    · linarith [abs_nonneg (Real.log ‖z‖)]
    · exact le_rfl
  have hjb : 0 ≤ jbracket X ^ (2 * M) := Real.rpow_nonneg (by unfold jbracket; positivity) _
  have hpos : 0 ≤ C * A * jbracket X ^ (2 * M) * R ^ (2 - sigma - (q : ℝ)) * (1 + |Real.log R|) ^ b := by
    positivity
  exact mul_le_mul_of_nonneg_left hif hpos

end HRS.MS.R26T8A
