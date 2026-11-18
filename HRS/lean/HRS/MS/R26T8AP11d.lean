import HRS.MS.R26T8AP11c

/-!
# S8.2 nonlocal layer, packet T8A.P11d: single annulus, comparable regime `R/4 <= |z| <= 4R`
Corollary of the common near estimate `r26t8a_p11_near` (relative derivatives moved to the source).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_p11d (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (alpha M sigma : ℝ)
    (halpha : 0 < alpha) (had : alpha < d) (hM : 0 ≤ M) (hsigma : 0 ≤ sigma) (hsd : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A →
      Conormal k b M sigma A F → ∀ R : ℝ, 0 < R → R ≤ 1 → ∀ X z, z ≠ 0 → R / 4 ≤ ‖z‖ ∧ ‖z‖ ≤ 4 * R →
      ∀ p q : ℕ, p + q ≤ k →
        ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
          (r26t8a_annularRiesz alpha chi R F Y) z) X‖ ≤
          C * A * jbracket X ^ (2 * M) * (R ^ (alpha - sigma - q)) * (1 + |Real.log R|) ^ b := by
  obtain ⟨C, hC0, hC⟩ := r26t8a_p11_near d hd k b alpha M sigma halpha had hM hsigma chi hchi
  exact ⟨C, hC0, fun F A hA hF R hR hR1 X z _ hz p q hpq =>
    hC F A hA hF R hR hR1 X z hz.2 p q hpq⟩

end HRS.MS.R26T8A
