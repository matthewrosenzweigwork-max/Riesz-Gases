import HRS.MS.R26T8AP06

/-!
# S8.2 local Newton layer, packet T8A.P19: unique `C^8` diagonal extension of the final remainder
Corollary of P06 with `k = 8`, `b = 0`, `sigma = -d/2-12` (`Conormal 10` implies `Conormal 9`; `8 < d/2 + 12`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_conormal_mono {d : ℕ} {k k' b : ℕ} {M sigma A : ℝ} {F : Euc d → Euc d → ℝ} (h : k ≤ k')
    (hF : Conormal k' b M sigma A F) : Conormal k b M sigma A F :=
  ⟨hF.1.of_le (by exact_mod_cast h), fun p q hpq X z hz => hF.2 p q (by omega) X z hz⟩

theorem r26t8a_parametrix_extension {d : ℕ} (hd : 2≤d) (M : ℝ) (hM : 0≤M) :
    ∃ C : ℝ, 0≤C ∧ ∀ A : ℝ, 0≤A → ∀ R : Euc d → Euc d → ℝ,
      Conormal 10 0 M (-(d:ℝ)/2-12) A R →
      ∃ Rext : Euc d → Euc d → ℝ, ContDiff ℝ 8 (Function.uncurry Rext) ∧
        (∀ x y, x≠y → Rext x y=R x y) ∧
        (∀ j≤8, ∀ x y, ‖iteratedFDeriv ℝ j (Function.uncurry Rext) (x,y)‖≤C*A*HRS.MS.Phase2S82.pairWeight M x y) ∧
        (∀ G : Euc d → Euc d → ℝ, Continuous (Function.uncurry G) →
          (∀ x y, x≠y → G x y=R x y) → G=Rext) := by

  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hsig : (-(d : ℝ) / 2 - 12) < 0 := by linarith
  have hk : ((8 : ℕ) : ℝ) < -(-(d : ℝ) / 2 - 12) := by push_cast; linarith
  obtain ⟨C, hC0, hC⟩ := r26t8a_negative_conormal_extension hd 8 0 M (-(d : ℝ) / 2 - 12) hM hsig hk
  refine ⟨C, hC0, fun A hA R hR => ?_⟩
  obtain ⟨Rext, h1, h2, h3, h4⟩ := hC A hA R (r26t8a_conormal_mono (k := 8 + 1) (by norm_num) hR)
  exact ⟨Rext, by exact_mod_cast h2, h1, h4, h3⟩

end HRS.MS.R26T8A
