import HRS.MS.R26T8AP15n
import HRS.MS.R26T8AP11g6
import HRS.MS.R26T8ARow6
import HRS.MS.R26T8AP11b0

/-!
# S8.2 T8A P15o: row averages of a conormal pair function against the thermal measure
For `G` conormal of order `σ < d`: `x ↦ ∫ G(x,y) dμ(y)` and `y ↦ ∫ G(x,y) dμ(x)` are `C^k` with jets `≤ C A jb^M`, and the rows are integrable.
Constants depend only on the (unique) thermal density, hence are uniform after the usual reduction.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_p15_rho_weight (hd : 2 ≤ d) (k : ℕ) (M : ℝ) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d (criticalS d) a β ρ) :
    ∃ K : ℝ, 0 ≤ K ∧ ContDiff ℝ (k : WithTop ℕ∞) ρ ∧
      ∀ i ≤ k, ∀ y : Euc d, ‖iteratedFDeriv ℝ i ρ y‖ ≤ K * (1 + ‖y‖) ^ (-(M + (d : ℝ) + 1)) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < criticalS d := by unfold criticalS; linarith
  have hsd : criticalS d < d := by unfold criticalS; linarith
  obtain ⟨hρs, hg⟩ := HRS.MS.Mov0.mv0_hgauss hd hs0.le hsd ha hβ hρ
  obtain ⟨Cρ, cρ, hCρ, hcρ, hb⟩ := r26t8a_f23_rho_unif hg k
  obtain ⟨Kp, hKp0, hKp⟩ := r26t8a_f25_rho_poly hCρ hcρ hb (M + (d : ℝ) + 1)
  exact ⟨Kp, hKp0, hρs.of_le (by exact_mod_cast le_top), hKp⟩

theorem r26t8a_p15_rowx (hd : 2 ≤ d) (k b : ℕ) (a beta M sigma : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    (hsd : sigma < d) {rho : Euc d → ℝ} (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : Euc d → Euc d → ℝ) (A : ℝ), 0 ≤ A → Conormal k b M sigma A G →
      (∀ x, Integrable (fun y => rho y * G x y)) ∧
      ContDiff ℝ (k : WithTop ℕ∞) (fun x => ∫ y, G x y ∂(HRS.Whole.withDensityReal rho)) ∧
      ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (fun x => ∫ y, G x y ∂(HRS.Whole.withDensityReal rho)) x‖ ≤
        C * A * jbracket x ^ M := by
  obtain ⟨K, hK0, hρk, hK⟩ := r26t8a_p15_rho_weight hd k M ha hbeta hrho
  obtain ⟨C, hC0, hC⟩ := r26t8a_row_lemma hd k b M sigma hM hsd K hK0
  have hprob : HRS.Whole.IsProbDensity rho := hrho.1.1
  refine ⟨C, hC0, fun G A hA hG => ?_⟩
  obtain ⟨hs, hj⟩ := hC rho hρk hK G A hA hG
  have e : (fun x => ∫ y, G x y ∂(HRS.Whole.withDensityReal rho)) = fun x => ∫ y, rho y * G x y := by
    funext x; exact r26t8a_f25_wd_integral hprob (G x)
  rw [e]
  exact ⟨fun x => r26t8a_row_integrable hd k b hM sigma hsd K hK0 hρk hK hA hG x, hs, hj⟩

theorem r26t8a_p15_rowy {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (hd : 2 ≤ d) (k b : ℕ) (a beta M sigma : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hsd : sigma < d) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : Euc d → Euc d → ℝ) (A : ℝ), 0 ≤ A → Conormal k b M sigma A G →
      (∀ y, Integrable (fun x => rho x * G x y)) ∧
      ContDiff ℝ (k : WithTop ℕ∞) (fun y => ∫ x, G x y ∂(HRS.Whole.withDensityReal rho)) ∧
      ∀ j ≤ k, ∀ y, ‖iteratedFDeriv ℝ j (fun y => ∫ x, G x y ∂(HRS.Whole.withDensityReal rho)) y‖ ≤
        C * A * jbracket y ^ M := by
  obtain ⟨C, hC0, hC⟩ := r26t8a_p15_rowx hd k b a beta M sigma ha hbeta hM hsd hrho
  refine ⟨C, hC0, fun G A hA hG => ?_⟩
  exact hC (fun x y => G y x) A hA (r26t8a_f24_conormal_swap hchi hG)

end HRS.MS.R26T8A
