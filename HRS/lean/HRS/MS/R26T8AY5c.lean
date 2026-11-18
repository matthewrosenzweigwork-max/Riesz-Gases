import HRS.MS.R26T8AY5b
import HRS.MS.R26T8AY4
import HRS.MS.R26T8AN0

/-!
# S8.2 T8A Y5c: the same-`k` local Riesz gain for every `σ < d` (same-`k` P11e)
`r26t8a_local_riesz_gain_same`: for `Conormal k b M σ A F` (`-N ≤ σ < d`, `0 < α < d`) the local Riesz integrand is integrable and
`localRiesz α χ F` is `Conormal k (b+1) M (σ-α) (C A)`.  Induction on `N`: `σ ≥ 0` is P11e; for `σ < 0` write `F = Fz + (F - Fz)` (`Fz = chi(4(x-y)) F`);
`F - Fz` vanishes near the diagonal (Y4) and the potential of `Fz` is handled by Y5b with the induction hypothesis at `(k-1, σ+1)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem r26t8a_Y5c_same_k (hd : 2 ≤ d) {α : ℝ} (hα : 0 < α) (hαd : α < d) {chi : Euc d → ℝ}
    (hchi : NewtonCutoff chi) (N : ℕ) : ∀ (k b : ℕ) (M σ : ℝ), 0 ≤ M → -(N : ℝ) ≤ σ → σ < d →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Euc d → Euc d → ℝ) (A : ℝ), 0 ≤ A → Conormal k b M σ A F →
      (∀ x y : Euc d, x ≠ y → Integrable (fun v => ‖x - y - v‖ ^ (α - (d : ℝ)) * chi v * F (y + v) y)) ∧
      Conormal k (b + 1) M (σ - α) (C * A) (r26t8a_localRiesz α chi F) := by
  induction N with
  | zero =>
    intro k b M σ hM hσ hσd
    have hσ0 : 0 ≤ σ := by simpa using hσ
    exact r26t8a_local_riesz_gain_nonneg d hd k b α M σ hα hαd hM hσ0 hσd chi hchi
  | succ N ih =>
    intro k b M σ hM hσ hσd
    by_cases hσ0 : 0 ≤ σ
    · exact r26t8a_local_riesz_gain_nonneg d hd k b α M σ hα hαd hM hσ0 hσd chi hchi
    · push Not at hσ0
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
      obtain ⟨CIH, hCIH0, hIH⟩ := ih (k - 1) b M (σ + 1) hM (by push_cast at hσ; linarith) (by linarith)
      obtain ⟨Cz, hCz0, hZ⟩ := r26t8a_Y5b_zeta hd hα hαd hchi k b M σ hM hσ0
        ⟨CIH, hCIH0, fun F' A' hA' h => (hIH F' A' hA' h).2⟩
      obtain ⟨cz, hcz0, hFz⟩ := r26t8a_Z5a2_conormal hchi k b M σ
      obtain ⟨CS, hCS0, hCS⟩ := r26t8a_Y4_smooth hd k b α M σ hα hαd hM hσd hchi
      obtain ⟨Cw, hCw0, hCw⟩ := r26t8a_local_riesz_gain_nonneg d hd k b α M 0 hα hαd hM le_rfl hd0 chi hchi
      set κ : ℝ := 2 ^ k * (((k : ℝ) + 1) ^ 2 * cz) with hκ
      have hκ0 : 0 ≤ κ := by positivity
      refine ⟨Cz + CS * (1 + κ), by positivity, fun F A hA hF => ?_⟩
      set Fz := r26t8a_Z5a2_Fz chi F with hFzdef
      have hFz' : Conormal k b M σ (cz * A) Fz := hFz F A hA hF
      have hczA : 0 ≤ cz * A := mul_nonneg hcz0 hA
      have hFz0 : Conormal k b M 0 (cz * A) Fz := r26t8a_conormal_mono_sA hczA le_rfl hσ0.le hFz'
      obtain ⟨hintZ, -⟩ := hCw Fz (cz * A) hczA hFz0
      set F1 : Euc d → Euc d → ℝ := fun x y => F x y - Fz x y with hF1
      have hF1c : Conormal k b M σ (A + 2 ^ k * (((k : ℝ) + 1) ^ 2 * (cz * A))) F1 :=
        r26t8a_conormal_sub hchi hA hczA hF hFz'
      have hA1 : 0 ≤ A + 2 ^ k * (((k : ℝ) + 1) ^ 2 * (cz * A)) := by positivity
      have hF1z : ∀ x y : Euc d, ‖x - y‖ ≤ 1 / 4 → F1 x y = 0 := fun x y h => by
        simp only [hF1, hFzdef, r26t8a_Z5a2_one hchi F x y h, sub_self]
      obtain ⟨hint1, hS⟩ := hCS F1 _ hA1 hF1c hF1z
      have hRz := hZ F A hA hF
      have hsum := r26t8a_N0_conormal_add hchi hRz hS
      have hAeq : Cz * A + CS * (A + 2 ^ k * (((k : ℝ) + 1) ^ 2 * (cz * A))) = (Cz + CS * (1 + κ)) * A := by
        rw [hκ]; ring
      rw [hAeq] at hsum
      have hlin : ∀ x y : Euc d, x ≠ y → r26t8a_localRiesz α chi F x y =
          r26t8a_localRiesz α chi Fz x y + r26t8a_localRiesz α chi F1 x y := by
        intro x y hxy
        unfold r26t8a_localRiesz
        rw [← mul_add, ← integral_add (hintZ x y hxy) (hint1 x y hxy)]
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        simp only [hF1]
        ring
      refine ⟨fun x y hxy => ?_, ?_⟩
      · have := (hintZ x y hxy).add (hint1 x y hxy)
        refine this.congr (Filter.Eventually.of_forall fun v => ?_)
        simp only [Pi.add_apply, hF1]
        ring
      · exact r26t8a_N0_conormal_congr (fun x y hxy => (hlin x y hxy).symm) hsum

end HRS.MS.R26T8A
