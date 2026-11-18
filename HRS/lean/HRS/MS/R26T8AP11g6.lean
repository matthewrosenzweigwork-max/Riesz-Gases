import HRS.MS.R26T8AP11g5
import HRS.MS.R26T8AP08h

/-!
# S8.2 T8A P11g (part 6): the weights `ρ (forceMean ρ)_i`
For a thermal `ρ`, `u ↦ ρ u * forceMean ρ u i` is `C^k` with all jets of order `≤ k` bounded by `K (1+‖u‖)^(-N)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_g6_force_unif {F : Euc d → Euc d}
    (hF : ∀ l : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ l F x‖ ≤ C) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ l ≤ k, ∀ x, ‖iteratedFDeriv ℝ l F x‖ ≤ C := by
  induction k with
  | zero =>
    obtain ⟨C, hC0, hC⟩ := hF 0
    exact ⟨C, hC0, fun l hl x => by
      have : l = 0 := by omega
      subst this; exact hC x⟩
  | succ k ih =>
    obtain ⟨C, hC0, hC⟩ := ih
    obtain ⟨C', hC'0, hC'⟩ := hF (k + 1)
    refine ⟨C + C', add_nonneg hC0 hC'0, fun l hl x => ?_⟩
    rcases Nat.lt_or_ge l (k + 1) with h | h
    · linarith [hC l (by omega) x]
    · have : l = k + 1 := by omega
      subst this; linarith [hC'  x]

theorem r26t8a_g6_weight (hd : 2 ≤ d) (k : ℕ) (M : ℝ) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d (criticalS d) a β ρ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i : Fin d, ContDiff ℝ (k : WithTop ℕ∞) (fun u => ρ u * forceMean ρ u i) ∧
      ∀ l ≤ k, ∀ u : Euc d, ‖iteratedFDeriv ℝ l (fun u => ρ u * forceMean ρ u i) u‖ ≤
        K * (1 + ‖u‖) ^ (-(M + (d : ℝ) + 1)) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < criticalS d := by unfold criticalS; linarith
  have hsd : criticalS d < d := by unfold criticalS; linarith
  obtain ⟨hρs, hg⟩ := HRS.MS.Mov0.mv0_hgauss hd hs0.le hsd ha hβ hρ
  obtain ⟨Cρ, cρ, hCρ, hcρ, hb⟩ := r26t8a_f23_rho_unif hg k
  obtain ⟨Kp, hKp0, hKp⟩ := r26t8a_f25_rho_poly hCρ hcρ hb (M + (d : ℝ) + 1)
  obtain ⟨hFs, hFb⟩ := r26t8a_thermal_force d hd a β ha hβ ρ hρ
  obtain ⟨CF, hCF0, hCF⟩ := r26t8a_g6_force_unif (F := forceMean ρ) (fun l => by
    obtain ⟨C, hC0, hC⟩ := hFb l
    exact ⟨C, hC0, fun x => (le_add_of_nonneg_right (norm_nonneg _)).trans (hC x)⟩) k
  refine ⟨2 ^ k * Kp * CF, by positivity, fun i => ?_⟩
  have hρk : ContDiff ℝ (k : WithTop ℕ∞) ρ := hρs.of_le (by exact_mod_cast le_top)
  have hgi : ContDiff ℝ (k : WithTop ℕ∞) (fun u => forceMean ρ u i) :=
    ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff).comp (hFs.of_le (by exact_mod_cast le_top))
  refine ⟨hρk.mul hgi, fun l hl u => ?_⟩
  have hmul := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) hρk hgi u (n := l) (by exact_mod_cast hl)
  refine hmul.trans ?_
  have hgb : ∀ m ≤ k, ‖iteratedFDeriv ℝ m (fun u => forceMean ρ u i) u‖ ≤ CF := by
    intro m hm
    have h1 := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).norm_iteratedFDeriv_comp_left
      (f := forceMean ρ) (x := u) (N := (k : WithTop ℕ∞)) (n := m)
      (hFs.contDiffAt.of_le (by exact_mod_cast le_top)) (by exact_mod_cast hm)
    have h2 : ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
      show ‖v i‖ ≤ 1 * ‖v‖
      rw [one_mul, Real.norm_eq_abs]; exact r26t8a_abs_coord_le v i
    calc ‖iteratedFDeriv ℝ m (fun u => forceMean ρ u i) u‖
        ≤ ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)‖ * ‖iteratedFDeriv ℝ m (forceMean ρ) u‖ := h1
      _ ≤ 1 * CF := mul_le_mul h2 (hCF m hm u) (norm_nonneg _) zero_le_one
      _ = CF := one_mul _
  calc ∑ m ∈ Finset.range (l + 1), (l.choose m : ℝ) * ‖iteratedFDeriv ℝ m ρ u‖ *
        ‖iteratedFDeriv ℝ (l - m) (fun u => forceMean ρ u i) u‖
      ≤ ∑ m ∈ Finset.range (l + 1), (l.choose m : ℝ) * (Kp * (1 + ‖u‖) ^ (-(M + (d : ℝ) + 1))) * CF := by
        refine Finset.sum_le_sum fun m hm' => ?_
        have hm2 : m ≤ l := by have := Finset.mem_range.1 hm'; omega
        refine mul_le_mul (mul_le_mul_of_nonneg_left (hKp m (by omega) u) (Nat.cast_nonneg _))
          (hgb (l - m) (by omega)) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (by
            have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖u‖) (-(M + (d : ℝ) + 1)); positivity))
    _ = 2 ^ l * (Kp * CF) * (1 + ‖u‖) ^ (-(M + (d : ℝ) + 1)) := by
        have hs : ∑ m ∈ Finset.range (l + 1), (l.choose m : ℝ) = 2 ^ l := by
          exact_mod_cast Nat.sum_range_choose l
        calc _ = (∑ m ∈ Finset.range (l + 1), (l.choose m : ℝ)) *
              (Kp * (1 + ‖u‖) ^ (-(M + (d : ℝ) + 1)) * CF) := by
              rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun m _ => by ring
          _ = _ := by rw [hs]; ring
    _ ≤ _ := by
        have h2l : (2 : ℝ) ^ l ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hl
        have hp := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖u‖) (-(M + (d : ℝ) + 1))
        have : 0 ≤ Kp * CF := mul_nonneg hKp0 hCF0
        nlinarith [mul_le_mul_of_nonneg_right h2l (mul_nonneg this hp)]

end HRS.MS.R26T8A
