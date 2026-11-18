import HRS.Main.A8PAux18

/-!
# Packet A8P, part 19: identification of the surrogate covariance with the integrated `Σ̄`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

theorem a8p_surrogateCov_eq (D : DynData d) (ρ : ℝ → Torus d → ℝ) (qq T : ℝ) {q : ℕ}
    (ts : Fin q → ℝ) (φ : Fin q → Torus d → ℝ) (hts : ∀ a, ts a ≤ T)
    (ρ' : ℝ → Torus d → ℝ) (hρ' : ∀ r ∈ Set.Icc (0 : ℝ) T, ρ' r = ρ r) :
    surrogateCov D ρ qq ts φ =
      integratedCov T (a8pSigBar ts (a8pG ts (fun a r => propagator D ρ r (ts a) (φ a))) ρ' (2 * qq)) := by
  ext a b
  unfold surrogateCov integratedCov a8pSigBar
  simp only [Matrix.of_apply]
  set F : ℝ → ℝ := fun r => ∫ x, inner ℝ (Torus.grad (propagator D ρ r (ts a) (φ a)) x)
    (Torus.grad (propagator D ρ r (ts b) (φ b)) x) * ρ r x with hF
  have hint : ∀ r, (if 0 ≤ r ∧ r < min (ts a) (ts b) then
      2 * qq * ∫ x, inner ℝ (a8pG ts (fun a r => propagator D ρ r (ts a) (φ a)) a r x)
        (a8pG ts (fun a r => propagator D ρ r (ts a) (φ a)) b r x) * ρ' r x else 0) =
      Set.indicator (Set.Ico 0 (min (ts a) (ts b))) (fun r => 2 * qq * F r) r ∨
      ¬ (r ∈ Set.Icc (0 : ℝ) T) := by
    intro r
    by_cases hr : r ∈ Set.Icc (0 : ℝ) T
    · left
      by_cases h : 0 ≤ r ∧ r < min (ts a) (ts b)
      · have hm : r ∈ Set.Ico 0 (min (ts a) (ts b)) := ⟨h.1, h.2⟩
        rw [if_pos h, Set.indicator_of_mem hm]
        have h1 : r ∈ Set.Icc 0 (ts a) := ⟨h.1, (lt_min_iff.1 h.2).1.le⟩
        have h2 : r ∈ Set.Icc 0 (ts b) := ⟨h.1, (lt_min_iff.1 h.2).2.le⟩
        simp only [a8pG, if_pos h1, if_pos h2, hρ' r hr, hF]
      · have hm : r ∉ Set.Ico 0 (min (ts a) (ts b)) := fun hm => h ⟨hm.1, hm.2⟩
        rw [if_neg h, Set.indicator_of_notMem hm]
    · right; exact hr
  have hcongr : ∫ r in Set.Icc (0 : ℝ) T, (if 0 ≤ r ∧ r < min (ts a) (ts b) then
      2 * qq * ∫ x, inner ℝ (a8pG ts (fun a r => propagator D ρ r (ts a) (φ a)) a r x)
        (a8pG ts (fun a r => propagator D ρ r (ts a) (φ a)) b r x) * ρ' r x else 0) =
      ∫ r in Set.Icc (0 : ℝ) T, Set.indicator (Set.Ico 0 (min (ts a) (ts b))) (fun r => 2 * qq * F r) r := by
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    rcases hint r with h | h
    · exact h
    · exact absurd hr h
  rw [hcongr, integral_indicator measurableSet_Ico]
  have hsub : Set.Ico (0 : ℝ) (min (ts a) (ts b)) ∩ Set.Icc 0 T = Set.Ico 0 (min (ts a) (ts b)) := by
    ext r
    simp only [Set.mem_inter_iff, Set.mem_Ico, Set.mem_Icc]
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h, h.1, h.2.le.trans ((min_le_left _ _).trans (hts a))⟩
  rw [Measure.restrict_restrict measurableSet_Ico, hsub, integral_const_mul, integral_Icc_eq_integral_Ico]

end HRS.Main.A8P
