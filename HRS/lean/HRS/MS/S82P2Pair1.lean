import HRS.MS.S82P2Sum4

/-!
# S8.2 (S82P2): pair-statistic algebra and the inner (pinned) second moment (UNCOMPILED DRAFT)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

lemma s82p2_pairSum_insertNth_gen {d m : ℕ} (F : Euc d → Euc d → ℝ) (i : Fin (m + 1))
    (z : Euc d) (X' : Fin m → Euc d) :
    Phase2S82.pairSum F (i.insertNth z X' : EucConfig d (m + 1)) =
      ∑ j, (F z (X' j) + F (X' j) z) + Phase2S82.pairSum F X' := by
  unfold Phase2S82.pairSum
  rw [Fin.sum_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  rw [s82p2_sum_erase (fun l => F z ((i.insertNth z X' : EucConfig d (m + 1)) l)) i]
  simp only [Fin.insertNth_apply_succAbove]
  have h1 : ∀ j : Fin m, ∑ l ∈ Finset.univ.erase (i.succAbove j),
      F (X' j) ((i.insertNth z X' : EucConfig d (m + 1)) l) =
      F (X' j) z + ∑ l ∈ Finset.univ.erase j, F (X' j) (X' l) := by
    intro j
    rw [s82p2_sum_erase_succAbove
      (fun l => F (X' j) ((i.insertNth z X' : EucConfig d (m + 1)) l)) i j]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  simp only [h1, Finset.sum_add_distrib]
  ring

lemma s82p2_update_insertNth {d m : ℕ} (i : Fin (m + 1)) (x y : Euc d) (X' : Fin m → Euc d) :
    Function.update (i.insertNth x X' : EucConfig d (m + 1)) i y = i.insertNth y X' := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    rw [Function.update_of_ne hj]
    simp

lemma s82p2_pairStat_diff {d m : ℕ} {Q : Euc d → Euc d → ℝ} (hsym : ∀ x y, Q x y = Q y x)
    (i : Fin (m + 1)) (x y : Euc d) (X' : Fin m → Euc d) :
    Phase2S82.pairStatistic (N := m + 1) Q (i.insertNth y X' : EucConfig d (m + 1)) -
        Phase2S82.pairStatistic (N := m + 1) Q (i.insertNth x X' : EucConfig d (m + 1)) =
      2 * ((m + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * ∑ j, (Q y (X' j) - Q x (X' j)) := by
  unfold Phase2S82.pairStatistic
  rw [s82p2_pairSum_insertNth_gen, s82p2_pairSum_insertNth_gen]
  have h2 : ∀ z, ∑ j, (Q z (X' j) + Q (X' j) z) = 2 * ∑ j, Q z (X' j) := fun z => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hsym (X' j) z]; ring
  simp only [h2, Finset.sum_sub_distrib]
  ring

lemma s82p2_cN_sq {n : ℕ} (hn : 0 < n) (S : ℝ) :
    (2 * (n : ℝ) ^ (-(3 / 2 : ℝ)) * S) ^ 2 = 4 / (n : ℝ) ^ 3 * S ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : ((n : ℝ) ^ (-(3 / 2 : ℝ))) ^ 2 = 1 / (n : ℝ) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    have : (-(3 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -((3 : ℕ) : ℝ) := by push_cast; ring
    rw [this, Real.rpow_neg hn0.le, Real.rpow_natCast, one_div]
  calc (2 * (n : ℝ) ^ (-(3 / 2 : ℝ)) * S) ^ 2
      = 4 * ((n : ℝ) ^ (-(3 / 2 : ℝ))) ^ 2 * S ^ 2 := by ring
    _ = 4 / (n : ℝ) ^ 3 * S ^ 2 := by rw [h1]; ring

/-- Inner second moment of the update difference, pinned at `x`, for a fixed new site `y`. -/
lemma s82p2_pair_inner_xy {d : ℕ} {a beta C0 C1 : ℝ} {rho : Euc d → ℝ}
    {q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}
    [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)] (hd : 2 ≤ d)
    (hW : WeakReferenceSetup d a beta rho q h C0) (hbeta : 0 < beta)
    (hP : PinComparison beta rho q h C1) (G c : ℝ) (hG : 0 < G) (hc : 0 < c)
    (hρ : HRS.Whole.IsProbDensity rho) (hρG : HRS.Whole.HasR2GaussianUpper G c rho)
    {m : ℕ} (hm : 1 ≤ m) (x : Euc d) (ψ : Euc d → ℝ) (hψm : Measurable ψ)
    (hψ2 : Integrable (fun z => ψ z ^ 2) (HRS.Whole.withDensityReal rho))
    (hψ0 : ∫ z, ψ z ∂HRS.Whole.withDensityReal rho = 0) :
    ∫⁻ X', ENNReal.ofReal ((2 * ((m + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * ∑ j, ψ (X' j)) ^ 2)
        ∂referenceLaw q h (HRS.Whole.withDensityReal rho) beta (m + 1) m
          (Fin.cons x (fun i : Fin 0 => i.elim0) : Fin (0 + 1) → Euc d) ≤
      ENNReal.ofReal (4 * (C0 ^ 2 * (2 + 2 * (1 + 2 * C1)) + (8 * C1 ^ 2 +
            2 * C1 ^ 2 * (1 + 2 * (1 / (1000 * beta))))) / ((m + 1 : ℕ) : ℝ) ^ 2 *
          ∫ z, ψ z ^ 2 ∂HRS.Whole.withDensityReal rho) := by
  have hmain := (s82p2_centered_sum_sq_simple (n := m) (p := 0 + 1) (N := m + 1) hd hW hbeta hP
    G c hG hc hρ hρG (by omega) (by norm_num) (by omega) (by omega)
    (Fin.cons x (fun i : Fin 0 => i.elim0)) ψ hψm hψ2 hψ0).2
  have hn0 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have e : ∀ X' : Fin m → Euc d, ENNReal.ofReal ((2 * ((m + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) *
      ∑ j, ψ (X' j)) ^ 2) = ENNReal.ofReal (4 / ((m + 1 : ℕ) : ℝ) ^ 3) *
      ENNReal.ofReal ((∑ j, ψ (X' j)) ^ 2) := fun X' => by
    rw [s82p2_cN_sq (by omega), ENNReal.ofReal_mul (by positivity)]
  simp only [e]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (mul_le_mul_of_nonneg_left hmain bot_le).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

end HRS.MS.S82P2
