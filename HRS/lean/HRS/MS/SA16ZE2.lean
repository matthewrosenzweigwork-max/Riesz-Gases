import HRS.MS.SA16ZE1

/-!
# S.A.16 (SA16Z) E2: the coefficient matrix `B^l` of the absorbed terms
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section E2
variable {d : ℕ}

/-- `B^l_{idx,κ} = cA [κ = idx] ĥ_l - cs ∑_q [κ = l::idx∖q] ĥ_{idx q}` -/
def sa16z_Bm (cA cs : ℝ) (μ : Euc d → ℝ) (l : Fin d) (j : ℕ) (x : Euc d) :
    Matrix (Fin j → Fin d) (Fin j → Fin d) ℝ := fun idx κ =>
  cA * (if κ = idx then sa16z_hh μ l x else 0) -
    cs * sa16z_Q j idx l (fun a κ' => if κ' = κ then sa16z_hh μ a x else 0)

lemma sa16z_Bm_apply (cA cs : ℝ) (μ : Euc d → ℝ) (l : Fin d) (j : ℕ) (x : Euc d) (G : (Fin j → Fin d) → ℝ)
    (idx : Fin j → Fin d) :
    ∑ κ, sa16z_Bm cA cs μ l j x idx κ * G κ =
      cA * (sa16z_hh μ l x * G idx) - cs * sa16z_Q j idx l (fun a κ' => sa16z_hh μ a x * G κ') := by
  unfold sa16z_Bm
  simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  congr 1
  · congr 1
    simp [ite_mul]
  · congr 1
    have h1 : (fun a κ' => sa16z_hh μ a x * G κ') = fun a κ' =>
        ∑ κ, G κ * (if κ' = κ then sa16z_hh μ a x else 0) := by
      funext a κ'
      simp [mul_ite, Finset.sum_ite_eq, mul_comm]
    rw [h1, sa16z_Q_sum]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [sa16z_Q_smul]; ring

lemma sa16z_Q_abs_le (j : ℕ) (idx : Fin j → Fin d) (l : Fin d) (F : Fin d → (Fin j → Fin d) → ℝ) {Bf : ℝ}
    (hF : ∀ a κ, |F a κ| ≤ Bf) : |sa16z_Q j idx l F| ≤ j * Bf := by
  cases j with
  | zero => simp [sa16z_Q]
  | succ n =>
    simp only [sa16z_Q]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ q : Fin (n + 1), |F (idx q) (Fin.cons l (Fin.removeNth q idx))| ≤ ∑ q : Fin (n + 1), Bf :=
          Finset.sum_le_sum fun q _ => hF _ _
      _ = ((n + 1 : ℕ) : ℝ) * Bf := by simp

lemma sa16z_Bm_abs {μ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ) (hpos : ∀ x, 0 ≤ μ x) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hCb : sa16z_Cb 2 Λ μ) (cA cs : ℝ) (l : Fin d) (j : ℕ) (x : Euc d) (idx κ : Fin j → Fin d) :
    |sa16z_Bm cA cs μ l j x idx κ| ≤ (|cA| + |cs| * j) * Real.sqrt (2 * Λ) := by
  have hh := fun a => sa16z_hh_abs hμ hpos hΛ hCb a x
  have h0 : 0 ≤ Real.sqrt (2 * Λ) := Real.sqrt_nonneg _
  unfold sa16z_Bm
  refine (abs_sub _ _).trans ?_
  have e1 : |cA * (if κ = idx then sa16z_hh μ l x else 0)| ≤ |cA| * Real.sqrt (2 * Λ) := by
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    split_ifs
    · exact hh l
    · simpa using h0
  have e2 : |cs * sa16z_Q j idx l (fun a κ' => if κ' = κ then sa16z_hh μ a x else 0)| ≤
      |cs| * j * Real.sqrt (2 * Λ) := by
    rw [abs_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine sa16z_Q_abs_le j idx l _ (fun a κ' => ?_)
    split_ifs
    · exact hh a
    · simpa using h0
  calc _ ≤ |cA| * Real.sqrt (2 * Λ) + |cs| * j * Real.sqrt (2 * Λ) := add_le_add e1 e2
    _ = _ := by ring

end E2

end HRS.Whole.AppendixA.Phase2SA16R
