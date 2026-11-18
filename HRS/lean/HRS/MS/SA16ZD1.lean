import HRS.MS.SA16ZM2

/-!
# S.A.16 (SA16Z) D1: the first-order Leibniz terms as an operator `Q` on tensors

`sa16z_Q j idx l F = ∑_q F (idx q) (l :: idx∖q)` (zero for `j = 0`);
`sa16z_C1_Q`: `C1_j idx = -c_s ∑_l Q j idx l (fun a κ => pvOdd_l (∂_aμ ∂^κφ))`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section D1
variable {d : ℕ} {s : ℝ}

/-- `∑_q F(idx q, l :: idx∖q)` -/
def sa16z_Q : (j : ℕ) → (Fin j → Fin d) → Fin d → (Fin d → (Fin j → Fin d) → ℝ) → ℝ
  | 0, _, _, _ => 0
  | (n + 1), idx, l, F => ∑ q : Fin (n + 1), F (idx q) (Fin.cons l (Fin.removeNth q idx))

lemma sa16z_Q_add (j : ℕ) (idx : Fin j → Fin d) (l : Fin d) (F G : Fin d → (Fin j → Fin d) → ℝ) :
    sa16z_Q j idx l (fun a κ => F a κ + G a κ) = sa16z_Q j idx l F + sa16z_Q j idx l G := by
  cases j with
  | zero => simp [sa16z_Q]
  | succ n => simp only [sa16z_Q, Finset.sum_add_distrib]

lemma sa16z_Q_smul (j : ℕ) (idx : Fin j → Fin d) (l : Fin d) (c : ℝ) (F : Fin d → (Fin j → Fin d) → ℝ) :
    sa16z_Q j idx l (fun a κ => c * F a κ) = c * sa16z_Q j idx l F := by
  cases j with
  | zero => simp [sa16z_Q]
  | succ n => simp only [sa16z_Q, Finset.mul_sum]

lemma sa16z_Q_sum {ι : Type*} (t : Finset ι) (j : ℕ) (idx : Fin j → Fin d) (l : Fin d)
    (F : ι → Fin d → (Fin j → Fin d) → ℝ) :
    sa16z_Q j idx l (fun a κ => ∑ i ∈ t, F i a κ) = ∑ i ∈ t, sa16z_Q j idx l (F i) := by
  cases j with
  | zero => simp [sa16z_Q]
  | succ n => simp only [sa16z_Q]; exact Finset.sum_comm

lemma sa16z_Q_congr (j : ℕ) (idx : Fin j → Fin d) (l : Fin d) {F G : Fin d → (Fin j → Fin d) → ℝ}
    (h : ∀ a κ, F a κ = G a κ) : sa16z_Q j idx l F = sa16z_Q j idx l G := by
  cases j with
  | zero => simp [sa16z_Q]
  | succ n => simp only [sa16z_Q, h]

lemma sa16z_C1_Q (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {μ φ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ)
    (hφ : IsCcInfty φ) (j : ℕ) (idx : Fin j → Fin d) (x : Euc d) :
    sa16z_C1 s μ φ j idx x = -(HRS.CZ.Hls.hlsg_c s) * ∑ l : Fin d, sa16z_Q j idx l
      (fun a κ => pvOdd d (s + 2 - d) (fun u : Euc d => u l) (fun y => sa16z_dm μ a y * partialDeriv κ φ y) x) := by
  cases j with
  | zero => simp [sa16z_C1, sa16z_Q]
  | succ n =>
    simp only [sa16z_C1, sa16z_Q]
    have hq : ∀ q : Fin (n + 1), sa16z_P s (sa16z_dm μ (idx q)) (partialDeriv (Fin.removeNth q idx) φ) x =
        -(HRS.CZ.Hls.hlsg_c s) * ∑ l : Fin d, pvOdd d (s + 2 - d) (fun u : Euc d => u l)
          (fun y => sa16z_dm μ (idx q) y * partialDeriv (Fin.cons l (Fin.removeNth q idx) : Fin (n + 1) → Fin d) φ y) x := by
      intro q
      rw [sa16z_P_pv hd hs0 hsd (sa16z_dm_smooth hμ _) (sa16s_cc_partialDeriv hφ _)]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      congr 2
      funext y
      unfold sa16z_src
      rw [sa16s_pd_cons hφ.1]
    simp_rw [hq]
    rw [← Finset.mul_sum, Finset.sum_comm]

end D1

end HRS.Whole.AppendixA.Phase2SA16R
