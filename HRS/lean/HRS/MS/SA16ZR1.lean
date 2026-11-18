import HRS.MS.SA16ZB2

/-!
# S.A.16 (SA16Z) R1: Leibniz expansion of `∂^idx (P_μ φ)` (exact recursion)

`sa16z_C1 s μ φ j idx x = ∑_q P_{∂_{idx q} μ}(∂^{idx∖q} φ)`; `sa16z_Rem` is the remainder
`∂^idx P_μ φ - P_μ ∂^idx φ - C1`.  `sa16z_Rem_cons`:
`Rem_{j+1}(l::idx)(μ,φ) = C1_j idx (∂_lμ, φ) + Rem_j idx (∂_lμ, φ) + Rem_j idx (μ, ∂_lφ)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section R1
variable {d : ℕ} {s : ℝ}

/-- `∂_l f` -/
def sa16z_dm (f : Euc d → ℝ) (l : Fin d) : Euc d → ℝ := fun y => fderiv ℝ f y (sa16z_e l)

/-- the first-order Leibniz terms `∑_q P_{∂_{idx q} μ}(∂^{idx∖q} φ)` -/
def sa16z_C1 (s : ℝ) (μ φ : Euc d → ℝ) : (j : ℕ) → (Fin j → Fin d) → Euc d → ℝ
  | 0, _, _ => 0
  | (n + 1), idx, x =>
      ∑ q : Fin (n + 1), sa16z_P s (sa16z_dm μ (idx q)) (partialDeriv (Fin.removeNth q idx) φ) x

/-- the remainder -/
def sa16z_Rem (s : ℝ) (μ φ : Euc d → ℝ) (j : ℕ) (idx : Fin j → Fin d) (x : Euc d) : ℝ :=
  partialDeriv idx (sa16z_P s μ φ) x - sa16z_P s μ (partialDeriv idx φ) x - sa16z_C1 s μ φ j idx x

lemma sa16z_dm_smooth {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (l : Fin d) : ContDiff ℝ ∞ (sa16z_dm f l) :=
  sa16so_dir_smooth hf _

lemma sa16z_dm_cc {f : Euc d → ℝ} (hf : IsCcInfty f) (l : Fin d) : IsCcInfty (sa16z_dm f l) :=
  sa16s_cc_fderiv hf _

lemma sa16z_pd_cons_eq {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) {j : ℕ} (l : Fin d) (idx : Fin j → Fin d) :
    partialDeriv (Fin.cons l idx : Fin (j + 1) → Fin d) φ = partialDeriv idx (sa16z_dm φ l) := by
  funext x
  rw [sa16s_pd_cons hφ l idx x]
  exact (congrFun (sa16sy_pd_comm hφ l idx) x).symm

lemma sa16z_C1_succ (hs0 : 0 ≤ s) (hsd : s < d) {μ φ : Euc d → ℝ} {j : ℕ} (l : Fin d) (idx : Fin j → Fin d)
    (hφ : ContDiff ℝ ∞ φ) (x : Euc d) :
    sa16z_C1 s μ φ (j + 1) (Fin.cons l idx) x =
      sa16z_P s (sa16z_dm μ l) (partialDeriv idx φ) x + sa16z_C1 s μ (sa16z_dm φ l) j idx x := by
  cases j with
  | zero =>
    simp [sa16z_C1, Fin.sum_univ_succ, Fin.removeNth_zero]
  | succ n =>
    simp only [sa16z_C1]
    rw [Fin.sum_univ_succ]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    have h1 : Fin.removeNth q.succ (Fin.cons l idx : Fin (n + 2) → Fin d) = Fin.cons l (Fin.removeNth q idx) :=
      Fin.cons_comp_succ_succAbove l idx q
    rw [Fin.cons_succ, h1, sa16z_pd_cons_eq hφ]

lemma sa16z_Rem_cons (hs0 : 0 ≤ s) (hsd : s < d) {μ φ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ) (hφ : IsCcInfty φ)
    {j : ℕ} (l : Fin d) (idx : Fin j → Fin d) (x : Euc d) :
    sa16z_Rem s μ φ (j + 1) (Fin.cons l idx) x =
      sa16z_C1 s (sa16z_dm μ l) φ j idx x + sa16z_Rem s (sa16z_dm μ l) φ j idx x +
        sa16z_Rem s μ (sa16z_dm φ l) j idx x := by
  have hPs : ContDiff ℝ ∞ (sa16z_P s μ φ) := sa16z_P_smooth hs0 hsd hμ hφ
  have h1 : partialDeriv (Fin.cons l idx : Fin (j + 1) → Fin d) (sa16z_P s μ φ) x =
      partialDeriv idx (fun y => sa16z_P s (sa16z_dm μ l) φ y + sa16z_P s μ (sa16z_dm φ l) y) x := by
    rw [sa16s_pd_cons hPs l idx x]
    have := congrFun (sa16sy_pd_comm hPs l idx) x
    rw [← this]
    congr 1
    funext y
    exact sa16z_P_deriv hs0 hsd hμ hφ l y
  have hA : ContDiff ℝ ∞ (sa16z_P s (sa16z_dm μ l) φ) := sa16z_P_smooth hs0 hsd (sa16z_dm_smooth hμ l) hφ
  have hB : ContDiff ℝ ∞ (sa16z_P s μ (sa16z_dm φ l)) := sa16z_P_smooth hs0 hsd hμ (sa16z_dm_cc hφ l)
  have h2 : partialDeriv (Fin.cons l idx : Fin (j + 1) → Fin d) φ = partialDeriv idx (sa16z_dm φ l) :=
    sa16z_pd_cons_eq hφ.1 l idx
  unfold sa16z_Rem
  rw [h1, sa16sy_pd_add hA hB, h2, sa16z_C1_succ hs0 hsd l idx hφ.1 x]
  ring

end R1

end HRS.Whole.AppendixA.Phase2SA16R
