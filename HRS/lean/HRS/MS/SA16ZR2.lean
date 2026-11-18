import HRS.MS.SA16ZR1

/-!
# S.A.16 (SA16Z) R2: jet `L^p` quantities and the bound of the first-order Leibniz terms
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section R2
variable {d : ℕ} {s : ℝ} {p : ℝ}

/-- `‖|D^kφ|‖_{L^p}` -/
def sa16z_JJ (p : ℝ) (φ : Euc d → ℝ) (k : ℕ) : ℝ≥0∞ :=
  eLpNorm (sa16sz_vn φ k) (ENNReal.ofReal p) volume

/-- `∑_{k ≤ N} ‖|D^kφ|‖_{L^p}` -/
def sa16z_S (p : ℝ) (φ : Euc d → ℝ) (N : ℕ) : ℝ≥0∞ := ∑ k ∈ Finset.range (N + 1), sa16z_JJ p φ k

lemma sa16z_JJ_le_S (φ : Euc d → ℝ) {k N : ℕ} (hk : k ≤ N) : sa16z_JJ p φ k ≤ sa16z_S p φ N :=
  Finset.single_le_sum (f := fun k => sa16z_JJ p φ k) (fun _ _ => zero_le) (Finset.mem_range.2 (by omega))

lemma sa16z_S_mono (φ : Euc d → ℝ) {N M : ℕ} (h : N ≤ M) : sa16z_S p φ N ≤ sa16z_S p φ M :=
  Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))

lemma sa16z_pd_dm_abs {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) {r : ℕ} (κ : Fin r → Fin d) (i : Fin d) (y : Euc d) :
    |sa16z_dm (partialDeriv κ φ) i y| ≤ sa16sz_vn φ (r + 1) y := by
  have : sa16z_dm (partialDeriv κ φ) i y = partialDeriv (Fin.cons i κ : Fin (r + 1) → Fin d) φ y := by
    rw [sa16s_pd_cons hφ i κ y]; rfl
  rw [this]
  exact sa16sz_abs_le_vn φ (r + 1) _ y

lemma sa16z_opNorm_le_sum (L : Euc d →L[ℝ] ℝ) : ‖L‖ ≤ ∑ l : Fin d, |L (sa16z_e l)| := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun l _ => abs_nonneg _) fun v => ?_
  have hv : v = ∑ l : Fin d, v l • sa16z_e l := by
    have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v
    simpa [EuclideanSpace.basisFun_apply, sa16z_e] using this.symm
  conv_lhs => rw [hv]
  rw [map_sum, Real.norm_eq_abs, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [map_smul, smul_eq_mul, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v l) (abs_nonneg _)

lemma sa16z_pd_dm_fderiv {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) {r : ℕ} (κ : Fin r → Fin d) (i : Fin d) (y : Euc d) :
    ‖fderiv ℝ (sa16z_dm (partialDeriv κ φ) i) y‖ ≤ (d : ℝ) * sa16sz_vn φ (r + 2) y := by
  refine (sa16z_opNorm_le_sum _).trans ?_
  have h1 : ∀ l : Fin d, |fderiv ℝ (sa16z_dm (partialDeriv κ φ) i) y (sa16z_e l)| ≤ sa16sz_vn φ (r + 2) y := by
    intro l
    have : sa16z_dm (partialDeriv κ φ) i = partialDeriv (Fin.cons i κ : Fin (r + 1) → Fin d) φ := by
      funext z; rw [sa16s_pd_cons hφ i κ z]; rfl
    rw [this]
    exact sa16z_pd_dm_abs hφ (Fin.cons i κ : Fin (r + 1) → Fin d) l y
  calc ∑ l : Fin d, |fderiv ℝ (sa16z_dm (partialDeriv κ φ) i) y (sa16z_e l)|
      ≤ ∑ l : Fin d, sa16sz_vn φ (r + 2) y := Finset.sum_le_sum fun l _ => h1 l
    _ = _ := by simp

lemma sa16z_vn_dm_le {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) (l : Fin d) (k : ℕ) (x : Euc d) :
    sa16sz_vn (sa16z_dm φ l) k x ≤ sa16sz_vn φ (k + 1) x := by
  unfold sa16sz_vn vnorm
  refine Real.sqrt_le_sqrt ?_
  have h : ∀ idx : Fin k → Fin d, partialDeriv idx (sa16z_dm φ l) x =
      partialDeriv (Fin.cons l idx : Fin (k + 1) → Fin d) φ x := fun idx => by
    rw [sa16z_pd_cons_eq hφ l idx]
  simp_rw [h]
  rw [← Finset.sum_image (f := fun idx' : Fin (k + 1) → Fin d => partialDeriv idx' φ x ^ 2)
    (s := Finset.univ) (g := fun idx : Fin k → Fin d => (Fin.cons l idx : Fin (k + 1) → Fin d))
    (fun a _ b _ hab => (Fin.cons_right_injective (α := fun _ : Fin (k + 1) => Fin d) l) hab)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)

lemma sa16z_JJ_dm_le {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) (l : Fin d) (k : ℕ) :
    sa16z_JJ p (sa16z_dm φ l) k ≤ sa16z_JJ p φ (k + 1) := by
  unfold sa16z_JJ
  refine eLpNorm_mono (sa16sz_vn_cont _ (sa16z_dm_smooth hφ l) k).aestronglyMeasurable fun x => ?_
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sa16sz_vn_nonneg _ _ _),
    abs_of_nonneg (sa16sz_vn_nonneg _ _ _)]
  exact sa16z_vn_dm_le hφ l k x

lemma sa16z_S_dm_le {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) (l : Fin d) (N : ℕ) :
    sa16z_S p (sa16z_dm φ l) N ≤ sa16z_S p φ (N + 1) := by
  unfold sa16z_S
  calc ∑ k ∈ Finset.range (N + 1), sa16z_JJ p (sa16z_dm φ l) k
      ≤ ∑ k ∈ Finset.range (N + 1), sa16z_JJ p φ (k + 1) := Finset.sum_le_sum fun k _ => sa16z_JJ_dm_le hφ l k
    _ ≤ ∑ k ∈ Finset.range (N + 2), sa16z_JJ p φ k := by
        rw [Finset.sum_range_succ' (fun k => sa16z_JJ p φ k) (N + 1)]
        exact le_self_add

end R2

end HRS.Whole.AppendixA.Phase2SA16R
