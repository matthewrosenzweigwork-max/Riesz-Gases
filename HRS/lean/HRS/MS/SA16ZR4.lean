import HRS.MS.SA16ZR3

/-!
# S.A.16 (SA16Z) R4: the remainder of the Leibniz expansion is bounded by the lower jets
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section R4
variable {d : ℕ} {s : ℝ}

/-- `‖D^k μ‖ ≤ Λ` for `k ≤ N` -/
def sa16z_Cb (N : ℕ) (Λ : ℝ) (μ : Euc d → ℝ) : Prop := ∀ k ≤ N, ∀ y, ‖iteratedFDeriv ℝ k μ y‖ ≤ Λ

lemma sa16z_Cb_mono {N M : ℕ} (h : N ≤ M) {Λ : ℝ} {μ : Euc d → ℝ} (hμ : sa16z_Cb M Λ μ) : sa16z_Cb N Λ μ :=
  fun k hk => hμ k (hk.trans h)

lemma sa16z_Cb_dm {N : ℕ} {Λ : ℝ} {μ : Euc d → ℝ} (hμs : ContDiff ℝ ∞ μ) (hμ : sa16z_Cb (N + 1) Λ μ) (l : Fin d) :
    sa16z_Cb N Λ (sa16z_dm μ l) := fun k hk y => by
  have h := sa16so_norm_iter_dir hμs (sa16z_e l) k y
  rw [show ‖sa16z_e l‖ = 1 by simp [sa16z_e], one_mul] at h
  exact h.trans (hμ (k + 1) (by omega) y)

lemma sa16z_Cb_abs {Λ : ℝ} {a : Euc d → ℝ} (ha : sa16z_Cb 0 Λ a) (y : Euc d) : |a y| ≤ Λ := by
  have := ha 0 le_rfl y
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this

lemma sa16z_Cb_fderiv {Λ : ℝ} {a : Euc d → ℝ} (ha : sa16z_Cb 1 Λ a) (y : Euc d) : ‖fderiv ℝ a y‖ ≤ Λ := by
  have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := a) (x := y) (n := 0)
  rw [norm_iteratedFDeriv_zero] at h
  rw [h]
  exact ha 1 le_rfl y

/-- the first-order Leibniz terms in `L^p` -/
theorem sa16z_C1_bound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {μ φ : Euc d → ℝ}, ContDiff ℝ ∞ μ → IsCcInfty φ → ∀ {Λ : ℝ}, 0 ≤ Λ →
      sa16z_Cb 2 Λ μ → ∀ (n : ℕ) (idx : Fin (n + 1) → Fin d),
      eLpNorm (fun x => sa16z_C1 s μ φ (n + 1) idx x) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * Λ * ((n : ℝ) + 1)) * sa16z_S p φ (n + 2) := by
  obtain ⟨C2, hC2, hB⟩ := sa16z_P_jet_bound hd hs0 hsd hθ1 hp
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    have : (1 : ℝ) ≤ p := hp.le
    simpa using ENNReal.ofReal_le_ofReal this
  refine ⟨C2 * 2 * ((d : ℝ) * (1 + d)), by positivity, fun {μ φ} hμ hφ {Λ} hΛ hCb n idx => ?_⟩
  have hfun : (fun x => sa16z_C1 s μ φ (n + 1) idx x) = ∑ q : Fin (n + 1),
      sa16z_P s (sa16z_dm μ (idx q)) (partialDeriv (Fin.removeNth q idx) φ) := by
    funext x; simp [sa16z_C1, Finset.sum_apply]
  have hq : ∀ q : Fin (n + 1), eLpNorm (sa16z_P s (sa16z_dm μ (idx q)) (partialDeriv (Fin.removeNth q idx) φ))
      (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (C2 * (Λ + Λ) * ((d : ℝ) * (1 + d))) * sa16z_S p φ (n + 2) := by
    intro q
    have hcb := sa16z_Cb_dm hμ hCb (idx q)
    exact hB (sa16z_dm_smooth hμ _) hφ hΛ hΛ (sa16z_Cb_abs (sa16z_Cb_mono (by omega) hcb))
      (sa16z_Cb_fderiv (sa16z_Cb_mono (by omega) hcb)) (Fin.removeNth q idx)
  rw [hfun]
  refine (eLpNorm_sum_le hp1).trans ((Finset.sum_le_sum fun q _ => hq q).trans ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : ((n + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (C2 * (Λ + Λ) * ((d : ℝ) * (1 + d))) * sa16z_S p φ (n + 2)) =
      ENNReal.ofReal (C2 * 2 * ((d : ℝ) * (1 + d)) * Λ * ((n : ℝ) + 1)) * sa16z_S p φ (n + 2) := by
    rw [← mul_assoc]
    congr 1
    rw [show ((n + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((n : ℝ) + 1) by
      rw [← ENNReal.ofReal_natCast]; push_cast; rfl, ← ENNReal.ofReal_mul (by positivity)]
    congr 1; ring
  exact this.le

end R4

end HRS.Whole.AppendixA.Phase2SA16R
