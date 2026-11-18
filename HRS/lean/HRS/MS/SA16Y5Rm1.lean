import HRS.MS.SA16Y5Dc1

/-!
# S.A.16 (SA16Y5) Rm1: the Leibniz remainder of `∂^idx P_μ φ` in the order-one range

`sa16y5_P_jet`: for `a` with `Dec 1 W a`: `‖P_a (∂^κ φ)‖_p ≤ K d S_{r+1}(φ)` (`r = |κ|`; one derivative of `φ` beyond `∂^κ`,
in place of the two of `sa16z_P_jet_bound`).
`sa16y5_C1_bound`: `‖C1_{n+1}‖_p ≤ C (n+1) S_{n+1}(φ)` under `Dec 2 W μ`.
`sa16y5_Rem_bound`: `‖Rem_j‖_p ≤ K S_j(φ)` under `Dec (j+1) W μ` (the exact recursion `sa16z_Rem_cons` is reused).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Rm1
variable {d : ℕ} {s : ℝ}

theorem sa16y5_P_jet (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) {p : ℝ} (hp : 2 ≤ p)
    (hfar : (d : ℝ) < p * (s + 1)) {W : ℝ} (hW : 0 ≤ W) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {a φ : Euc d → ℝ}, ContDiff ℝ ∞ a → sa16y5_Dec 1 W a → IsCcInfty φ →
      ∀ {r : ℕ} (κ : Fin r → Fin d),
      eLpNorm (sa16z_P s a (partialDeriv κ φ)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (K * (d : ℝ)) * sa16z_S p φ (r + 1) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ p)
  obtain ⟨K, hK0, hK⟩ := sa16y5_D0 hd hs0 hs1 hp hfar hW
  refine ⟨K, hK0, fun {a φ} ha hdec hφ {r} κ => ?_⟩
  have hψ : IsCcInfty (partialDeriv κ φ) := sa16s_cc_partialDeriv hφ κ
  have hfun : sa16z_P s a (partialDeriv κ φ) = ∑ i : Fin d, (fun x => fderiv ℝ (convFun (rieszKernel d s)
      (fun y => a y * sa16z_dm (partialDeriv κ φ) i y)) x (sa16z_e i)) := by
    funext x
    simp only [sa16z_P, Finset.sum_apply]
    rfl
  have hi : ∀ i : Fin d, eLpNorm (fun x => fderiv ℝ (convFun (rieszKernel d s)
      (fun y => a y * sa16z_dm (partialDeriv κ φ) i y)) x (sa16z_e i)) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal K * sa16z_S p φ (r + 1) := by
    intro i
    refine (hK ha hdec (sa16z_dm_cc hψ i) i).trans (mul_le_mul' le_rfl ?_)
    refine le_trans ?_ (sa16z_JJ_le_S φ (k := r + 1) (N := r + 1) le_rfl)
    unfold sa16z_JJ
    refine eLpNorm_mono ((sa16z_dm_cc hψ i).1.continuous.aestronglyMeasurable) fun y => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sa16sz_vn_nonneg _ _ _)]
    exact sa16z_pd_dm_abs hφ.1 κ i y
  rw [hfun]
  refine (eLpNorm_sum_le hp1).trans ((Finset.sum_le_sum fun i _ => hi i).trans (le_of_eq ?_))
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ENNReal.ofReal_mul hK0,
    ENNReal.ofReal_natCast]
  ring

theorem sa16y5_C1_bound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) {p : ℝ} (hp : 2 ≤ p)
    (hfar : (d : ℝ) < p * (s + 1)) {W : ℝ} (hW : 0 ≤ W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {μ φ : Euc d → ℝ}, ContDiff ℝ ∞ μ → IsCcInfty φ → sa16y5_Dec 2 W μ →
      ∀ (n : ℕ) (idx : Fin (n + 1) → Fin d),
      eLpNorm (fun x => sa16z_C1 s μ φ (n + 1) idx x) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * ((n : ℝ) + 1)) * sa16z_S p φ (n + 1) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ p)
  obtain ⟨K, hK0, hK⟩ := sa16y5_P_jet hd hs0 hs1 hp hfar hW
  refine ⟨K * d, mul_nonneg hK0 (Nat.cast_nonneg d), fun {μ φ} hμ hφ hdec n idx => ?_⟩
  have hfun : (fun x => sa16z_C1 s μ φ (n + 1) idx x) = ∑ q : Fin (n + 1),
      sa16z_P s (sa16z_dm μ (idx q)) (partialDeriv (Fin.removeNth q idx) φ) := by
    funext x; simp [sa16z_C1, Finset.sum_apply]
  have hq : ∀ q : Fin (n + 1), eLpNorm (sa16z_P s (sa16z_dm μ (idx q)) (partialDeriv (Fin.removeNth q idx) φ))
      (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (K * (d : ℝ)) * sa16z_S p φ (n + 1) := fun q =>
    hK (sa16z_dm_smooth hμ _) (sa16y5_Dec_dm hμ hdec (idx q)) hφ (Fin.removeNth q idx)
  rw [hfun]
  refine (eLpNorm_sum_le hp1).trans ((Finset.sum_le_sum fun q _ => hq q).trans (le_of_eq ?_))
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
  congr 1
  rw [show ((n + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((n : ℝ) + 1) by
    rw [← ENNReal.ofReal_natCast]; push_cast; rfl, ← ENNReal.ofReal_mul (by positivity)]
  congr 1; ring

theorem sa16y5_Rem_bound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hs1 : s < (d : ℝ) - 1) {p : ℝ} (hp : 2 ≤ p)
    (hfar : (d : ℝ) < p * (s + 1)) {W : ℝ} (hW : 0 ≤ W) :
    ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ j : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ {μ φ : Euc d → ℝ}, ContDiff ℝ ∞ μ → IsCcInfty φ →
      sa16y5_Dec (j + 1) W μ → ∀ (idx : Fin j → Fin d),
      eLpNorm (fun x => sa16z_Rem s μ φ j idx x) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal K * sa16z_S p φ j := by
  obtain ⟨C1, hC1, hC1b⟩ := sa16y5_C1_bound hd hs0 hs1 hp hfar hW
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ p)
  refine ⟨C1, hC1, fun j => ?_⟩
  induction j with
  | zero =>
    refine ⟨0, le_rfl, fun {μ φ} hμ hφ hdec idx => ?_⟩
    have : (fun x => sa16z_Rem s μ φ 0 idx x) = 0 := by
      funext x
      simp only [sa16z_Rem, sa16j_pd_zero, sa16z_C1, Pi.zero_apply]
      have : partialDeriv idx φ = φ := funext fun y => sa16j_pd_zero idx φ y
      rw [this]; ring
    rw [this, eLpNorm_zero]; exact zero_le
  | succ j ih =>
    obtain ⟨K, hK0, hK⟩ := ih
    refine ⟨2 * K + C1 * j, by positivity, fun {μ φ} hμ hφ hdec idx => ?_⟩
    obtain ⟨l, idx', rfl⟩ : ∃ (l : Fin d) (idx' : Fin j → Fin d), idx = Fin.cons l idx' :=
      ⟨idx 0, Fin.tail idx, (Fin.cons_self_tail idx).symm⟩
    have hfun : (fun x => sa16z_Rem s μ φ (j + 1) (Fin.cons l idx') x) =
        (fun x => sa16z_C1 s (sa16z_dm μ l) φ j idx' x) + (fun x => sa16z_Rem s (sa16z_dm μ l) φ j idx' x) +
          (fun x => sa16z_Rem s μ (sa16z_dm φ l) j idx' x) := by
      funext x
      simp only [Pi.add_apply]
      exact sa16z_Rem_cons hs0 hsd hμ hφ l idx' x
    rw [hfun]
    have hdec' : sa16y5_Dec (j + 1) W (sa16z_dm μ l) := sa16y5_Dec_dm hμ hdec l
    have e2 := hK (sa16z_dm_smooth hμ l) hφ hdec' idx'
    have e3 := hK hμ (sa16z_dm_cc hφ l) (sa16y5_Dec_mono (by omega) hdec) idx'
    have e1 : eLpNorm (fun x => sa16z_C1 s (sa16z_dm μ l) φ j idx' x) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C1 * j) * sa16z_S p φ (j + 1) := by
      cases j with
      | zero =>
        have : (fun x => sa16z_C1 s (sa16z_dm μ l) φ 0 idx' x) = 0 := rfl
        rw [this, eLpNorm_zero]; exact zero_le
      | succ n =>
        have h := hC1b (sa16z_dm_smooth hμ l) hφ (sa16y5_Dec_mono (by omega) hdec') n idx'
        refine h.trans ?_
        push_cast
        exact mul_le_mul' le_rfl (sa16z_S_mono φ (by omega))
    have hS2 : sa16z_S p (sa16z_dm φ l) j ≤ sa16z_S p φ (j + 1) := sa16z_S_dm_le hφ.1 l j
    have hS1 : sa16z_S p φ j ≤ sa16z_S p φ (j + 1) := sa16z_S_mono φ (by omega)
    calc eLpNorm ((fun x => sa16z_C1 s (sa16z_dm μ l) φ j idx' x) + (fun x => sa16z_Rem s (sa16z_dm μ l) φ j idx' x) +
          (fun x => sa16z_Rem s μ (sa16z_dm φ l) j idx' x)) (ENNReal.ofReal p) volume
        ≤ eLpNorm ((fun x => sa16z_C1 s (sa16z_dm μ l) φ j idx' x) + (fun x => sa16z_Rem s (sa16z_dm μ l) φ j idx' x))
            (ENNReal.ofReal p) volume + eLpNorm (fun x => sa16z_Rem s μ (sa16z_dm φ l) j idx' x)
            (ENNReal.ofReal p) volume := eLpNorm_add_le hp1
      _ ≤ (eLpNorm (fun x => sa16z_C1 s (sa16z_dm μ l) φ j idx' x) (ENNReal.ofReal p) volume +
            eLpNorm (fun x => sa16z_Rem s (sa16z_dm μ l) φ j idx' x) (ENNReal.ofReal p) volume) +
            eLpNorm (fun x => sa16z_Rem s μ (sa16z_dm φ l) j idx' x) (ENNReal.ofReal p) volume := by
          gcongr; exact eLpNorm_add_le hp1
      _ ≤ (ENNReal.ofReal (C1 * j) * sa16z_S p φ (j + 1) + ENNReal.ofReal K * sa16z_S p φ (j + 1)) +
            ENNReal.ofReal K * sa16z_S p φ (j + 1) := by
          gcongr
          · exact e2.trans (by gcongr)
          · exact e3.trans (by gcongr)
      _ = ENNReal.ofReal (2 * K + C1 * j) * sa16z_S p φ (j + 1) := by
          rw [← add_mul, ← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 2; ring

end Rm1

end HRS.Whole.AppendixA.Phase2SA16R
