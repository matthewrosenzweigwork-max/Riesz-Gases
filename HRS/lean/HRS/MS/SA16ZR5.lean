import HRS.MS.SA16ZR4

/-!
# S.A.16 (SA16Z) R5: `‖Rem_j‖_p ≤ K Λ ∑_{k ≤ j} ‖|D^kφ|‖_p`
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section R5
variable {d : ℕ} {s : ℝ}

theorem sa16z_Rem_bound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) {p : ℝ} (hp : 1 < p) :
    ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ j : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ {μ φ : Euc d → ℝ}, ContDiff ℝ ∞ μ → IsCcInfty φ →
      ∀ {Λ : ℝ}, 0 ≤ Λ → sa16z_Cb (j + 2) Λ μ → ∀ (idx : Fin j → Fin d),
      eLpNorm (fun x => sa16z_Rem s μ φ j idx x) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (K * Λ) * sa16z_S p φ j := by
  obtain ⟨C1, hC1, hC1b⟩ := sa16z_C1_bound hd hs0 hsd hθ1 hp
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    have : (1 : ℝ) ≤ p := hp.le
    simpa using ENNReal.ofReal_le_ofReal this
  refine ⟨C1, hC1, fun j => ?_⟩
  induction j with
  | zero =>
    refine ⟨0, le_rfl, fun {μ φ} hμ hφ {Λ} hΛ hCb idx => ?_⟩
    have : (fun x => sa16z_Rem s μ φ 0 idx x) = 0 := by
      funext x
      simp only [sa16z_Rem, sa16j_pd_zero, sa16z_C1, Pi.zero_apply]
      have : partialDeriv idx φ = φ := funext fun y => sa16j_pd_zero idx φ y
      rw [this]; ring
    rw [this, eLpNorm_zero]; exact zero_le
  | succ j ih =>
    obtain ⟨K, hK0, hK⟩ := ih
    refine ⟨2 * K + C1 * j, by positivity, fun {μ φ} hμ hφ {Λ} hΛ hCb idx => ?_⟩
    obtain ⟨l, idx', rfl⟩ : ∃ (l : Fin d) (idx' : Fin j → Fin d), idx = Fin.cons l idx' :=
      ⟨idx 0, Fin.tail idx, (Fin.cons_self_tail idx).symm⟩
    have hfun : (fun x => sa16z_Rem s μ φ (j + 1) (Fin.cons l idx') x) =
        (fun x => sa16z_C1 s (sa16z_dm μ l) φ j idx' x) + (fun x => sa16z_Rem s (sa16z_dm μ l) φ j idx' x) +
          (fun x => sa16z_Rem s μ (sa16z_dm φ l) j idx' x) := by
      funext x
      simp only [Pi.add_apply]
      exact sa16z_Rem_cons hs0 hsd hμ hφ l idx' x
    rw [hfun]
    have hcb' : sa16z_Cb (j + 2) Λ (sa16z_dm μ l) := sa16z_Cb_dm hμ hCb l
    have e2 := hK (sa16z_dm_smooth hμ l) hφ hΛ hcb' idx'
    have e3 := hK hμ (sa16z_dm_cc hφ l) hΛ (sa16z_Cb_mono (by omega) hCb) idx'
    have e1 : eLpNorm (fun x => sa16z_C1 s (sa16z_dm μ l) φ j idx' x) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C1 * Λ * j) * sa16z_S p φ (j + 1) := by
      cases j with
      | zero =>
        have : (fun x => sa16z_C1 s (sa16z_dm μ l) φ 0 idx' x) = 0 := rfl
        rw [this, eLpNorm_zero]; exact zero_le
      | succ n =>
        have := hC1b (sa16z_dm_smooth hμ l) hφ hΛ (sa16z_Cb_mono (by omega) hcb') n idx'
        simpa using this
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
      _ ≤ (ENNReal.ofReal (C1 * Λ * j) * sa16z_S p φ (j + 1) + ENNReal.ofReal (K * Λ) * sa16z_S p φ (j + 1)) +
            ENNReal.ofReal (K * Λ) * sa16z_S p φ (j + 1) := by
          gcongr
          · exact e2.trans (by gcongr)
          · exact e3.trans (by gcongr)
      _ = ENNReal.ofReal ((2 * K + C1 * j) * Λ) * sa16z_S p φ (j + 1) := by
          rw [← add_mul, ← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 2; ring

end R5

end HRS.Whole.AppendixA.Phase2SA16R
