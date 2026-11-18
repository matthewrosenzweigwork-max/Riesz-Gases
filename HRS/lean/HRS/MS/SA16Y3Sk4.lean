import HRS.MS.SA16Y3Sk3

/-!
# S.A.16 (SA16Y3) Sk4: the bound `‖R_j(b,φ,idx)‖_p ≤ K Λ S_j(φ)` (packet P7, Hilbert corner)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.MH.AdjointRd

section Sk4
variable {d : ℕ} {s : ℝ}

theorem sa16y3_R_bound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) {p : ℝ} (hp : 1 < p)
    (i : Fin d) (j : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {b φ : Euc d → ℝ}, ContDiff ℝ ∞ b → IsCcInfty φ → ∀ {Λ : ℝ}, 0 ≤ Λ →
      sa16z_Cb (j + 1) Λ b → ∀ idx : Fin j → Fin d,
      eLpNorm (fun x => sa16y3_R s i b φ j idx x) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (K * Λ) * sa16z_S p φ j := by
  obtain ⟨CQ, hCQ, hQ⟩ := sa16y3_Q_jet (s := s) hd hs0 hsd hθ1 hp i
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    have : (1 : ℝ) ≤ p := hp.le
    simpa using ENNReal.ofReal_le_ofReal this
  induction j with
  | zero =>
    refine ⟨0, le_rfl, fun {b φ} hb hφ {Λ} hΛ hCb idx => ?_⟩
    rw [sa16y3_R_zero, eLpNorm_zero]; exact zero_le
  | succ j ih =>
    obtain ⟨K, hK0, hK⟩ := ih
    refine ⟨2 * K + 2 * CQ, by positivity, fun {b φ} hb hφ {Λ} hΛ hCb idx => ?_⟩
    obtain ⟨l, idx', rfl⟩ : ∃ (l : Fin d) (idx' : Fin j → Fin d), idx = Fin.cons l idx' :=
      ⟨idx 0, Fin.tail idx, (Fin.cons_self_tail idx).symm⟩
    have hfun : (fun x => sa16y3_R s i b φ (j + 1) (Fin.cons l idx') x) =
        (fun x => sa16y3_Q s i (fun y => sa16z_dm b l y * partialDeriv idx' φ y) x) +
          (fun x => sa16y3_R s i (sa16z_dm b l) φ j idx' x) + (fun x => sa16y3_R s i b (sa16z_dm φ l) j idx' x) := by
      funext x
      simp only [Pi.add_apply]
      exact sa16y3_R_cons hs0 hsd hb hφ i l idx' x
    rw [hfun]
    have hcb' : sa16z_Cb (j + 1) Λ (sa16z_dm b l) := sa16z_Cb_dm hb hCb l
    have e1 : eLpNorm (fun x => sa16y3_Q s i (fun y => sa16z_dm b l y * partialDeriv idx' φ y) x)
        (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (CQ * (Λ + Λ)) * sa16z_S p φ (j + 1) :=
      hQ (sa16z_dm_smooth hb l) hφ hΛ hΛ (sa16z_Cb_abs (sa16z_Cb_mono (by omega) hcb'))
        (sa16z_Cb_fderiv (sa16z_Cb_mono (by omega) hcb')) idx'
    have e2 := hK (sa16z_dm_smooth hb l) hφ hΛ hcb' idx'
    have e3 := hK hb (sa16z_dm_cc hφ l) hΛ (sa16z_Cb_mono (by omega) hCb) idx'
    have hS2 : sa16z_S p (sa16z_dm φ l) j ≤ sa16z_S p φ (j + 1) := sa16z_S_dm_le hφ.1 l j
    have hS1 : sa16z_S p φ j ≤ sa16z_S p φ (j + 1) := sa16z_S_mono φ (by omega)
    calc eLpNorm ((fun x => sa16y3_Q s i (fun y => sa16z_dm b l y * partialDeriv idx' φ y) x) +
          (fun x => sa16y3_R s i (sa16z_dm b l) φ j idx' x) + (fun x => sa16y3_R s i b (sa16z_dm φ l) j idx' x))
          (ENNReal.ofReal p) volume
        ≤ eLpNorm ((fun x => sa16y3_Q s i (fun y => sa16z_dm b l y * partialDeriv idx' φ y) x) +
          (fun x => sa16y3_R s i (sa16z_dm b l) φ j idx' x)) (ENNReal.ofReal p) volume +
          eLpNorm (fun x => sa16y3_R s i b (sa16z_dm φ l) j idx' x) (ENNReal.ofReal p) volume := eLpNorm_add_le hp1
      _ ≤ (eLpNorm (fun x => sa16y3_Q s i (fun y => sa16z_dm b l y * partialDeriv idx' φ y) x)
            (ENNReal.ofReal p) volume + eLpNorm (fun x => sa16y3_R s i (sa16z_dm b l) φ j idx' x)
            (ENNReal.ofReal p) volume) +
          eLpNorm (fun x => sa16y3_R s i b (sa16z_dm φ l) j idx' x) (ENNReal.ofReal p) volume := by
          gcongr; exact eLpNorm_add_le hp1
      _ ≤ (ENNReal.ofReal (CQ * (Λ + Λ)) * sa16z_S p φ (j + 1) + ENNReal.ofReal (K * Λ) * sa16z_S p φ (j + 1)) +
            ENNReal.ofReal (K * Λ) * sa16z_S p φ (j + 1) := by
          gcongr
          · exact e2.trans (by gcongr)
          · exact e3.trans (by gcongr)
      _ = ENNReal.ofReal ((2 * K + 2 * CQ) * Λ) * sa16z_S p φ (j + 1) := by
          rw [← add_mul, ← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 2; ring

end Sk4

end HRS.Whole.AppendixA.Phase2SA16R
