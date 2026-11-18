import HRS.MS.SA16ZD4

/-!
# S.A.16 (SA16Z) D5: `‖Err_idx‖_p ≤ K Λ S_j(φ)`
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section D5
variable {d : ℕ} {s : ℝ}

theorem sa16z_Err_bound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) {p : ℝ} (hp : 2 ≤ p)
    (c : ℝ) :
    ∃ cθ : ℝ, ∀ j : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ {μ φ : Euc d → ℝ}, ContDiff ℝ ∞ μ → IsCcInfty φ → ∀ {Λ : ℝ}, 0 ≤ Λ →
      sa16z_Cb (j + 3) Λ μ → ∀ (idx : Fin j → Fin d),
      eLpNorm (fun x => sa16z_Err s c cθ μ φ j idx x) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (K * Λ) * sa16z_S p φ j := by
  have hp1 : 1 < p := by linarith
  have hθ2 : s + 2 - (d : ℝ) < 2 := by linarith
  have hp1' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp1.le
  obtain ⟨cθ, Ce, Cp, hCe, hCp, hR', hCm⟩ := sa16z_comm_consts hd hθ1 hθ2 hp
  obtain ⟨C1, hC1, hRem⟩ := sa16z_Rem_bound hd hs0 hsd hθ1 hp1
  refine ⟨cθ, fun j => ?_⟩
  obtain ⟨K0, hK0, hRemj⟩ := hRem j
  set cs := HRS.CZ.Hls.hlsg_c s with hcs
  have hcs0 : 0 ≤ cs := HRS.CZ.Hls.hlsg_c_nonneg hs0
  refine ⟨K0 + |c| * (Ce * 3) + cs * d * (Cp * 2) + cs * d * j * (Cp * 2), by positivity,
    fun {μ φ} hμ hφ {Λ} hΛ hCb idx => ?_⟩
  have hCb2 : sa16z_Cb 2 Λ μ := sa16z_Cb_mono (by omega) hCb
  have hmem2 : HRS.MemCb 2 μ := sa16z_memCb hμ hCb2
  have hcb2 : HRS.cbNorm 2 μ ≤ 3 * Λ := by
    have := sa16z_cbNorm_le hCb2; push_cast at this; linarith
  have hWj : ∀ {k : ℕ} (κ : Fin k → Fin d), eLpNorm (partialDeriv κ φ) (ENNReal.ofReal p) volume ≤
      sa16z_S p φ k := fun {k} κ => (sa16z_eLpNorm_pd_le hφ.1 κ).trans (sa16z_JJ_le_S φ le_rfl)
  have hSmono : ∀ {k : ℕ}, k ≤ j → sa16z_S p φ k ≤ sa16z_S p φ j := fun {k} hk => sa16z_S_mono φ hk
  -- the four terms
  have e1 := hRemj hμ hφ hΛ (sa16z_Cb_mono (by omega) hCb) idx
  have e2 : eLpNorm (fun x => sa16z_Rp d (s + 2 - d) cθ μ (partialDeriv idx φ) x) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (Ce * 3 * Λ) * sa16z_S p φ j := by
    refine (hR' hmem2 hφ idx).trans ?_
    have : ENNReal.ofReal (Ce * HRS.cbNorm 2 μ) ≤ ENNReal.ofReal (Ce * 3 * Λ) :=
      ENNReal.ofReal_le_ofReal (by nlinarith)
    exact mul_le_mul' this (hWj idx)
  have hcbl : ∀ a : Fin d, HRS.MemCb 1 (sa16z_dm μ a) ∧ HRS.cbNorm 1 (sa16z_dm μ a) ≤ 2 * Λ := by
    intro a
    have h1 : sa16z_Cb 1 Λ (sa16z_dm μ a) := sa16z_Cb_dm hμ (sa16z_Cb_mono (by omega) hCb) a
    exact ⟨sa16z_memCb (sa16z_dm_smooth hμ a) h1, by have := sa16z_cbNorm_le h1; push_cast at this; linarith⟩
  have e3 : eLpNorm (fun x => ∑ l : Fin d, sa16z_Cm d (s + 2 - d) l (sa16z_dm μ l) (partialDeriv idx φ) x)
      (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (d * (Cp * 2 * Λ)) * sa16z_S p φ j := by
    have hf : (fun x => ∑ l : Fin d, sa16z_Cm d (s + 2 - d) l (sa16z_dm μ l) (partialDeriv idx φ) x) =
        ∑ l : Fin d, fun x => sa16z_Cm d (s + 2 - d) l (sa16z_dm μ l) (partialDeriv idx φ) x := by
      funext x; simp [Finset.sum_apply]
    rw [hf]
    refine (eLpNorm_sum_le hp1').trans ?_
    calc ∑ l : Fin d, eLpNorm (fun x => sa16z_Cm d (s + 2 - d) l (sa16z_dm μ l) (partialDeriv idx φ) x)
          (ENNReal.ofReal p) volume
        ≤ ∑ l : Fin d, ENNReal.ofReal (Cp * (2 * Λ)) * sa16z_S p φ j := by
          refine Finset.sum_le_sum fun l _ => (hCm (hcbl l).1 hφ l idx).trans ?_
          exact mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hcbl l).2 hCp)) (hWj idx)
      _ = ENNReal.ofReal (d * (Cp * 2 * Λ)) * sa16z_S p φ j := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg d), ENNReal.ofReal_natCast, mul_assoc]
          congr 2; ring_nf
  have e4 : eLpNorm (fun x => ∑ l : Fin d, sa16z_Q j idx l
      (fun a κ => sa16z_Cm d (s + 2 - d) l (sa16z_dm μ a) (partialDeriv κ φ) x)) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (d * j * (Cp * 2 * Λ)) * sa16z_S p φ j := by
    cases j with
    | zero => simp [sa16z_Q]
    | succ n =>
      simp only [sa16z_Q]
      have hf : (fun x => ∑ l : Fin d, ∑ q : Fin (n + 1), sa16z_Cm d (s + 2 - d) l (sa16z_dm μ (idx q))
          (partialDeriv (Fin.cons l (Fin.removeNth q idx) : Fin (n + 1) → Fin d) φ) x) =
          ∑ l : Fin d, ∑ q : Fin (n + 1), fun x => sa16z_Cm d (s + 2 - d) l (sa16z_dm μ (idx q))
          (partialDeriv (Fin.cons l (Fin.removeNth q idx) : Fin (n + 1) → Fin d) φ) x := by
        funext x; simp [Finset.sum_apply]
      rw [hf]
      refine (eLpNorm_sum_le hp1').trans ((Finset.sum_le_sum fun l _ => (eLpNorm_sum_le hp1').trans
        (Finset.sum_le_sum fun q _ => (hCm (hcbl (idx q)).1 hφ l (Fin.cons l (Fin.removeNth q idx))).trans
          (mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hcbl (idx q)).2 hCp))
            (hWj (Fin.cons l (Fin.removeNth q idx)))))).trans ?_)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← mul_assoc, ← mul_assoc]
      refine le_of_eq ?_
      congr 1
      rw [show ((d : ℝ≥0∞) * ((n + 1 : ℕ) : ℝ≥0∞)) = ENNReal.ofReal ((d : ℝ) * ((n + 1 : ℕ) : ℝ)) by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg d), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast],
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1; ring
  -- assemble
  have hfun : (fun x => sa16z_Err s c cθ μ φ j idx x) =
      (fun x => sa16z_Rem s μ φ j idx x) + (-c) • (fun x => sa16z_Rp d (s + 2 - d) cθ μ (partialDeriv idx φ) x) +
        cs • (fun x => ∑ l : Fin d, sa16z_Cm d (s + 2 - d) l (sa16z_dm μ l) (partialDeriv idx φ) x) +
        (-cs) • (fun x => ∑ l : Fin d, sa16z_Q j idx l
          (fun a κ => sa16z_Cm d (s + 2 - d) l (sa16z_dm μ a) (partialDeriv κ φ) x)) := by
    funext x; simp only [sa16z_Err, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [hfun]
  have hn : ∀ (a : ℝ) (f : Euc d → ℝ), eLpNorm (a • f) (ENNReal.ofReal p) volume =
      ENNReal.ofReal |a| * eLpNorm f (ENNReal.ofReal p) volume := fun a f => by
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs]
  have e2' : eLpNorm ((-c) • (fun x => sa16z_Rp d (s + 2 - d) cθ μ (partialDeriv idx φ) x)) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal |c| * (ENNReal.ofReal (Ce * 3 * Λ) * sa16z_S p φ j) := by
    rw [hn, abs_neg]; exact mul_le_mul' le_rfl e2
  have e3' : eLpNorm (cs • (fun x => ∑ l : Fin d, sa16z_Cm d (s + 2 - d) l (sa16z_dm μ l) (partialDeriv idx φ) x))
      (ENNReal.ofReal p) volume ≤ ENNReal.ofReal cs * (ENNReal.ofReal (d * (Cp * 2 * Λ)) * sa16z_S p φ j) := by
    rw [hn, abs_of_nonneg hcs0]; exact mul_le_mul' le_rfl e3
  have e4' : eLpNorm ((-cs) • (fun x => ∑ l : Fin d, sa16z_Q j idx l
      (fun a κ => sa16z_Cm d (s + 2 - d) l (sa16z_dm μ a) (partialDeriv κ φ) x))) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal cs * (ENNReal.ofReal (d * j * (Cp * 2 * Λ)) * sa16z_S p φ j) := by
    rw [hn, abs_neg, abs_of_nonneg hcs0]; exact mul_le_mul' le_rfl e4
  refine (eLpNorm_add_le hp1').trans ?_
  refine (add_le_add ((eLpNorm_add_le hp1').trans (add_le_add ((eLpNorm_add_le hp1').trans (add_le_add e1 e2')) e3')) e4').trans ?_
  refine le_of_eq ?_
  have hc0 : 0 ≤ |c| := abs_nonneg c
  have m2 : ENNReal.ofReal |c| * (ENNReal.ofReal (Ce * 3 * Λ) * sa16z_S p φ j) =
      ENNReal.ofReal (|c| * (Ce * 3 * Λ)) * sa16z_S p φ j := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul hc0]
  have m3 : ENNReal.ofReal cs * (ENNReal.ofReal (d * (Cp * 2 * Λ)) * sa16z_S p φ j) =
      ENNReal.ofReal (cs * (d * (Cp * 2 * Λ))) * sa16z_S p φ j := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul hcs0]
  have m4 : ENNReal.ofReal cs * (ENNReal.ofReal (d * j * (Cp * 2 * Λ)) * sa16z_S p φ j) =
      ENNReal.ofReal (cs * (d * j * (Cp * 2 * Λ))) * sa16z_S p φ j := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul hcs0]
  rw [m2, m3, m4, ← add_mul, ← add_mul, ← add_mul,
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 2; ring

end D5

end HRS.Whole.AppendixA.Phase2SA16R
