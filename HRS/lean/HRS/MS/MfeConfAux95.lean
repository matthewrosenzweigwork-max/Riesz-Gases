import HRS.MS.MfeConfAux94

/-!
# S.B.1, packet F8 (part 27): `H + Ψ_0` is bounded below (the level-`k` reference density at time `0` is bounded above)
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section Traj

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ) (hT : 0 ≤ T)
  {r₀ : ℝ} {k : Euc d → ℝ}

include H hT

theorem sb1_lv_hC0 (hk4 : IsP4Kernel d D.s r₀ k) (hθ : 0 < D.invβ) (hN : 1 ≤ N) :
    ∃ C0 : ℝ, ∀ x : EucConfig d N, 0 ≤ sb1Hs D k N x +
      (∑ i, sb1_lv_Psi D k hT ρ 0 (x i) + sb1_lv_kappa D k N hT ρ 0) + C0 := by
  have hk := sb1KerU_of_p4 H.tr.hs0 hk4
  have hβ : 0 ≤ D.invβ⁻¹ := (inv_pos.2 hθ).le
  obtain ⟨m, M, hm, hmM⟩ := sb1_lv_Kb_bounds H hT hk hβ hN (N := N)
  have hR := sb1_lv_rb_rho H hT 0
  have hC3 := H.C3nn
  set Cq := m⁻¹ * (C3 ^ N * Real.exp (D.invβ⁻¹ * N * (sb1CG d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y) +
    sb1kap D.s * (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y)))) with hCq
  refine ⟨D.invβ * Real.log Cq, fun x => ?_⟩
  have hpos := sb1_lv_rb_pos H hT 0
  have hKp := sb1_lv_Kb_pos H hT hk hβ hN 0 (N := N)
  have hΨ := sb1_Psi_onebody D k hθ (s := 0) (ρ := sb1_lv_rb hT ρ) (hpos) hKp hN x
  have hid : ∑ i, sb1_lv_Psi D k hT ρ 0 (x i) + sb1_lv_kappa D k N hT ρ 0 =
      sb1Psi D.invβ (sb1Hs D k N) k D.invβ⁻¹ (sb1_lv_rb hT ρ) 0 x := hΨ.symm
  rw [hid]
  unfold sb1Psi
  have hq : 0 < sb1qd k D.invβ⁻¹ N (sb1_lv_rb hT ρ 0) x := by
    unfold sb1qd
    exact mul_pos (inv_pos.2 hKp) (mul_pos (Finset.prod_pos fun i _ => hpos (x i)) (Real.exp_pos _))
  have hle : sb1qd k D.invβ⁻¹ N (sb1_lv_rb hT ρ 0) x ≤ Cq := by
    unfold sb1qd
    have h1 : ∏ i, sb1_lv_rb hT ρ 0 (x i) ≤ C3 ^ N := by
      calc _ ≤ ∏ i : Fin N, C3 := Finset.prod_le_prod₀ (fun i _ => (hpos (x i)).le) (fun i _ => hR.le (x i))
        _ = _ := by simp
    have h2 := sb1_E_le H.tr.hd H.tr.hs0 H.tr.hsd hN hβ hk hR x
    have h3 : (Whole.gibbsNormalizer k N D.invβ⁻¹ (Whole.withDensityReal (sb1_lv_rb hT ρ 0)))⁻¹ ≤ m⁻¹ :=
      inv_anti₀ hm (hmM 0).1
    calc _ ≤ m⁻¹ * ((C3 ^ N) * Real.exp (D.invβ⁻¹ * N * (sb1CG d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y) +
          sb1kap D.s * (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y)))) := by
          exact mul_le_mul h3 (mul_le_mul h1 h2 (Real.exp_pos _).le (pow_nonneg hC3 N))
            (mul_nonneg (Finset.prod_nonneg fun i _ => (hpos (x i)).le) (Real.exp_pos _).le) (inv_pos.2 hm).le
      _ = Cq := rfl
  have hlog := Real.log_le_log hq hle
  have : D.invβ * Real.log (sb1qd k D.invβ⁻¹ N (sb1_lv_rb hT ρ 0) x) ≤ D.invβ * Real.log Cq :=
    mul_le_mul_of_nonneg_left hlog hθ.le
  linarith

end Traj

end HRS.MS.MfeConf
