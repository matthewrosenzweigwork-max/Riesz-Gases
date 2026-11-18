import HRS.MS.R26T8AP15t
import HRS.MS.R26T8AP14b
import HRS.MS.R26T8AZ7b
import HRS.MS.R26T8AP11g5

/-!
# S8.2 T8A Z7d (= P15 same-k): `r26t8a_local_defect_bound_same`
The Pro P15 contract (without `CanonicalPair F`) for every `σ < d` with the hypothesis `Conormal (k+2) 0 M σ A F`; the proof of `r26t8a_local_defect_bound_same`
with the same-`k` P07/P09 (Z6, Z7b).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem r26t8a_local_defect_bound_same (d : ℕ) (hd : 2 ≤ d) (k : ℕ)
    (a beta M sigma : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    (hsd : sigma < d) (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A →
      Conormal (k + 2) 0 M sigma A F →
      Conormal k 1 (M + 2) (sigma - 2) (C * A)
        (fun x y => newtonDefect (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi F x y -
          pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho)
            (localNewton (HRS.Whole.withDensityReal rho) beta⁻¹ chi F) x y) := by
  classical
  by_cases hex : ∃ ρ0 : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta ρ0
  swap
  · exact ⟨0, le_rfl, fun rho hrho => absurd ⟨rho, hrho⟩ hex⟩
  obtain ⟨ρ0, h0⟩ := hex
  have hν : 0 < beta⁻¹ := inv_pos.2 hbeta
  obtain ⟨C1, hC10, hC1⟩ := r26t8a_raw_newton_bound_same d hd (k + 2) 0 beta⁻¹ M sigma hν hM hsd chi hchi
  obtain ⟨C2, hC20, hC2⟩ := r26t8a_local_newton_bound_same d hd (k + 2) 0 a beta M sigma ha hbeta hM hsd chi hchi
  obtain ⟨B, hB0, hBα⟩ := r26t8a_drift_coord hd a beta ha hbeta h0 (k + 1)
  set α : Fin d → Euc d → ℝ := fun i x => -(forceMean ρ0 x i) - a * x i with hαdef
  have hα1 : ∀ i, ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (α i) := fun i => (hBα i).1
  have hαb1 : ∀ i, ∀ j ≤ k + 1, ∀ x, ‖iteratedFDeriv ℝ j (α i) x‖ ≤ B * jbracket x := fun i => (hBα i).2
  have hαk : ∀ i, ContDiff ℝ (k : WithTop ℕ∞) (α i) := fun i =>
    (hα1 i).of_le (by exact_mod_cast Nat.le_succ k)
  have hαbk : ∀ i, ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (α i) x‖ ≤ B * jbracket x :=
    fun i j hj x => hαb1 i j (by omega) x
  have hb : ∀ i x, (critCoeff d a beta ρ0).drift 0 x i = α i x := fun i x => r26t8a_drift_coord_eq a beta ρ0 i x
  obtain ⟨cT, hcT0, hT⟩ := r26t8a_Tloc_conormal hchi k M sigma beta⁻¹ B hB0 α hα1 hαb1
  obtain ⟨cx, hcx0, hOx⟩ := r26t8a_Lop_onevar_x hchi (critCoeff d a beta ρ0) α hb k M B (sigma - 2) hB0 hM hαk hαbk
  obtain ⟨cy, hcy0, hOy⟩ := r26t8a_Lop_onevar_y hchi (critCoeff d a beta ρ0) α hb k M B (sigma - 2) hB0 hM hαk hαbk
  obtain ⟨Crx, hCrx0, hrx⟩ := r26t8a_p15_rowx hd (k + 2) 1 a beta M (sigma - 2) ha hbeta hM (by linarith) h0
  obtain ⟨Cry, hCry0, hry⟩ := r26t8a_p15_rowy hchi hd (k + 2) 1 a beta M (sigma - 2) ha hbeta hM (by linarith) h0
  obtain ⟨Cl, hCl0, hell⟩ := r26t8a_p15_ell hchi hd (critCoeff d a beta ρ0) α hb k a beta M sigma B ha hbeta hM
    hsd hB0 hαk hαbk h0
  set κ : ℝ := 2 ^ k * (((k : ℝ) + 1) ^ 2) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  refine ⟨cT * (C1 + 1) + κ * (cx * (Crx * C1) + cy * (Cry * C1) + 2 * (Cl * C2)), by positivity,
    fun rho hrho F A hA hF => ?_⟩
  have hρeq : rho = ρ0 :=
    (critical_thermal_eq d hd a beta ha hbeta hrho).trans (critical_thermal_eq d hd a beta ha hbeta h0).symm
  subst hρeq
  have hprob : HRS.Whole.IsProbDensity rho := hrho.1.1
  set mu := HRS.Whole.withDensityReal rho with hmu
  set C0 := critCoeff d a beta rho with hC0
  set R : Euc d → Euc d → ℝ := rawNewton beta⁻¹ chi F with hRdef
  set Q : Euc d → Euc d → ℝ := localNewton mu beta⁻¹ chi F with hQdef
  have hQeq : Q = r2CenterKernel mu R := rfl
  -- conormal data
  obtain ⟨-, hR'⟩ := hC1 F A hA hF
  obtain ⟨-, -, hQ'⟩ := hC2 rho hrho F A hA hF
  have hR1 : Conormal (k + 2) 1 M (sigma - 2) (C1 * A) R := hR'
  have hQ1 : Conormal (k + 2) 1 M (sigma - 2) (C2 * A) Q := hQ'
  have hF0 : Conormal k 0 M sigma A F :=
    r26t8a_conormal_mono (by omega) hF
  have hF2 : Conormal 2 0 M sigma A F :=
    r26t8a_conormal_mono (by omega) hF
  have hRcd : ∀ x y : Euc d, x ≠ y → ContDiffAt ℝ 2 (fun q : Euc d × Euc d => R q.1 q.2) (x, y) :=
    fun x y hxy => r26t8a_cd2_of_conormal hR1 hxy
  have hC1A : 0 ≤ C1 * A := mul_nonneg hC10 hA
  have hC2A : 0 ≤ C2 * A := mul_nonneg hC20 hA
  -- principal cancellation
  have hcancel : ∀ x y : Euc d, x ≠ y → ‖x - y‖ < 1 → F x y + 2 * beta⁻¹ * r26t8a_ZZ R x y = 0 := by
    intro x y hxy hxy1
    have hcan := r26t8a_principal_newton_cancel2 d hd beta⁻¹ hν chi hchi F A M sigma hM hA hsd hF2
      ((1 / 2 : ℝ) • (x + y)) (x - y) (sub_ne_zero.2 hxy) hxy1
    rw [← r26t8a_p15_ZZ (hRcd x y hxy)]
    have hm : midPair F ((1 / 2 : ℝ) • (x + y)) (x - y) = F x y := by
      show F (((1 / 2 : ℝ) • (x + y)) + (1 / 2 : ℝ) • (x - y)) (((1 / 2 : ℝ) • (x + y)) - (1 / 2 : ℝ) • (x - y)) = _
      congr 1 <;> module
    rw [hm] at hcan
    linarith
  -- row averages
  obtain ⟨-, hs1, hj1⟩ := hrx R (C1 * A) hC1A hR1
  obtain ⟨-, hs2, hj2⟩ := hry R (C1 * A) hC1A hR1
  set r1 : Euc d → ℝ := fun x => ∫ y', R x y' ∂mu with hr1
  set r2 : Euc d → ℝ := fun y => ∫ x', R x' y ∂mu with hr2
  have hU1 := hOx r1 (Crx * (C1 * A)) (by positivity) hs1 (fun j hj x => hj1 j hj x)
  have hU2 := hOy r2 (Cry * (C1 * A)) (by positivity) hs2 (fun j hj x => hj2 j hj x)
  obtain ⟨hint1, hint3, hE1, hE2⟩ := hell Q (C2 * A) hC2A hQ1
  have hint2 : ∀ y, Integrable (oneJ C0 (fun u => Q u y)) mu := fun y =>
    (r26t8a_g5_row d hd k 1 a beta M sigma ha hbeta hM hsd rho hrho Q (C2 * A) hC2A hQ1 y).1
  have hQs : Conormal (k + 2) 1 M (sigma - 2) (C2 * A) (fun x y => Q y x) :=
    r26t8a_f24_conormal_swap hchi hQ1
  have hint4 : ∀ x, Integrable (oneJ C0 (Q x)) mu := fun x =>
    (r26t8a_g5_row d hd k 1 a beta M sigma ha hbeta hM hsd rho hrho (fun x y => Q y x) (C2 * A) hC2A hQs x).1
  -- the local part
  have hTl := hT R F (C1 * A) A hC1A hA hR1 hF0 hcancel
  -- combination
  have c1 := r26t8a_conormal_sub hchi (by positivity) (by positivity) hTl hU1
  have c2 := r26t8a_conormal_sub hchi (by positivity) (by positivity) c1 hU2
  have c3 := r26t8a_conormal_sub hchi (by positivity) (by positivity) c2 hE1
  have c4 := r26t8a_conormal_sub hchi (by positivity) (by positivity) c3 hE2
  have c5 := r26t8a_conormal_mono_M (by positivity) (by linarith : M + 1 ≤ M + 2) c4
  refine r26t8a_conormal_congr (fun x y hxy => ?_)
    (r26t8a_conormal_mono_sA (by positivity) (le_of_eq ?_) le_rfl c5)
  · -- pointwise identity
    beta_reduce
    have hCnu : C0.ν = beta⁻¹ := r26t8a_critCoeff_nu a beta rho
    have e1 : newtonDefect C0 mu chi F x y = F x y + pairA C0 mu Q x y := by
      show F x y + pairA C0 mu (localNewton mu C0.ν chi F) x y = _
      rw [hCnu]
    have e2 := r26t8a_p15_defect_alg C0 mu Q x y (hint1 y) (hint2 y) (hint3 x) (hint4 x)
    have e3 : r26t8a_Lop C0 (fun w => Q w y) x =
        r26t8a_Lop C0 (fun w => R w y) x - r26t8a_Lop C0 r1 x :=
      r26t8a_Lop_centre_x C0 mu R x y (r26t8a_slice_x hR1 hxy)
        (hs1.contDiffAt.of_le (by exact_mod_cast (by omega : 2 ≤ k + 2)))
    have e4 : r26t8a_Lop C0 (Q x) y = r26t8a_Lop C0 (R x) y - r26t8a_Lop C0 r2 y :=
      r26t8a_Lop_centre_y C0 mu R x y (r26t8a_slice_y hR1 hxy)
        (hs2.contDiffAt.of_le (by exact_mod_cast (by omega : 2 ≤ k + 2)))
    have e5 : F x y + (r26t8a_Lop C0 (fun w => R w y) x + r26t8a_Lop C0 (R x) y) =
        r26t8a_Tloc beta⁻¹ α R F x y := by
      have := r26t8a_Tloc_eq C0 α hb R F x y (hRcd x y hxy)
      rwa [hCnu] at this
    linarith [e1, e2, e3, e4, e5]
  · simp only [hκ]; ring

end HRS.MS.R26T8A
