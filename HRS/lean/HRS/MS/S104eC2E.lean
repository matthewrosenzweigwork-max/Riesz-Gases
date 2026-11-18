import HRS.MS.S104eC2C
import HRS.MS.S104eC2D
import HRS.MS.R2WinOrbNLAux11

/-!
# S104E route C, packet C2, part E: the nonlocal term `movForce (ρ ∂_i f)` on `C^{j+1,η}`

Prefix `s104c2_`, namespace `HRS.MS.S104e.C`.  For `ρ ∈ U2Dec (j+1) L A`, `L > d + j + s + 4`, `f ∈ HolB j η B`
(`max 0 (s-d+1) < η < 1`) and `v = e_i`:
`x ↦ movForce d s (ρ · ∂_v f) x i` is `C^j`, its jets up to order `j` are bounded by `C A B`, and they vanish at infinity.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.Ul HRS.MS.R2WinOrbNL

variable {d : ℕ}

theorem s104c2_force_term (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (j : ℕ) {η : ℝ}
    (hη0 : max 0 (s - d + 1) < η) (hη1 : η < 1) {L : ℝ} (hL : (d : ℝ) + j + s + 4 < L) (v : Euc d)
    (i : Fin d) (hv : ‖v‖ = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ) (ρ : Euc d → ℝ), 0 ≤ A → U2Dec (j + 1) L A ρ →
      ∀ (B : ℝ) (f : Euc d → ℝ), HolB j η B f →
        ContDiff ℝ j (fun x => movForce d s (fun y => ρ y * fderiv ℝ f y v) x i) ∧
        (∀ m ≤ j, ∀ x, ‖iteratedFDeriv ℝ m (fun x => movForce d s (fun y => ρ y * fderiv ℝ f y v) x i) x‖ ≤ C * A * B) ∧
        VanB j (fun x => movForce d s (fun y => ρ y * fderiv ℝ f y v) x i) := by
  have hηp : 0 < η := lt_of_le_of_lt (le_max_left _ _) hη0
  have hηd : s + 1 - η < (d : ℝ) := by
    have := lt_of_le_of_lt (le_max_right _ _) hη0
    linarith
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hd1 : 1 ≤ d := by omega
  have hsd' : s < (d : ℝ) := hsd
  have hL' : (d : ℝ) < L := by linarith
  have hL0 : 0 ≤ L := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hker := ult_ker_kap (d := d) hs0 hsd' i
  obtain ⟨CN, CF, hCN, hCF, hKb⟩ := s104c2_K_bound hd1 hker hη1 hηd hL'
  refine ⟨CN * (2 ^ j * 3) + CF * 2 ^ j, by positivity, fun A ρ hA hρ B f hf => ?_⟩
  have hB0 : 0 ≤ B := hf.bd.nonneg
  obtain ⟨hkd, hkh⟩ := s104c2_k_data hηp hη1.le hL0 hρ hf v
  rw [hv] at hkd hkh
  set k : Euc d → ℝ := fun y => ρ y * fderiv ℝ f y v with hk
  have hA' : 0 ≤ A * (B * 1) * 2 ^ j := by positivity
  have hH : 0 ≤ 2 ^ j * A * (B * 1 + 2 * (B * 1)) := by positivity
  have hkb0 : ∀ y, ‖k y‖ ≤ A * (B * 1) * 2 ^ j * u2Wt L y := fun y => by
    have := hkd.2 0 (Nat.zero_le _) y
    rwa [norm_iteratedFDeriv_zero] at this
  have hkc : Continuous k := hkd.1.continuous
  have hfun : (fun x => movForce d s k x i) = ultK (u2_kap d s i) k := by
    funext x
    exact (s104c2_conv_comp hd1 hs0 hsd' hη1 hηd hH hL' hA' hkc (s104c2_hol_zero (hkh 0 (Nat.zero_le _))) hkb0 x).2 i
  obtain ⟨hit, hcd⟩ := s104c2_K_iter hd1 hker hη1 hηd hH hL' hA' hkd hkh
  rw [hfun]
  refine ⟨hcd, fun m hm x => ?_, fun m hm => ?_⟩
  · rw [hit m hm x]
    have hmc : Continuous (iteratedFDeriv ℝ m k) := hkd.1.continuous_iteratedFDeriv (by exact_mod_cast hm)
    have := hKb (Euc d [×m]→L[ℝ] ℝ) (iteratedFDeriv ℝ m k) (2 ^ j * A * (B * 1 + 2 * (B * 1)))
      (A * (B * 1) * 2 ^ j) hH hA' (hkh m hm) (fun y => hkd.2 m hm y) x
    refine this.trans (le_of_eq ?_)
    ring
  · have hmc : Continuous (iteratedFDeriv ℝ m k) := hkd.1.continuous_iteratedFDeriv (by exact_mod_cast hm)
    have hfn : (fun x => ‖iteratedFDeriv ℝ m (ultK (u2_kap d s i) k) x‖) =
        fun x => ‖ultK (u2_kap d s i) (iteratedFDeriv ℝ m k) x‖ := funext fun x => by rw [hit m hm x]
    rw [hfn]
    have := (s104c2_K_van hd1 hker hη1 hηd hH hL' hmc (hkh m hm) hA' (fun y => hkd.2 m hm y)).norm
    simpa using this

end HRS.MS.S104e.C

end
