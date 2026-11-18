import HRS.MS.WsInitGAux4
import HRS.MS.WsStatAux16

/-!
# S21 packet G, part 5: the stationary orbit data

`s21g_stat_cos`: for the stationary quadratic coefficient `C = (quadraticGradientDyn d s a β).coeff (fun _ => ρ)` of a thermal equilibrium `ρ`,
`m = wholeSpaceIndex d`, `T > 0` and `J = ⌊d/2⌋ + 3 > d/2 + 2`: the cosine orbit tests `r2CosOrbitTest C m T n α` are in `C_b^J`, summable in
`C_b^J`-norm, and the orbit `t ↦ U^{0,t} φ_α(x)` is continuous on `[0,T]` (the inputs of `HRS.Whole.r2_static_observation_path*`).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S21

open HRS HRS.Whole HRS.MS.Ul HRS.MS.S52B HRS.MS.S53

variable {d : ℕ}

/-- The integer `J = ⌊d/2⌋ + 3`, `J > d/2 + 2`. -/
def s21gJ (d : ℕ) : ℕ := ⌊(d : ℝ) / 2⌋₊ + 3

theorem s21gJ_gt (d : ℕ) : (d : ℝ) / 2 + 2 < (s21gJ d : ℕ) := by
  unfold s21gJ
  have h : (d : ℝ) / 2 < ((⌊(d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast; exact Nat.lt_floor_add_one _
  push_cast at h ⊢
  linarith

/-- The level `K0` of the orbit estimates. -/
def s21gK0 (d : ℕ) : ℕ := max (⌊(4 : ℝ) + (d : ℝ) / 2⌋₊ + 1) (⌊((s21gJ d : ℕ) : ℝ) + (d : ℝ) / 2⌋₊ + 1)

theorem s21gK0_gt (d : ℕ) : (4 : ℝ) + (d : ℝ) / 2 < (s21gK0 d : ℕ) ∧
    ((s21gJ d : ℕ) : ℝ) + (d : ℝ) / 2 < (s21gK0 d : ℕ) := by
  have h1 : (4 : ℝ) + (d : ℝ) / 2 < ((⌊(4 : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast; exact Nat.lt_floor_add_one _
  have h2 : ((s21gJ d : ℕ) : ℝ) + (d : ℝ) / 2 < ((⌊((s21gJ d : ℕ) : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast; exact Nat.lt_floor_add_one _
  unfold s21gK0
  exact ⟨h1.trans_le (by exact_mod_cast le_max_left _ _), h2.trans_le (by exact_mod_cast le_max_right _ _)⟩

theorem s21g_index_bound (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) :
    ((s52bIdx d s (s21gK0 d + 4) : ℕ) : ℝ) + 3 * d < ((wholeSpaceIndex d : ℕ) : ℝ) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : ((⌊(4 : ℝ) + (d : ℝ) / 2⌋₊ : ℕ) : ℝ) ≤ 4 + (d : ℝ) / 2 := Nat.floor_le (by positivity)
  have hJ : ((s21gJ d : ℕ) : ℝ) ≤ (d : ℝ) / 2 + 3 := by
    unfold s21gJ
    have : ((⌊(d : ℝ) / 2⌋₊ : ℕ) : ℝ) ≤ (d : ℝ) / 2 := Nat.floor_le (by positivity)
    push_cast; linarith
  have h2 : ((⌊((s21gJ d : ℕ) : ℝ) + (d : ℝ) / 2⌋₊ : ℕ) : ℝ) ≤ ((s21gJ d : ℕ) : ℝ) + (d : ℝ) / 2 :=
    Nat.floor_le (by positivity)
  have hK0 : ((s21gK0 d : ℕ) : ℝ) ≤ (d : ℝ) + 4 := by
    unfold s21gK0
    have : ((max (⌊(4 : ℝ) + (d : ℝ) / 2⌋₊ + 1) (⌊((s21gJ d : ℕ) : ℝ) + (d : ℝ) / 2⌋₊ + 1) : ℕ) : ℝ) ≤ (d : ℝ) + 4 := by
      rcases le_total (⌊(4 : ℝ) + (d : ℝ) / 2⌋₊ + 1) (⌊((s21gJ d : ℕ) : ℝ) + (d : ℝ) / 2⌋₊ + 1) with h | h
      · rw [max_eq_right h]; push_cast; linarith
      · rw [max_eq_left h]; push_cast; linarith
    exact this
  have h3 : ((⌈s + 1⌉₊ : ℕ) : ℝ) < s + 1 + 1 := Nat.ceil_lt_add_one (by linarith)
  have h4 : ((⌊(d : ℝ) / 2⌋₊ : ℕ) : ℝ) ≤ (d : ℝ) / 2 := Nat.floor_le (by positivity)
  unfold s52bIdx wholeSpaceIndex
  push_cast
  linarith

theorem s21g_orbit_stat (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {T : ℝ} (hT : 0 ≤ T) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) :
    ∃ (b : MultiIndex d → ℝ) (K : ℝ) (G0 G1 G2 G3 : MultiIndex d → ℝ → Euc d → ℝ),
      S21GOrbit ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T K
        (s21gJ d) b G0 G1 G2 G3 := by
  have hρS : IsSchwartzDensity ρ := by
    rw [HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ]; exact s21_schwartz_thermal hd hs0 hsd ha hβ
  have hν : 0 < β⁻¹ := inv_pos.2 hβ
  obtain ⟨θ, hθ⟩ := s52b_exists_ulCutoff d
  have hO : UlOrb d s β⁻¹ ρ (fun _ => (0 : Euc d)) (fun x => (fun _ : Euc d => (0 : Euc d)) x -
      convGradConvW (rieszKernelGrad d s) ρ x) θ :=
    ⟨hd, hs0, hsd, hν, hρS.2.elim fun ψ hψ => ⟨ψ, hψ⟩, fun i => ⟨0, by ext x; simp⟩, rfl, hθ⟩
  have huniq := s53_uniq hd hs0 hsd hν (a • (1 : Matrix (Fin d) (Fin d) ℝ)) hρS T
  rw [s53_coeff_eq] at huniq
  obtain ⟨hK4, hkK⟩ := s21gK0_gt d
  obtain ⟨b, K, G0, G1, G2, G3, Orb⟩ := s21g_orbit_of_uniq hO (Torus.symPart (a • (1 : Matrix (Fin d) (Fin d) ℝ)))
    ((wholeSpaceIndex d : ℕ) : ℝ) hT huniq (s21gJ d) (s21gK0 d) hK4 hkK (s21g_index_bound hd s hs0 hsd)
  rw [← s53_coeff_eq, ← s21_dyn_eq] at Orb
  exact ⟨b, K, G0, G1, G2, G3, Orb⟩

theorem s21g_stat_cos (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {T : ℝ} (hT : 0 < T) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) :
    (∀ n α, MemCb (s21gJ d) (r2CosOrbitTest ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
      ((wholeSpaceIndex d : ℕ) : ℝ) T n α)) ∧
    (Summable fun q : ℕ × MultiIndex d => cbNorm (s21gJ d) (r2CosOrbitTest
      ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T q.1 q.2)) ∧
    (∀ (α : MultiIndex d) (x : Euc d), ContinuousOn (fun t => propagatorW
      ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 t (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) x)
      (Set.Icc (0 : ℝ) T)) := by
  obtain ⟨b, K, G0, G1, G2, G3, Orb⟩ := s21g_orbit_stat hd hs0 hsd ha hβ hT.le hρ
  exact s21g_orbit_cos hT Orb

/-- The product decay of the cosine tests, `cbNorm_J(f_{n,α})² ≤ B (1+n)^{-5/2} V_α` with `∑ V^{2/5} < ∞` (input of the `W_1` projection
tails of packet H, `W:r2:initial-orbit-summability`). -/
theorem s21g_stat_decay (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {T : ℝ} (hT : 0 < T) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) :
    ∃ (B : ℝ) (V : MultiIndex d → ℝ), 0 ≤ B ∧ (∀ α, 0 ≤ V α) ∧
      (Summable fun α => V α ^ ((2 : ℝ) / 5)) ∧
      ∀ (n : ℕ) (α : MultiIndex d), cbNorm (s21gJ d) (r2CosOrbitTest ((quadraticGradientDyn d s a β).coeff
        (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T n α) ^ 2 ≤ B * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 2) * V α := by
  obtain ⟨b, K, G0, G1, G2, G3, Orb⟩ := s21g_orbit_stat hd hs0 hsd ha hβ hT.le hρ
  obtain ⟨-, -, -, B1, hB1, hdec⟩ := s21g_orbit_cos_full hT Orb
  refine ⟨B1 ^ 2, fun α => b α ^ 2, by positivity, fun α => by positivity, ?_, fun n α => ?_⟩
  · refine Orb.b_pow.congr fun α => ?_
    show b α ^ ((4 : ℝ) / 5) = (b α ^ 2) ^ ((2 : ℝ) / 5)
    rw [← Real.rpow_natCast (b α) 2, ← Real.rpow_mul (Orb.b_nonneg α)]
    norm_num
  · have h0 := HRS.MS.Tc5.tc5_cb_nonneg (d := d) (s21gJ d) (r2CosOrbitTest ((quadraticGradientDyn d s a β).coeff
        (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T n α)
    have h1 := hdec n α
    have hx : 0 ≤ (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
    have hx2 : ((1 + (n : ℝ)) ^ (-(5 : ℝ) / 4)) ^ 2 = (1 + (n : ℝ)) ^ (-(5 : ℝ) / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    calc _ ≤ (B1 * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * b α) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = B1 ^ 2 * ((1 + (n : ℝ)) ^ (-(5 : ℝ) / 4)) ^ 2 * b α ^ 2 := by ring
      _ = _ := by rw [hx2]

end HRS.MS.S21
