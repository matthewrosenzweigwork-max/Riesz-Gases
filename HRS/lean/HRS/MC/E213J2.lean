import HRS.MC.S7PIDPPoly
import HRS.MC.E213I2

/-!
# Packet E213J2: family-quantified `s7_PID_poly` (Theorem 2.13, translation-uniform PI-D)

`e213j_poly` is `s7_PID_poly_proof` with the constant `C₁ = max 1 Cb` chosen before the shift `b ≥ 0`, for the regimes
`E213F.shift R b hb` at the fixed horizon `G`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213J

open HRS HRS.Sec7 HRS.MC.Sec7.PID HRS.MC.Sec7.PIE HRS.MC.Sec7.S7PIDP

variable {d : ℕ}

theorem e213j_poly (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (G : ℝ) (hG : 0 < G) :
    ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ b : ℝ, ∀ hb : 0 ≤ b,
      ∀ c c' : ℝ, 0 ≤ c → c ≤ c' → c' ≤ G → ∀ (n : ℕ) (v : ℕ → NegSobolev d m),
      (c < c' → ∀ t ∈ Set.Icc (0 : ℝ) G, pathAt (polyPath (HRS.MC.E213F.shift R b hb).D
          (HRS.MC.E213F.shift R b hb).ρ m G c c' n v) t =
        if t ≤ c' then polyAt c c' n v t else
          Vprop (HRS.MC.E213F.shift R b hb).D (HRS.MC.E213F.shift R b hb).ρ m t c' (v (2 ^ n))) ∧
      (∀ b' : ℝ, (∀ i ≤ 2 ^ n, ‖v i‖ ≤ b') →
        ‖polyPath (HRS.MC.E213F.shift R b hb).D (HRS.MC.E213F.shift R b hb).ρ m G c c' n v‖ ≤ C₁ * b') ∧
      (∀ B : ℝ, (∀ k < 2 ^ (n + 1), ‖v (k + 1) - v k‖ ≤ B) →
        ‖polyPath (HRS.MC.E213F.shift R b hb).D (HRS.MC.E213F.shift R b hb).ρ m G c c' (n + 1) v -
          polyPath (HRS.MC.E213F.shift R b hb).D (HRS.MC.E213F.shift R b hb).ρ m G c c' n (fun i => v (2 * i))‖ ≤ B) := by
  obtain ⟨k0, hk1, hk2, hk3, hkst, -⟩ := HRS.MC.Sec7.S7PIDV.S7PIDV_hyp R m hm 1 one_pos
  obtain ⟨L, Ac, Am, Cb, hL, hAc, hAm1, hCb, hU⟩ :=
    HRS.MC.E213I.e213i_V_unif_shift R k0 hk1 hkst m hk2 hk3 G hG
  obtain ⟨Rg, MB, Λ, VB, ν₀, hbundle⟩ := HRS.MC.E213F.adjointData_uniform R (k0 + 3)
  have hd1 : 1 ≤ d := by have := R.hd; omega
  have hn₀ : 1 ≤ k0 + 2 := by omega
  have hJ : k0 + 2 + 1 ≤ k0 + 3 := le_rfl
  have hm0 : ((k0 + 2 : ℕ) : ℝ) < m := by push_cast; exact hk2
  have hm1 : m ≤ ((k0 + 2 : ℕ) : ℝ) + 1 := by push_cast; linarith
  refine ⟨max 1 Cb, le_max_left _ _, fun b₀ hb₀ => ?_⟩
  have H : PIEHyp (k0 + 3) (HRS.MC.E213F.shift R b₀ hb₀).D (HRS.MC.E213F.shift R b₀ hb₀).ρ G :=
    ⟨hd1, by omega, Rg, MB, Λ, VB, ν₀, hbundle G hG b₀ hb₀⟩
  set Rb := HRS.MC.E213F.shift R b₀ hb₀ with hRb
  intro c c' hc hcc hc'G n v
  refine ⟨?_, ?_, ?_⟩
  · -- (a) the genuine continuous path on `[0,G]`
    intro hlt t ht
    exact S7PIDP_pathAt_cont (S7PIDP_cont H hn₀ hJ hm0 hm1 c c' hc hlt hc'G n v) t ht
  · -- (b) the norm bound (valid also for `c = c'`: then the path is `pathOf` of a bounded function)
    intro b hb
    have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0 (Nat.zero_le _))
    have hC1 : (1 : ℝ) ≤ max 1 Cb := le_max_left _ _
    have hnn : 0 ≤ max 1 Cb * b := mul_nonneg (zero_le_one.trans hC1) hb0
    have hpt : ∀ t ∈ Set.Icc (0 : ℝ) G, ‖if t ≤ c' then polyAt c c' n v t
        else Vprop Rb.D Rb.ρ m t c' (v (2 ^ n))‖ ≤ max 1 Cb * b := by
      intro t ht
      split_ifs with h
      · exact (S7PIDP_polyAt_norm c c' t hc hcc n v b hb0 hb).trans (le_mul_of_one_le_left hb0 hC1)
      · have htpos : 0 < t := lt_of_le_of_lt (hc.trans hcc) (not_le.1 h)
        have hV := (hU b₀ hb₀ c' c' t (hc.trans hcc) le_rfl (not_le.1 h).le ht.2).2.1 (v (2 ^ n))
        calc _ ≤ Cb * ‖v (2 ^ n)‖ := hV
          _ ≤ Cb * b := mul_le_mul_of_nonneg_left (hb _ le_rfl) hCb
          _ ≤ max 1 Cb * b := mul_le_mul_of_nonneg_right (le_max_right _ _) hb0
    unfold polyPath
    exact S7PIDP_norm_pathOf_le _ _ hnn hpt
  · -- (c) refinement
    intro B hB
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (pow_pos (by norm_num) _))
    rcases eq_or_lt_of_le hcc with heq | hlt
    · subst heq
      have hEq : polyPath Rb.D Rb.ρ m G c c (n + 1) v = polyPath Rb.D Rb.ρ m G c c n (fun i => v (2 * i)) := by
        unfold polyPath
        congr 1
        funext t
        dsimp only
        split_ifs with h
        · rw [S7PIDP_polyAt_degen, S7PIDP_polyAt_degen]
        · show Vprop Rb.D Rb.ρ m t c (v (2 ^ (n + 1))) = Vprop Rb.D Rb.ρ m t c (v (2 * 2 ^ n))
          rw [pow_succ']
      rw [hEq, sub_self, norm_zero]
      exact hB0
    · have hcont1 := S7PIDP_cont H hn₀ hJ hm0 hm1 c c' hc hlt hc'G (n + 1) v
      have hcont0 := S7PIDP_cont H hn₀ hJ hm0 hm1 c c' hc hlt hc'G n (fun i => v (2 * i))
      unfold polyPath
      rw [S7PIDP_pathOf_cont hcont1, S7PIDP_pathOf_cont hcont0]
      refine (ContinuousMap.norm_le _ hB0).2 ?_
      intro x
      show ‖(if x.1 ≤ c' then polyAt c c' (n + 1) v x.1
          else Vprop Rb.D Rb.ρ m x.1 c' (v (2 ^ (n + 1)))) -
        (if x.1 ≤ c' then polyAt c c' n (fun i => v (2 * i)) x.1
          else Vprop Rb.D Rb.ρ m x.1 c' (v (2 * 2 ^ n)))‖ ≤ B
      split_ifs with h
      · exact S7PIDP_polyAt_refine c c' hc hlt n v x.1 B hB0 hB
      · rw [show 2 * 2 ^ n = 2 ^ (n + 1) by ring, sub_self, norm_zero]
        exact hB0

end HRS.MC.E213J

end
