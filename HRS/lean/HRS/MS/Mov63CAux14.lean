import HRS.MS.Mov63CAux13

/-!
# S6.3, uniqueness chain (N4): singular Gronwall and the uniqueness theorem

Namespace `HRS.MS.Mov63`, helper prefix `mnc_`.  See `Mov63CAux1` for the plan.
`mnc_sing_gronwall`: an abstract Mittag-Leffler iteration (same pattern as `mov2c_vol_unique`) for a continuous
nonnegative `f` with `f(t) ≤ ∫ ... (t-s)^{θ-1} f(s)` (in the iterated form); `mov_nl_unique`: the uniqueness conjunct
of `MovNonlinearConclusion` at every radius and every exponent `c₀` (no smallness, no decay used).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

/-- Abstract singular Gronwall (Mittag-Leffler iteration). -/
theorem mnc_sing_gronwall {T θ Kc : ℝ} (hθ : 0 < θ) (hT : 0 ≤ T) (hKc : 0 ≤ Kc) {f : ℝ → ℝ}
    (hf0 : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ f t) (hfb : ∃ N : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, f t ≤ N)
    (hstep : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (n : ℕ) (A : ℝ), 0 ≤ A →
      (∀ s ∈ Set.Icc (0 : ℝ) T, f s ≤ A * s ^ ((n : ℝ) * θ) / Real.Gamma (1 + n * θ)) →
      f t ≤ A * Kc * Real.Gamma θ * t ^ (((n : ℝ) + 1) * θ) / Real.Gamma (1 + ((n : ℝ) + 1) * θ)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, f t = 0 := by
  obtain ⟨N, hN⟩ := hfb
  have hN0 : 0 ≤ N := (hf0 0 ⟨le_rfl, hT⟩).trans (hN 0 ⟨le_rfl, hT⟩)
  set c : ℝ := Kc * Real.Gamma θ with hc
  have hc0 : 0 ≤ c := mul_nonneg hKc (Real.Gamma_pos_of_pos hθ).le
  have key : ∀ n : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      f t ≤ (N * c ^ n) * t ^ ((n : ℝ) * θ) / Real.Gamma (1 + n * θ) := by
    intro n
    induction n with
    | zero => intro t ht; simpa using hN t ht
    | succ n ih =>
      intro t ht
      have := hstep t ht n (N * c ^ n) (mul_nonneg hN0 (pow_nonneg hc0 _)) ih
      refine this.trans (le_of_eq ?_)
      push_cast
      rw [hc]; ring
  intro t ht
  have hsum := mov2c_gamma_summable hθ (x := c * t ^ θ) (mul_nonneg hc0 (Real.rpow_nonneg ht.1 _))
  have hlim := (hsum.tendsto_atTop_zero).const_mul N
  have hle : ∀ n : ℕ, f t ≤ N * ((c * t ^ θ) ^ n / Real.Gamma (1 + n * θ)) := by
    intro n
    refine (key n t ht).trans (le_of_eq ?_)
    rw [mov2c_pow_rpow ht.1, mul_pow]; ring
  have := ge_of_tendsto' hlim hle
  simp only [mul_zero] at this
  exact le_antisymm this (hf0 t ht)

section Unique

variable (H : Mov2dTh d s β q ρ) {m : ℕ} (hm : (d : ℝ) / 2 + 3 < m) {P1 P2 : ℝ → Euc d → ℝ}

include H hm in
/-- **N4.** `w = 0` on `[0,T]`. -/
theorem mnc_w_zero (hβ : 0 < β) (hq : 0 < q) {r1 r2 c1 c2 : ℝ} {f0 : Euc d → ℝ}
    (hcls1 : MovInSmallClass d s q β ρ m r1 c1 f0 P1) (hcls2 : MovInSmallClass d s q β ρ m r2 c2 f0 P2)
    {T : ℝ} (hT : 0 < T) : ∀ t ∈ Set.Icc (0 : ℝ) T, mnc_w ρ P1 P2 m t = 0 := by
  have ha := mov2d_a_bounds d H.hd H.hsd
  obtain ⟨Kc, hK⟩ := mnc_ker (m := m) H hT
  have hθ : 0 < 1 - movA d s / 2 := by linarith [ha.2]
  -- bounds
  have hu1 : ContinuousOn (mnc_u ρ P1 m) (Set.Icc 0 T) := hcls1.cont.mono Set.Icc_subset_Ici_self
  have hu2 : ContinuousOn (mnc_u ρ P2 m) (Set.Icc 0 T) := hcls2.cont.mono Set.Icc_subset_Ici_self
  have hw := mnc_w_cont hcls1 hcls2 T
  obtain ⟨M1, hM1⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hu1
  obtain ⟨M2, hM2⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hu2
  obtain ⟨N, hN⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hw
  have hM10 : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0 ⟨le_rfl, hT.le⟩)
  have hM20 : 0 ≤ M2 := (norm_nonneg _).trans (hM2 0 ⟨le_rfl, hT.le⟩)
  obtain ⟨KB, hKB0, hKB⟩ := mov_B_ext_bound H hm
  set Rn : ℝ := ‖mov2d_R d s β q ρ (m : ℝ)‖ with hRn
  set L : ℝ := Rn + KB * (M1 + M2) with hL
  have hL0 : 0 ≤ L := by positivity
  have hG : ∀ x ∈ Set.Icc (0 : ℝ) T, ‖mnc_G H hm P1 P2 x‖ ≤ L * ‖mnc_w ρ P1 P2 m x‖ := by
    intro x hx
    unfold mnc_G
    have b1 : ‖-(mov2d_R d s β q ρ (m : ℝ) (mnc_w ρ P1 P2 m x))‖ ≤ Rn * ‖mnc_w ρ P1 P2 m x‖ := by
      rw [norm_neg]; exact (mov2d_R d s β q ρ (m : ℝ)).le_opNorm _
    have b2 : ‖mov_B_ext H hm (mnc_u ρ P1 m x) (mnc_w ρ P1 P2 m x)‖ ≤ KB * M1 * ‖mnc_w ρ P1 P2 m x‖ :=
      (hKB _ _).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hM1 x hx) hKB0) (norm_nonneg _))
    have b3 : ‖mov_B_ext H hm (mnc_w ρ P1 P2 m x) (mnc_u ρ P2 m x)‖ ≤ KB * M2 * ‖mnc_w ρ P1 P2 m x‖ := by
      refine (hKB _ _).trans ?_
      calc KB * ‖mnc_w ρ P1 P2 m x‖ * ‖mnc_u ρ P2 m x‖ ≤ KB * ‖mnc_w ρ P1 P2 m x‖ * M2 :=
            mul_le_mul_of_nonneg_left (hM2 x hx) (mul_nonneg hKB0 (norm_nonneg _))
        _ = KB * M2 * ‖mnc_w ρ P1 P2 m x‖ := by ring
    calc _ ≤ ‖-(mov2d_R d s β q ρ (m : ℝ) (mnc_w ρ P1 P2 m x))‖ +
          ‖mov_B_ext H hm (mnc_u ρ P1 m x) (mnc_w ρ P1 P2 m x)‖ +
          ‖mov_B_ext H hm (mnc_w ρ P1 P2 m x) (mnc_u ρ P2 m x)‖ := norm_add₃_le
      _ ≤ _ := by
          rw [hL]
          nlinarith [b1, b2, b3]
  refine mnc_sing_gronwall (T := T) (θ := 1 - movA d s / 2) (Kc := Kc * L) hθ hT.le
    (mul_nonneg hK.Kc_nonneg hL0) (f := fun t => ‖mnc_w ρ P1 P2 m t‖) (fun t _ => norm_nonneg _)
    ⟨N, hN⟩ ?_ |> fun h t ht => norm_eq_zero.1 (h t ht)
  intro t ht n A hA hIH
  have hint : IntervalIntegrable (fun x => mov2d_Sm (d := d) β q (sub_le_self (m : ℝ) ha.1) (t - x) (mnc_G H hm P1 P2 x))
      volume 0 t := by
    have := mov2c_vol_int (K := fun τ => mov2d_Sm (d := d) β q (sub_le_self (m : ℝ) ha.1) τ) hK hθ
      (by linarith [ha.1]) (y := mnc_G H hm P1 P2) (mnc_G_cont H hm hcls1 hcls2 T) ht
    exact this
  rw [mnc_duhamel H hm hβ hq hcls1 hcls2 hT ht]
  have := mov2c_integral_norm_le (v := fun x => mov2d_Sm (d := d) β q (sub_le_self (m : ℝ) ha.1) (t - x)
      (mnc_G H hm P1 P2 x)) (t := t) (Kc := Kc * L) (A := A) (θ := 1 - movA d s / 2) hθ
    (mul_nonneg hK.Kc_nonneg hL0) hA n ht.1 (by
      intro x hx
      have hxT : x ∈ Set.Icc (0 : ℝ) T := ⟨hx.1.le, hx.2.le.trans ht.2⟩
      have hτ : t - x ∈ Set.Ioc (0 : ℝ) T := ⟨by linarith [hx.2], by linarith [hx.1, ht.2]⟩
      calc ‖mov2d_Sm (d := d) β q (sub_le_self (m : ℝ) ha.1) (t - x) (mnc_G H hm P1 P2 x)‖
          ≤ ‖(mov2d_Sm (d := d) β q (sub_le_self (m : ℝ) ha.1) (t - x) :
              OscSpace d ((m : ℝ) - movA d s) →L[ℝ] OscSpace d (m : ℝ))‖ * ‖mnc_G H hm P1 P2 x‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ (Kc * (t - x) ^ (1 - movA d s / 2 - 1)) * (L * ‖mnc_w ρ P1 P2 m x‖) :=
            mul_le_mul (hK.bound _ hτ) (hG x hxT) (norm_nonneg _)
              (mul_nonneg hK.Kc_nonneg (Real.rpow_nonneg (by linarith [hx.2]) _))
        _ ≤ (Kc * (t - x) ^ (1 - movA d s / 2 - 1)) * (L * (A * x ^ ((n : ℝ) * (1 - movA d s / 2)) /
              Real.Gamma (1 + n * (1 - movA d s / 2)))) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hIH x hxT) hL0)
              (mul_nonneg hK.Kc_nonneg (Real.rpow_nonneg (by linarith [hx.2]) _))
        _ = (Kc * L) * (t - x) ^ (1 - movA d s / 2 - 1) *
              (A * x ^ ((n : ℝ) * (1 - movA d s / 2)) / Real.Gamma (1 + n * (1 - movA d s / 2))) := by ring)
  refine this.trans (le_of_eq ?_)
  ring

end Unique

end HRS.MS.Mov63
