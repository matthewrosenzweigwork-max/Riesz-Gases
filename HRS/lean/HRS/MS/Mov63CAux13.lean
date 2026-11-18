import HRS.MS.Mov63CAux12

/-!
# S6.3, uniqueness chain (N3b, part 8): the `S_0`-Duhamel formula for the difference of two solutions

Namespace `HRS.MS.Mov63`, helper prefix `mnc_`.  See `Mov63CAux1` for the plan.
`mnc_duhamel`: for two members of the class with the same initial datum and `t ∈ [0,T]`,
`w_t = ∫_0^t e^{-(t-x)S_0} G_x dx` in `Σ^m` (Bochner integral in `OscSpace d m`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

section Duhamel

variable (H : Mov2dTh d s β q ρ) {m : ℕ} (hm : (d : ℝ) / 2 + 3 < m) {P1 P2 : ℝ → Euc d → ℝ}

lemma mnc_w_cont {r1 r2 c1 c2 : ℝ} {f0 : Euc d → ℝ} (hcls1 : MovInSmallClass d s q β ρ m r1 c1 f0 P1)
    (hcls2 : MovInSmallClass d s q β ρ m r2 c2 f0 P2) (T : ℝ) :
    ContinuousOn (mnc_w ρ P1 P2 m) (Set.Icc 0 T) :=
  (hcls1.cont.mono Set.Icc_subset_Ici_self).sub (hcls2.cont.mono Set.Icc_subset_Ici_self)

lemma mnc_G_cont {r1 r2 c1 c2 : ℝ} {f0 : Euc d → ℝ} (hcls1 : MovInSmallClass d s q β ρ m r1 c1 f0 P1)
    (hcls2 : MovInSmallClass d s q β ρ m r2 c2 f0 P2) (T : ℝ) :
    ContinuousOn (mnc_G H hm P1 P2) (Set.Icc 0 T) := by
  have hu1 : ContinuousOn (mnc_u ρ P1 m) (Set.Icc 0 T) := hcls1.cont.mono Set.Icc_subset_Ici_self
  have hu2 : ContinuousOn (mnc_u ρ P2 m) (Set.Icc 0 T) := hcls2.cont.mono Set.Icc_subset_Ici_self
  have hw := mnc_w_cont hcls1 hcls2 T
  unfold mnc_G
  refine ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_
  · exact ((mov2d_R d s β q ρ (m : ℝ)).continuous.comp_continuousOn hw).neg
  · have hB : ContinuousOn (fun x => mov_B_ext H hm (mnc_u ρ P1 m x)) (Set.Icc 0 T) :=
      (mov_B_ext H hm).continuous.comp_continuousOn hu1
    exact hB.clm_apply hw
  · have hB : ContinuousOn (fun x => mov_B_ext H hm (mnc_w ρ P1 P2 m x)) (Set.Icc 0 T) :=
      (mov_B_ext H hm).continuous.comp_continuousOn hw
    exact hB.clm_apply hu2

lemma mnc_ker {T : ℝ} (hT : 0 < T) :
    ∃ Kc : ℝ, Mov2cKer (fun τ => mov2d_Sm (d := d) β q (sub_le_self (m : ℝ) (mov2d_a_bounds d H.hd H.hsd).1) τ)
      T Kc (1 - movA d s / 2) := by
  have hyp := mov2d_hyp' H hT
  have ha0 := (mov2d_a_bounds d H.hd H.hsd).1
  obtain ⟨C, hC0, hC⟩ := hyp.bound (sub_le_self (m : ℝ) ha0)
  refine ⟨C, ⟨hC0, ?_, ?_⟩⟩
  · intro y
    exact (mov2c_Sm_cont hyp (sub_le_self (m : ℝ) ha0) y).mono (fun τ hτ => hτ.1)
  · intro τ hτ
    have e : -(((m : ℝ) - ((m : ℝ) - movA d s)) / 2) = 1 - movA d s / 2 - 1 := by ring
    have := hC τ hτ
    rw [e] at this
    exact this

/-- **The `S_0`-Duhamel formula** for the difference of two solutions. -/
theorem mnc_duhamel (hβ : 0 < β) (hq : 0 < q) {r1 r2 c1 c2 : ℝ} {f0 : Euc d → ℝ}
    (hcls1 : MovInSmallClass d s q β ρ m r1 c1 f0 P1) (hcls2 : MovInSmallClass d s q β ρ m r2 c2 f0 P2)
    {T : ℝ} (hT : 0 < T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    mnc_w ρ P1 P2 m t = ∫ x in (0 : ℝ)..t,
      mov2d_Sm (d := d) β q (sub_le_self (m : ℝ) (mov2d_a_bounds d H.hd H.hsd).1) (t - x) (mnc_G H hm P1 P2 x) := by
  have ha := mov2d_a_bounds d H.hd H.hsd
  obtain ⟨Kc, hK⟩ := mnc_ker (m := m) H hT
  have hθ : 0 < 1 - movA d s / 2 := by linarith [ha.2]
  have hθ1 : 1 - movA d s / 2 ≤ 1 := by linarith [ha.1]
  have hGc := mnc_G_cont H hm hcls1 hcls2 T
  have hint := mov2c_vol_int (K := fun τ => mov2d_Sm (d := d) β q (sub_le_self (m : ℝ) ha.1) τ) hK hθ hθ1
    (y := mnc_G H hm P1 P2) hGc ht
  have hma : 0 ≤ (m : ℝ) - movA d s := mnb_sub_a_nonneg H hm
  refine mnc_ext_of_ip hβ hq (fun α => ?_)
  -- the pairing of the right-hand side
  have hR : mnc_ipL (mnc_hα d β q α) (Nat.cast_nonneg m) (∫ x in (0 : ℝ)..t,
      mov2d_Sm (d := d) β q (sub_le_self (m : ℝ) ha.1) (t - x) (mnc_G H hm P1 P2 x)) =
      ∫ x in Set.Icc (0 : ℝ) t, Real.exp (-(q * (α.degree : ℝ)) * (t - x)) *
        mnc_ipL (mnc_hα d β q α) hma (mnc_G H hm P1 P2 x) := by
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ hint, intervalIntegral.integral_of_le ht.1,
      integral_Icc_eq_integral_Ioc, integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo (fun x hx => ?_)
    rw [mnc_ipL_Sm hβ hq ha.1 hma α (by linarith [hx.2])]
    congr 2
    ring
  rw [hR]
  -- the coefficient formula
  have hc : ContinuousOn (fun x => mnc_ipL (mnc_hα d β q α) (Nat.cast_nonneg m) (mnc_w ρ P1 P2 m x)) (Set.Icc 0 T) :=
    (mnc_ipL _ _).continuous.comp_continuousOn (mnc_w_cont hcls1 hcls2 T)
  have hg : ContinuousOn (fun x => mnc_ipL (mnc_hα d β q α) hma (mnc_G H hm P1 P2 x)) (Set.Icc 0 T) :=
    (mnc_ipL _ _).continuous.comp_continuousOn hGc
  have := mnc_ode_formula (lam := q * (α.degree : ℝ)) hT.le hc hg (fun t' ht' => mnc_diff_coeff H hm hβ hq hcls1 hcls2 α ht'.1)
    t ht
  exact this

end Duhamel

end HRS.MS.Mov63
