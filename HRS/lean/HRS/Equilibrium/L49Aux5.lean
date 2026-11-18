/-
# HRS.Equilibrium.L49Aux5 — Proposition 4.9, part 5: the abstract local estimate

`l49_local_abstract`: `∫_{cube} ρ_w H(λ γ) = (|S^{d-1}|/(2s)) ρ₀ λ² log(1/λ) + O(λ²)`
(`R:eq:compensated-integral`), the inner ball `|w| ≤ r_λ = λ^{1/s}`, the annulus
`r_λ < |w| ≤ δ` (model `ρ₀ λ² |w|^{-2s}/2`) and the exterior of the cube handled separately.
-/
import HRS.Equilibrium.L49Aux4

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace L49

open HRS.LocalDivAux

variable {d : ℕ}

theorem l49_measurable_taylorH : Measurable taylorH := by
  have : Continuous taylorH := by unfold taylorH; fun_prop
  exact this.measurable

set_option maxHeartbeats 3200000 in
theorem l49_local_abstract (hd : 2 ≤ d) {s : ℝ} (hs1 : 1 ≤ s) (hds : (d : ℝ) = 2 * s)
    {γ ρw : Euc d → ℝ} {ρ0 Lam L R δ Γ₀ lam rl : ℝ}
    (hγm : Measurable γ) (hρm : Measurable ρw)
    (hγ0 : ∀ w, 0 ≤ γ w)
    (hγu : ∀ w : Euc d, 0 < ‖w‖ → ‖w‖ ≤ δ → |γ w - ‖w‖ ^ (-s)| ≤ R) (hR : 0 ≤ R)
    (hρ : ∀ w, 0 ≤ ρw w ∧ ρw w ≤ Lam) (hρ0 : 0 ≤ ρ0 ∧ ρ0 ≤ Lam)
    (hρL : ∀ w : Euc d, ‖w‖ ≤ δ → |ρw w - ρ0| ≤ L * ‖w‖) (hL : 0 ≤ L)
    (hfar : ∀ w ∈ cube d, δ < ‖w‖ → γ w ≤ Γ₀) (hΓ0 : 0 ≤ Γ₀)
    (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4)
    (hrl0 : 0 < rl) (hrlδ : rl ≤ δ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hrls : rl ^ s = lam) :
    IntegrableOn (fun w => ρw w * taylorH (lam * γ w)) (cube d) ∧
    |(∫ w in cube d, ρw w * taylorH (lam * γ w)) -
        ballConst d / (2 * s) * ρ0 * lam ^ 2 * Real.log (1 / lam)| ≤
      (Lam * (1 + R) * ballConst d / s +
        (L * (1 + R ^ 2) + Lam * (4 * R ^ 3 + R + R ^ 2 / 2)) * ballConst d * δ +
        4 * Lam * ballConst d / s + Lam * Γ₀ ^ 2 / 2 + Lam * ballConst d * |Real.log δ| / 2) *
        lam ^ 2 := by
  have hd1 : 1 ≤ d := by omega
  have hs0 : 0 < s := by linarith
  have hLam : 0 ≤ Lam := hρ0.1.trans hρ0.2
  have hδ1 : δ ≤ 1 := by linarith
  set K2 : ℝ := L * (1 + R ^ 2) + Lam * (4 * R ^ 3 + R + R ^ 2 / 2) with hK2
  have hK2' : 0 ≤ K2 := by positivity
  set Bc : ℝ := ballConst d with hBc
  have hBc0 : 0 ≤ Bc := ballConst_nonneg
  -- functions
  set e : Euc d → ℝ := fun w => ρw w * taylorH (lam * γ w) with he
  set e1 : Euc d → ℝ := fun w => if ‖w‖ ≤ δ then e w else 0 with he1
  set e2 : Euc d → ℝ := fun w => if δ < ‖w‖ then e w else 0 with he2
  set Mf : Euc d → ℝ := fun w => ρ0 * (lam ^ 2 / 2) * l49_ind d rl δ (2 * s) w with hMf
  set b1 : Euc d → ℝ := fun w => Lam * (1 + R) * lam * l49_ind d 0 rl s w with hb1
  set b2 : Euc d → ℝ := fun w => K2 * lam ^ 2 * l49_ind d rl δ (2 * s - 1) w with hb2
  set b3 : Euc d → ℝ := fun w => 4 * Lam * lam ^ 3 * l49_ind d rl δ (3 * s) w with hb3
  set bnd : Euc d → ℝ := fun w => b1 w + b2 w + b3 w with hbnd
  have hem : Measurable e := hρm.mul (l49_measurable_taylorH.comp (measurable_const.mul hγm))
  have hnormm : Measurable fun w : Euc d => ‖w‖ := measurable_norm
  have he1m : Measurable e1 := Measurable.ite (measurableSet_le hnormm measurable_const) hem measurable_const
  have he2m : Measurable e2 := Measurable.ite (measurableSet_lt measurable_const hnormm) hem measurable_const
  have hMm : Measurable Mf := measurable_const.mul (l49_measurable_ind _ _ _)
  have hbndm : Measurable bnd :=
    (((measurable_const.mul (l49_measurable_ind _ _ _)).add
      (measurable_const.mul (l49_measurable_ind _ _ _))).add (measurable_const.mul (l49_measurable_ind _ _ _)))
  -- integrals of model functions
  obtain ⟨hi1, hv1⟩ := l49_int_ind1 hd1 hs0 hds hrl0
  obtain ⟨hi2, hv2⟩ := l49_int_ind2 hd1 hs0 hds hrl0 hrlδ
  obtain ⟨hi3, hv3⟩ := l49_int_ind3 hd1 hs0 hds hrl0 hrlδ
  obtain ⟨hi4, hv4⟩ := l49_int_ind4 hd1 hs0 hds hrl0 hrlδ
  have hMi : Integrable Mf := hi4.const_mul _
  have hb1i : Integrable b1 := hi1.const_mul _
  have hb2i : Integrable b2 := hi2.const_mul _
  have hb3i : Integrable b3 := hi3.const_mul _
  have hbndi : Integrable bnd := (hb1i.add hb2i).add hb3i
  -- nonnegativity of bnd
  have hbnd0 : ∀ w, 0 ≤ bnd w := by
    intro w
    simp only [hbnd, hb1, hb2, hb3]
    have := l49_ind_nonneg (d := d) 0 rl s le_rfl w
    have := l49_ind_nonneg (d := d) rl δ (2 * s - 1) hrl0.le w
    have := l49_ind_nonneg (d := d) rl δ (3 * s) hrl0.le w
    have h1 : 0 ≤ Lam * (1 + R) * lam := by positivity
    have h2 : 0 ≤ K2 * lam ^ 2 := by positivity
    have h3 : 0 ≤ 4 * Lam * lam ^ 3 := by positivity
    have := mul_nonneg h1 (l49_ind_nonneg (d := d) 0 rl s le_rfl w)
    have := mul_nonneg h2 (l49_ind_nonneg (d := d) rl δ (2 * s - 1) hrl0.le w)
    have := mul_nonneg h3 (l49_ind_nonneg (d := d) rl δ (3 * s) hrl0.le w)
    linarith
  -- pointwise bound
  have hpt : ∀ w : Euc d, w ≠ 0 → |e1 w - Mf w| ≤ bnd w := by
    intro w hw0
    have ht0 : 0 < ‖w‖ := norm_pos_iff.2 hw0
    by_cases h1 : ‖w‖ ≤ δ
    · have he1w : e1 w = e w := by simp only [he1]; rw [if_pos h1]
      rw [he1w]
      have ht1 : ‖w‖ ≤ 1 := by linarith
      by_cases h2 : ‖w‖ ≤ rl
      · have hM0 : Mf w = 0 := by
          simp only [hMf]
          rw [l49_ind_of_notMem (fun hm => absurd hm.1 (not_lt.2 h2))]; ring
        have hmem : ‖w‖ ∈ Ioc (0 : ℝ) rl := ⟨ht0, h2⟩
        have hb1w : b1 w = Lam * (1 + R) * lam * ‖w‖ ^ (-s) := by
          simp only [hb1]; rw [l49_ind_of_mem hmem]
        have hb2w : b2 w = 0 := by
          simp only [hb2]
          rw [l49_ind_of_notMem (fun hm => absurd hm.1 (not_lt.2 h2))]; ring
        have hb3w : b3 w = 0 := by
          simp only [hb3]
          rw [l49_ind_of_notMem (fun hm => absurd hm.1 (not_lt.2 h2))]; ring
        have hbw : bnd w = b1 w := by simp only [hbnd]; rw [hb2w, hb3w]; ring
        rw [hM0, hbw, hb1w, sub_zero]
        exact l49_pt_inner (rl := rl) hs1 ht0 ht1 hlam0 (hγ0 w) (hγu w ht0 h1) hR hLam (hρ w).1 (hρ w).2
      · push Not at h2
        have hmem : ‖w‖ ∈ Ioc rl δ := ⟨h2, h1⟩
        have hb1w : b1 w = 0 := by
          simp only [hb1]
          rw [l49_ind_of_notMem (fun hm => absurd hm.2 (not_le.2 h2))]; ring
        have hM : Mf w = ρ0 * (lam ^ 2 / 2) * ‖w‖ ^ (-(2 * s)) := by
          simp only [hMf]; rw [l49_ind_of_mem hmem]
        have hb2w : b2 w = K2 * lam ^ 2 * ‖w‖ ^ (-(2 * s - 1)) := by
          simp only [hb2]; rw [l49_ind_of_mem hmem]
        have hb3w : b3 w = 4 * Lam * lam ^ 3 * ‖w‖ ^ (-(3 * s)) := by
          simp only [hb3]; rw [l49_ind_of_mem hmem]
        have hbw : bnd w = b2 w + b3 w := by simp only [hbnd]; rw [hb1w]; ring
        rw [hM, hbw, hb2w, hb3w]
        exact l49_pt_outer hs1 ht0 ht1 hlam0 hlam1 hrl0 hrls h2 (hγ0 w) (hγu w ht0 h1) hR hL hLam
          (hρ w).1 (hρ w).2 hρ0.1 hρ0.2 (hρL w h1)
    · push Not at h1
      have he1w : e1 w = 0 := by simp only [he1]; rw [if_neg (not_le.2 h1)]
      have hM0 : Mf w = 0 := by
        simp only [hMf]; rw [l49_ind_supp h1]; ring
      rw [he1w, hM0, sub_zero, abs_zero]
      exact hbnd0 w
  have hae : ∀ᵐ w : Euc d ∂volume, ‖e1 w - Mf w‖ ≤ bnd w := by
    have : ∀ᵐ w : Euc d ∂volume, w ∉ ({0} : Set (Euc d)) := by
      haveI : Nonempty (Fin d) := ⟨⟨0, hd1⟩⟩
      haveI : Nontrivial (Euc d) := inferInstance
      exact (Set.countable_singleton (0 : Euc d)).ae_notMem _
    filter_upwards [this] with w hw
    rw [Real.norm_eq_abs]
    exact hpt w (by simpa using hw)
  have hdiffi : Integrable (fun w => e1 w - Mf w) :=
    Integrable.mono' hbndi (he1m.sub hMm).aestronglyMeasurable hae
  have he1i : Integrable e1 := by
    refine (hdiffi.add hMi).congr (Eventually.of_forall fun w => ?_)
    simp
  -- the exterior part
  have hB2 : ∀ w ∈ cube d, |e2 w| ≤ Lam * Γ₀ ^ 2 / 2 * lam ^ 2 := by
    intro w hw
    simp only [he2]
    split_ifs with h
    · have hg := hfar w hw h
      have hg0 := hγ0 w
      have hv0 : 0 ≤ lam * γ w := by positivity
      have hH0 := l49_H_nonneg (lam * γ w)
      have hHs := l49_H_le_sq hv0
      have hv : lam * γ w ≤ lam * Γ₀ := mul_le_mul_of_nonneg_left hg hlam0.le
      have hv2 : (lam * γ w) ^ 2 ≤ (lam * Γ₀) ^ 2 := pow_le_pow_left₀ hv0 hv 2
      simp only [he]
      rw [abs_of_nonneg (mul_nonneg (hρ w).1 hH0)]
      calc ρw w * taylorH (lam * γ w) ≤ Lam * ((lam * Γ₀) ^ 2 / 2) :=
            mul_le_mul (hρ w).2 (hHs.trans (by linarith)) hH0 hLam
        _ = _ := by ring
    · simp only [abs_zero]; positivity
  have he2I : IntegrableOn e2 (cube d) :=
    integrableOn_cube_bdd he2m hB2
  have he1I : IntegrableOn e1 (cube d) := he1i.integrableOn
  have hsplit : ∀ w, e w = e1 w + e2 w := by
    intro w
    simp only [he1, he2]
    by_cases h : ‖w‖ ≤ δ
    · rw [if_pos h, if_neg (not_lt.2 h)]; ring
    · rw [if_neg h, if_pos (not_le.1 h)]; ring
  have heI : IntegrableOn e (cube d) := by
    have := he1I.add he2I
    refine this.congr_fun (fun w _ => (hsplit w).symm) measurableSet_cube
  refine ⟨heI, ?_⟩
  -- the integral over the cube
  have hsupp1 : ∀ w, w ∉ cube d → e1 w = 0 := by
    intro w hw
    simp only [he1]
    rw [if_neg]
    intro h
    exact hw (cube_of_norm_le hδ4 h)
  have hcube1 : ∫ w in cube d, e1 w = ∫ w, e1 w :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hsupp1
  have hI : ∫ w in cube d, e w = (∫ w, e1 w) + ∫ w in cube d, e2 w := by
    rw [← hcube1, ← integral_add he1I he2I]
    exact setIntegral_congr_fun measurableSet_cube fun w _ => hsplit w
  have hfarI : |∫ w in cube d, e2 w| ≤ Lam * Γ₀ ^ 2 / 2 * lam ^ 2 := by
    have : IsFiniteMeasure ((volume : Measure (Euc d)).restrict (cube d)) :=
      ⟨by rw [Measure.restrict_apply_univ, volume_cube]; exact ENNReal.one_lt_top⟩
    have h := norm_integral_le_of_norm_le_const
      (μ := (volume : Measure (Euc d)).restrict (cube d)) (f := e2)
      (C := Lam * Γ₀ ^ 2 / 2 * lam ^ 2) ?_
    · have h1 : ((volume : Measure (Euc d)).restrict (cube d)).real univ = 1 := by
        simp [Measure.real, Measure.restrict_apply_univ, volume_cube]
      rw [h1, mul_one, Real.norm_eq_abs] at h
      exact h
    · refine (ae_restrict_iff' measurableSet_cube).2 (Eventually.of_forall fun w hw => ?_)
      rw [Real.norm_eq_abs]; exact hB2 w hw
  have hnear : |(∫ w, e1 w) - ∫ w, Mf w| ≤ ∫ w, bnd w := by
    rw [← integral_sub he1i hMi, ← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le hbndi hae
  -- values
  have hMval : ∫ w, Mf w = ρ0 * (lam ^ 2 / 2) * (Bc * (Real.log δ - Real.log rl)) := by
    simp only [hMf]; rw [integral_const_mul, hv4]
  have hlogrl : Real.log rl = Real.log lam / s := by
    have : Real.log (rl ^ s) = s * Real.log rl := Real.log_rpow hrl0 s
    rw [hrls] at this
    field_simp
    linarith
  have hbval : ∫ w, bnd w ≤ Lam * (1 + R) * Bc / s * lam ^ 2 + K2 * Bc * δ * lam ^ 2 +
      4 * Lam * Bc / s * lam ^ 2 := by
    have e1' : ∫ w, b1 w = Lam * (1 + R) * lam * (Bc * (rl ^ s / s)) := by
      simp only [hb1]; rw [integral_const_mul, hv1]
    have e2' : ∫ w, b2 w = K2 * lam ^ 2 * (Bc * (δ - rl)) := by
      simp only [hb2]; rw [integral_const_mul, hv2]
    have e3' : ∫ w, b3 w ≤ 4 * Lam * lam ^ 3 * (Bc * (rl ^ (-s) / s)) := by
      simp only [hb3]; rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hv3 (by positivity)
    have hrs : rl ^ (-s) = lam⁻¹ := by rw [Real.rpow_neg hrl0.le, hrls]
    have : ∫ w, bnd w = (∫ w, b1 w) + (∫ w, b2 w) + ∫ w, b3 w := by
      have h12 : ∫ w, (b1 w + b2 w) = (∫ w, b1 w) + ∫ w, b2 w := integral_add hb1i hb2i
      have h123 : ∫ w, (b1 w + b2 w + b3 w) = (∫ w, (b1 w + b2 w)) + ∫ w, b3 w :=
        integral_add (hb1i.add hb2i) hb3i
      simp only [hbnd]; rw [h123, h12]
    rw [this, e1', e2']
    rw [hrls] at *
    have h3 : 4 * Lam * lam ^ 3 * (Bc * (lam⁻¹ / s)) = 4 * Lam * Bc / s * lam ^ 2 := by
      field_simp
    have h2 : K2 * lam ^ 2 * (Bc * (δ - rl)) ≤ K2 * Bc * δ * lam ^ 2 := by
      have : K2 * lam ^ 2 * (Bc * (δ - rl)) = K2 * Bc * lam ^ 2 * (δ - rl) := by ring
      rw [this]
      have : δ - rl ≤ δ := by linarith
      have h0 : 0 ≤ K2 * Bc * lam ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this h0]
    have h1 : Lam * (1 + R) * lam * (Bc * (lam / s)) = Lam * (1 + R) * Bc / s * lam ^ 2 := by
      field_simp
    rw [hrs] at e3'
    nlinarith [e3', h3, h2, h1]
  -- assemble
  have hmain : ρ0 * (lam ^ 2 / 2) * (Bc * (Real.log δ - Real.log rl)) =
      Bc / (2 * s) * ρ0 * lam ^ 2 * Real.log (1 / lam) + ρ0 * lam ^ 2 * Bc * Real.log δ / 2 := by
    rw [hlogrl, one_div, Real.log_inv]
    field_simp
    ring
  rw [hI]
  have e : ((∫ w, e1 w) + ∫ w in cube d, e2 w) - Bc / (2 * s) * ρ0 * lam ^ 2 * Real.log (1 / lam) =
      ((∫ w, e1 w) - ∫ w, Mf w) + (∫ w in cube d, e2 w) + ρ0 * lam ^ 2 * Bc * Real.log δ / 2 := by
    rw [hMval, hmain]; ring
  rw [e]
  have hlast : |ρ0 * lam ^ 2 * Bc * Real.log δ / 2| ≤ Lam * Bc * |Real.log δ| / 2 * lam ^ 2 := by
    rw [abs_div, abs_mul, abs_mul, abs_mul, abs_of_nonneg hρ0.1, abs_of_nonneg (sq_nonneg lam),
      abs_of_nonneg hBc0, abs_two]
    have : ρ0 * lam ^ 2 * Bc * |Real.log δ| ≤ Lam * lam ^ 2 * Bc * |Real.log δ| := by gcongr; exact hρ0.2
    linarith
  calc _ ≤ |(∫ w, e1 w) - ∫ w, Mf w| + |∫ w in cube d, e2 w| + |ρ0 * lam ^ 2 * Bc * Real.log δ / 2| := by
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by nlinarith [hnear, hbval, hfarI, hlast]

end L49

end HRS

end
