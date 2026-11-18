import HRS.Commutator.Whole.XNRSAux29

/-!
# Packet X-NRS, part 30: convergence of `𝒞(v, a_n) → 𝒞(v, a)`
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

lemma xBil_diff (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {v : Euc d → Euc d} {L : ℝ}
    (hL0 : 0 ≤ L) (hL : XLip v L) {a e : Euc d → ℝ} {φa φe : 𝓢(Euc d, ℂ)}
    (ha : ∀ x, φa x = (a x : ℂ)) (he : ∀ x, φe x = (e x : ℂ)) :
    xBil s v (fun x => a x - e x) (fun x => a x - e x) - xBil s v a a =
      -xBil s v e a - xBil s v a e + xBil s v e e := by
  have hae : ∀ x, (φa - φe) x = ((a x - e x : ℝ) : ℂ) := fun x => by
    rw [sub_apply, ha, he]; push_cast; ring
  have i_aa := xBil_int hd hs0 hsd hL0 hL ha ha
  have i_ea := xBil_int hd hs0 hsd hL0 hL he ha
  have i_ae := xBil_int hd hs0 hsd hL0 hL ha he
  have i_ee := xBil_int hd hs0 hsd hL0 hL he he
  have i_mm := xBil_int hd hs0 hsd hL0 hL hae hae
  unfold xBil at *
  rw [← integral_sub i_mm i_aa]
  have e1 : ∀ p : Euc d × Euc d,
      commKer (kernGrad s) v p.1 p.2 * ((a p.1 - e p.1) * (a p.2 - e p.2)) -
        commKer (kernGrad s) v p.1 p.2 * (a p.1 * a p.2) =
      (-(commKer (kernGrad s) v p.1 p.2 * (e p.1 * a p.2)) -
        commKer (kernGrad s) v p.1 p.2 * (a p.1 * e p.2)) +
        commKer (kernGrad s) v p.1 p.2 * (e p.1 * e p.2) := by
    intro p; ring
  rw [show (∫ p : Euc d × Euc d, (commKer (kernGrad s) v p.1 p.2 * ((a p.1 - e p.1) * (a p.2 - e p.2)) -
        commKer (kernGrad s) v p.1 p.2 * (a p.1 * a p.2)) ∂(volume.prod volume)) =
      ∫ p : Euc d × Euc d, ((-(commKer (kernGrad s) v p.1 p.2 * (e p.1 * a p.2)) -
        commKer (kernGrad s) v p.1 p.2 * (a p.1 * e p.2)) +
        commKer (kernGrad s) v p.1 p.2 * (e p.1 * e p.2)) ∂(volume.prod volume) from
    integral_congr_ae (Eventually.of_forall e1)]
  have j1 : Integrable (fun p : Euc d × Euc d =>
      -(commKer (kernGrad s) v p.1 p.2 * (e p.1 * a p.2))) (volume.prod volume) := i_ea.neg
  have j2 : Integrable (fun p : Euc d × Euc d =>
      -(commKer (kernGrad s) v p.1 p.2 * (e p.1 * a p.2)) -
        commKer (kernGrad s) v p.1 p.2 * (a p.1 * e p.2)) (volume.prod volume) := j1.sub i_ae
  rw [integral_add j2 i_ee, integral_sub j1 i_ae, integral_neg]

lemma xdiff_bound (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {v : Euc d → Euc d} {L : ℝ}
    (hL0 : 0 ≤ L) (hL : XLip v L) {a : Euc d → ℝ} {φ : 𝓢(Euc d, ℂ)} (ha : ∀ x, φ x = (a x : ℂ))
    {n : ℝ} (hn0 : 0 < n) {R : ℝ} (hR : 0 < R) :
    |CcommFun (kernGrad s) v (xan a n) - CcommFun (kernGrad s) v a| ≤
      L * (2 * (xNR d s R * (∫ ξ, (1 - xσ n ξ) * ‖𝓕 φ ξ‖) * (∫ y, |a y|) +
          R ^ (-s) * (∫ y, |a y - xan a n y|) * (∫ y, |a y|)) +
        (xNR d s R * (∫ ξ, (1 - xσ n ξ) * ‖𝓕 φ ξ‖) * (∫ y, |a y - xan a n y|) +
          R ^ (-s) * (∫ y, |a y - xan a n y|) * (∫ y, |a y - xan a n y|))) := by
  set om : ℝ := ∫ ξ, (1 - xσ n ξ) * ‖𝓕 φ ξ‖ with hom
  set e : Euc d → ℝ := fun y => a y - xan a n y with he
  have hφn : ∀ x, xφn φ n hn0 x = ((xan a n x : ℝ) : ℂ) := xφn_real ha n hn0
  have hφe : ∀ x, (φ - xφn φ n hn0) x = ((e x : ℝ) : ℂ) := fun x => by
    rw [sub_apply, hφn, ha]; simp only [he]; push_cast; ring
  have hCn : CcommFun (kernGrad s) v (xan a n) = xBil s v (xan a n) (xan a n) :=
    xCcomm_eq hd hs0 hsd hL0 hL hφn
  have hCa : CcommFun (kernGrad s) v a = xBil s v a a := xCcomm_eq hd hs0 hsd hL0 hL ha
  have hxan : (xan a n) = fun x => a x - e x := by funext x; simp [he]
  have hCn' : CcommFun (kernGrad s) v (xan a n) =
      xBil s v (fun x => a x - e x) (fun x => a x - e x) := by
    rw [hCn, hxan]
  have hdiff := xBil_diff hd hs0 hsd hL0 hL ha hφe
  rw [hCn', hCa, hdiff]
  have hMe : ∀ x, |e x| ≤ om := fun x => xsup_bound ha hn0 x
  have b1 : |xBil s v e a| ≤ L * xIa s e a := xBil_abs_le hd hs0 hsd hL0 hL hφe ha
  have b2 : |xBil s v a e| ≤ L * xIa s a e := xBil_abs_le hd hs0 hsd hL0 hL ha hφe
  have b3 : |xBil s v e e| ≤ L * xIa s e e := xBil_abs_le hd hs0 hsd hL0 hL hφe hφe
  have c1 : xIa s e a ≤ xNR d s R * om * (∫ y, |a y|) + R ^ (-s) * (∫ y, |e y|) * ∫ y, |a y| :=
    xIa_bound hd hs0 hsd hφe ha hR hMe
  have c3 : xIa s e e ≤ xNR d s R * om * (∫ y, |e y|) + R ^ (-s) * (∫ y, |e y|) * ∫ y, |e y| :=
    xIa_bound hd hs0 hsd hφe hφe hR hMe
  have c2 : xIa s a e = xIa s e a := xIa_symm s a e
  rw [c2] at b2
  calc |-xBil s v e a - xBil s v a e + xBil s v e e|
      ≤ |xBil s v e a| + |xBil s v a e| + |xBil s v e e| := by
        calc _ ≤ |-xBil s v e a - xBil s v a e| + |xBil s v e e| := abs_add_le _ _
          _ ≤ (|-xBil s v e a| + |xBil s v a e|) + |xBil s v e e| := by
              gcongr; exact abs_sub _ _
          _ = _ := by rw [abs_neg]
    _ ≤ L * xIa s e a + L * xIa s e a + L * xIa s e e := by linarith
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left c1 hL0
        have := mul_le_mul_of_nonneg_left c3 hL0
        nlinarith

theorem xCcomm_tendsto (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2)
    {v : Euc d → Euc d} {L : ℝ} (hL0 : 0 ≤ L) (hL : XLip v L) {a : Euc d → ℝ}
    {φ : 𝓢(Euc d, ℂ)} (ha : ∀ x, φ x = (a x : ℂ)) (hmass : s = 0 → ∫ x, a x = 0) :
    Tendsto (fun n : ℝ => CcommFun (kernGrad s) v (xan a n)) atTop
      (nhds (CcommFun (kernGrad s) v a)) := by
  have hd1 : 1 ≤ d := by omega
  have hsd' : s < d := by linarith
  obtain ⟨C0, C1, hC0, hC1, hE⟩ := xe_L1 ha
  have hom : Tendsto (fun n : ℝ => ∫ ξ, (1 - xσ n ξ) * ‖𝓕 φ ξ‖) atTop (nhds 0) := tendsto_xsup hd1 φ
  set A : ℝ := ∫ y, |a y| with hA
  have hA0 : 0 ≤ A := integral_nonneg fun _ => abs_nonneg _
  have hom0 : ∀ n : ℝ, 0 ≤ ∫ ξ, (1 - xσ n ξ) * ‖𝓕 φ ξ‖ := fun n =>
    integral_nonneg fun ξ => mul_nonneg (sub_nonneg.2 (xcut_le_one n n ξ)) (norm_nonneg _)
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- the master bound
  have master : ∀ n : ℝ, 2 ≤ n → ∀ R : ℝ, 0 < R →
      dist (CcommFun (kernGrad s) v (xan a n)) (CcommFun (kernGrad s) v a) ≤
        L * xNR d s R * (∫ ξ, (1 - xσ n ξ) * ‖𝓕 φ ξ‖) * (2 * A + C0) +
          L * R ^ (-s) * (2 * A * (∫ y, |a y - xan a n y|) + (∫ y, |a y - xan a n y|) ^ 2) := by
    intro n hn R hR
    have hn0 : 0 < n := by linarith
    rw [Real.dist_eq]
    refine (xdiff_bound hd1 hs0 hsd' hL0 hL ha hn0 hR).trans ?_
    obtain ⟨_, hEb, _⟩ := hE n hn
    set E := ∫ y, |a y - xan a n y| with hEdef
    set om := ∫ ξ, (1 - xσ n ξ) * ‖𝓕 φ ξ‖ with homdef
    have hE0 : 0 ≤ E := integral_nonneg fun _ => abs_nonneg _
    have hN0 := xNR_nonneg (d := d) s R
    have hRs : 0 ≤ R ^ (-s) := Real.rpow_nonneg hR.le _
    have hom0' := hom0 n
    have : xNR d s R * om * E ≤ xNR d s R * om * C0 :=
      mul_le_mul_of_nonneg_left hEb (mul_nonneg hN0 hom0')
    nlinarith [mul_nonneg hL0 (mul_nonneg hN0 hom0'), mul_nonneg hL0 hRs,
      mul_nonneg (mul_nonneg hL0 hN0) hom0', mul_nonneg hA0 hE0]
  rcases hs0.eq_or_lt with hs | hs
  · -- `s = 0`
    subst hs
    have hm := hmass rfl
    have hbd : ∀ n : ℝ, 2 ≤ n → ∫ y, |a y - xan a n y| ≤ C1 * n⁻¹ := fun n hn => (hE n hn).2.2 hm
    have hlim : Tendsto (fun n : ℝ => L * xNR d 0 1 * (∫ ξ, (1 - xσ n ξ) * ‖𝓕 φ ξ‖) * (2 * A + C0) +
        L * 1 ^ (-(0 : ℝ)) * (2 * A * (C1 * n⁻¹) + (C1 * n⁻¹) ^ 2)) atTop (nhds 0) := by
      have h1 : Tendsto (fun n : ℝ => n⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
      have h2 := ((hom.const_mul (L * xNR d 0 1)).mul_const (2 * A + C0))
      have h3 := ((h1.const_mul C1).const_mul (2 * A)).add (((h1.const_mul C1).pow 2))
      have := h2.add (h3.const_mul (L * 1 ^ (-(0 : ℝ))))
      simpa using this
    have := (Metric.tendsto_nhds.1 hlim) ε hε
    filter_upwards [this, eventually_ge_atTop (2 : ℝ)] with n hn hn2
    rw [Real.dist_eq, sub_zero] at hn
    refine lt_of_le_of_lt ((master n hn2 1 one_pos).trans ?_) (lt_of_le_of_lt (le_abs_self _) hn)
    have hE0 : 0 ≤ ∫ y, |a y - xan a n y| := integral_nonneg fun _ => abs_nonneg _
    have hb := hbd n hn2
    have : 0 ≤ L * 1 ^ (-(0 : ℝ)) := by positivity
    have h2 : 2 * A * (∫ y, |a y - xan a n y|) + (∫ y, |a y - xan a n y|) ^ 2 ≤
        2 * A * (C1 * n⁻¹) + (C1 * n⁻¹) ^ 2 := by
      have := pow_le_pow_left₀ hE0 hb 2
      nlinarith [mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * A)]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left h2 this)
  · -- `s > 0`
    set T : ℝ := 2 * A * C0 + C0 ^ 2 with hT
    have hT0 : 0 ≤ T := by positivity
    have hRlim : Tendsto (fun R : ℝ => R ^ (-s)) atTop (nhds 0) := tendsto_rpow_neg_atTop hs
    have hRev : ∀ᶠ R : ℝ in atTop, L * R ^ (-s) * T < ε / 2 := by
      have h := (hRlim.const_mul L).mul_const T
      have h' : Tendsto (fun R : ℝ => L * R ^ (-s) * T) atTop (nhds 0) := by simpa using h
      exact h'.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 2))
    obtain ⟨R, hRT, hR1⟩ := (hRev.and (eventually_ge_atTop (1 : ℝ))).exists
    have hR0 : 0 < R := by linarith
    have hlim : Tendsto (fun n : ℝ => L * xNR d s R * (∫ ξ, (1 - xσ n ξ) * ‖𝓕 φ ξ‖) * (2 * A + C0))
        atTop (nhds 0) := by
      have := (hom.const_mul (L * xNR d s R)).mul_const (2 * A + C0)
      simpa using this
    have h1 := (Metric.tendsto_nhds.1 hlim) (ε / 2) (by positivity)
    filter_upwards [h1, eventually_ge_atTop (2 : ℝ)] with n hn hn2
    refine lt_of_le_of_lt (master n hn2 R hR0) ?_
    have hE0 : 0 ≤ ∫ y, |a y - xan a n y| := integral_nonneg fun _ => abs_nonneg _
    have hb := (hE n hn2).2.1
    have h2 : 2 * A * (∫ y, |a y - xan a n y|) + (∫ y, |a y - xan a n y|) ^ 2 ≤ T := by
      have := pow_le_pow_left₀ hE0 hb 2
      nlinarith [mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * A)]
    have hRs : 0 ≤ L * R ^ (-s) := mul_nonneg hL0 (Real.rpow_nonneg hR0.le _)
    have h3 := mul_le_mul_of_nonneg_left h2 hRs
    have h4 : L * xNR d s R * (∫ ξ, (1 - xσ n ξ) * ‖𝓕 φ ξ‖) * (2 * A + C0) < ε / 2 := by
      have := hn
      rw [Real.dist_eq, sub_zero] at this
      exact lt_of_le_of_lt (le_abs_self _) this
    have h5 := lt_of_le_of_lt h3 hRT
    linarith

end HRS.Commutator.Whole.XNRS
