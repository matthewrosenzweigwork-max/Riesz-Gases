/-
# HRS.Equilibrium.L49Aux2 — Proposition 4.9, part 2: radial integrals and the pointwise estimate

* `l49_ballConst_eq`: `ballConst d = sphereArea d` (`d · vol B₁ = 2π^{d/2}/Γ(d/2)`).
* `l49_radial_ind`: `∫_{ℝ^d} 1_{(ε,δ]}(|w|) |w|^{-a} dw = ballConst d · ∫_ε^δ r^{d-1-a} dr`.
* `l49_pointwise`: the elementary pointwise estimate behind `R:eq:compensated-integral`
  (all five error terms of the TeX proof at once).
-/
import HRS.Equilibrium.LocalDivMain
import HRS.Equilibrium.L49Aux1

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace L49

open HRS.LocalDivAux

variable {d : ℕ}

/-- `ballConst d = d vol(B₁) = |S^{d-1}| = 2π^{d/2}/Γ(d/2)`. -/
theorem l49_ballConst_eq (hd : 1 ≤ d) : ballConst d = sphereArea d := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin d))).real (ball 0 1) =
      Real.sqrt Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1) := by
    have h := EuclideanSpace.volume_ball (ι := Fin d) (0 : EuclideanSpace ℝ (Fin d)) 1
    simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul] at h
    rw [Measure.real, h, ENNReal.toReal_ofReal]
    positivity
  unfold ballConst sphereArea
  rw [hvol, Real.Gamma_add_one (by positivity)]
  have hsq : Real.sqrt Real.pi ^ d = Real.pi ^ ((d : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    congr 1; ring
  rw [hsq]
  have hg : 0 < Real.Gamma ((d : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  field_simp

theorem l49_radial_ind (hd : 1 ≤ d) {ε δ : ℝ} (hε : 0 ≤ ε) (hεδ : ε ≤ δ) (a : ℝ)
    (hint : -1 < (d : ℝ) - 1 - a ∨ 0 < ε) :
    Integrable (fun w : Euc d => (Ioc ε δ).indicator (fun r : ℝ => r ^ (-a)) ‖w‖) ∧
    ∫ w : Euc d, (Ioc ε δ).indicator (fun r : ℝ => r ^ (-a)) ‖w‖ =
      ballConst d * ∫ r in ε..δ, r ^ ((d : ℝ) - 1 - a) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have h1 : ∀ r : ℝ, r ^ (d - 1) * (Ioc ε δ).indicator (fun r : ℝ => r ^ (-a)) r =
      (Ioc ε δ).indicator (fun r : ℝ => r ^ ((d : ℝ) - 1 - a)) r := by
    intro r
    by_cases hr : r ∈ Ioc ε δ
    · have hr0 : 0 < r := hε.trans_lt hr.1
      rw [indicator_of_mem hr, indicator_of_mem hr, ← Real.rpow_natCast, ← Real.rpow_add hr0]
      congr 1
      rw [Nat.cast_sub hd]; push_cast; ring
    · simp [indicator_of_notMem hr]
  have hii : IntegrableOn (fun r : ℝ => r ^ ((d : ℝ) - 1 - a)) (Ioc ε δ) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hεδ]
    rcases hint with h | h
    · exact intervalIntegral.intervalIntegrable_rpow' h
    · refine intervalIntegral.intervalIntegrable_rpow (Or.inr ?_)
      rw [uIcc_of_le hεδ]
      exact fun h0 => absurd h0.1 (not_le.2 h)
  have hfun : (fun y : ℝ => y ^ (d - 1) • (Ioc ε δ).indicator (fun r : ℝ => r ^ (-a)) y) =
      (Ioc ε δ).indicator (fun r : ℝ => r ^ ((d : ℝ) - 1 - a)) := by
    funext r; simp only [smul_eq_mul]; exact h1 r
  constructor
  · rw [integrable_fun_norm_addHaar (volume : Measure (Euc d)), finrank_euclideanSpace_fin, hfun]
    exact ((integrable_indicator_iff measurableSet_Ioc).2 hii).integrableOn
  · rw [integral_radial hd]
    congr 1
    have e1 : ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * (Ioc ε δ).indicator (fun r : ℝ => r ^ (-a)) r =
        ∫ r in Ioi (0 : ℝ), (Ioc ε δ).indicator (fun r : ℝ => r ^ ((d : ℝ) - 1 - a)) r :=
      setIntegral_congr_fun measurableSet_Ioi fun r _ => h1 r
    rw [e1, intervalIntegral.integral_of_le hεδ, setIntegral_indicator measurableSet_Ioc]
    have e : Ioi (0 : ℝ) ∩ Ioc ε δ = Ioc ε δ := by
      ext r
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨hε.trans_lt h.1, h⟩
    rw [e]

set_option maxHeartbeats 1600000 in
theorem l49_pointwise_near {t u lam gam R L Lam rw r0 : ℝ}
    (hu1 : 1 ≤ u) (htu : 1 ≤ t * u) (ht0 : 0 < t)
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hg0 : 0 ≤ gam) (hgu : |gam - u| ≤ R) (hR : 0 ≤ R)
    (hL : 0 ≤ L) (hLam : 0 ≤ Lam)
    (hrw : 0 ≤ rw) (hrwL : rw ≤ Lam) (hr0 : 0 ≤ r0) (hr0L : r0 ≤ Lam)
    (hrr : |rw - r0| ≤ L * t) (ha : lam * u < 1) :
    |rw * taylorH (lam * gam) - r0 * (lam ^ 2 * u ^ 2 / 2)| ≤
      (L * (1 + R ^ 2) + Lam * (4 * R ^ 3 + R + R ^ 2 / 2)) * (lam ^ 2 * (t * u ^ 2)) +
        4 * Lam * (lam ^ 3 * u ^ 3) := by
  set a : ℝ := lam * u with ha_def
  set v : ℝ := lam * gam with hv_def
  set b : ℝ := v - a with hb_def
  have ha0 : 0 ≤ a := by positivity
  have hv0 : 0 ≤ v := by positivity
  have hbabs : |b| ≤ lam * R := by
    have : b = lam * (gam - u) := by rw [hb_def, hv_def, ha_def]; ring
    rw [this, abs_mul, abs_of_pos hlam0]
    exact mul_le_mul_of_nonneg_left hgu hlam0.le
  have hb0 : 0 ≤ |b| := abs_nonneg _
  have hlR : 0 ≤ lam * R := by positivity
  have hv_le : v ≤ a + |b| := by
    have : v = a + b := by rw [hb_def]; ring
    rw [this]; linarith [le_abs_self b]
  have hH0 := l49_H_nonneg v
  have hHsq := l49_H_le_sq hv0
  have hHc := l49_H_cubic hv0
  -- bound on `H(v)`
  have hHbd : taylorH v ≤ a ^ 2 + (lam * R) ^ 2 := by
    have h1 : v ^ 2 ≤ (a + |b|) ^ 2 := pow_le_pow_left₀ hv0 hv_le 2
    have h2 : (a + |b|) ^ 2 ≤ 2 * a ^ 2 + 2 * |b| ^ 2 := by nlinarith [sq_nonneg (a - |b|)]
    have h3 : |b| ^ 2 ≤ (lam * R) ^ 2 := pow_le_pow_left₀ hb0 hbabs 2
    nlinarith
  -- bound on the cubic and the quadratic difference
  have hcub : v ^ 3 ≤ 4 * (a ^ 3 + (lam * R) ^ 3) := by
    have h1 : v ^ 3 ≤ (a + |b|) ^ 3 := pow_le_pow_left₀ hv0 hv_le 3
    have h2 : (a + |b|) ^ 3 ≤ 4 * (a ^ 3 + |b| ^ 3) := by
      nlinarith [sq_nonneg (a - |b|), mul_nonneg ha0 hb0, mul_nonneg (mul_nonneg ha0 hb0) (sq_nonneg (a - |b|)),
        mul_nonneg (add_nonneg ha0 hb0) (sq_nonneg (a - |b|))]
    have h3 : |b| ^ 3 ≤ (lam * R) ^ 3 := pow_le_pow_left₀ hb0 hbabs 3
    nlinarith
  have hsqd : |v ^ 2 - a ^ 2| / 2 ≤ (lam * R) * a + (lam * R) ^ 2 / 2 := by
    have e : v ^ 2 - a ^ 2 = b * (2 * a + b) := by rw [hb_def]; ring
    rw [e, abs_mul]
    have h1 : |2 * a + b| ≤ 2 * a + |b| := by
      calc |2 * a + b| ≤ |2 * a| + |b| := abs_add_le _ _
        _ = 2 * a + |b| := by rw [abs_of_nonneg (by positivity)]
    have h2 : |b| * |2 * a + b| ≤ |b| * (2 * a + |b|) := mul_le_mul_of_nonneg_left h1 hb0
    have h3 : |b| * (2 * a + |b|) ≤ (lam * R) * (2 * a) + (lam * R) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hbabs ha0, mul_le_mul hbabs hbabs hb0 hlR]
    nlinarith
  -- the main decomposition
  have hdec : rw * taylorH v - r0 * (a ^ 2 / 2) =
      (rw - r0) * taylorH v + r0 * ((taylorH v - v ^ 2 / 2) + (v ^ 2 - a ^ 2) / 2) := by ring
  have e2 : lam ^ 2 * u ^ 2 / 2 = a ^ 2 / 2 := by rw [ha_def]; ring
  rw [e2, hdec]
  refine (abs_add_le _ _).trans ?_
  have t1 : |(rw - r0) * taylorH v| ≤ L * t * (a ^ 2 + (lam * R) ^ 2) := by
    rw [abs_mul, abs_of_nonneg hH0]
    exact mul_le_mul hrr hHbd hH0 (by positivity)
  have t2 : |r0 * ((taylorH v - v ^ 2 / 2) + (v ^ 2 - a ^ 2) / 2)| ≤
      Lam * (4 * (a ^ 3 + (lam * R) ^ 3) + ((lam * R) * a + (lam * R) ^ 2 / 2)) := by
    rw [abs_mul, abs_of_nonneg hr0]
    refine mul_le_mul hr0L ?_ (abs_nonneg _) hLam
    refine (abs_add_le _ _).trans ?_
    have : |(v ^ 2 - a ^ 2) / 2| = |v ^ 2 - a ^ 2| / 2 := by
      rw [abs_div, abs_two]
    rw [this]
    linarith
  -- comparison with `Q = lam² t u²`
  have hu0 : 0 ≤ u := by linarith
  have htu2e : t * u ^ 2 = (t * u) * u := by ring
  have hutu : u ≤ t * u ^ 2 := by rw [htu2e]; exact le_mul_of_one_le_left hu0 htu
  have htu2 : 1 ≤ t * u ^ 2 := hu1.trans hutu
  have hu2 : 1 ≤ u ^ 2 := one_le_pow₀ hu1
  have htt : t ≤ t * u ^ 2 := le_mul_of_one_le_right ht0.le hu2
  have hQ0 : 0 ≤ lam ^ 2 := by positivity
  have hl3 : lam ^ 3 ≤ lam ^ 2 := by
    have : lam ^ 3 = lam ^ 2 * lam := by ring
    rw [this]; exact mul_le_of_le_one_right hQ0 hlam1
  have c1 : L * t * (a ^ 2 + (lam * R) ^ 2) ≤ L * (1 + R ^ 2) * (lam ^ 2 * (t * u ^ 2)) := by
    have : L * t * (a ^ 2 + (lam * R) ^ 2) = L * (lam ^ 2 * (t * u ^ 2)) + L * R ^ 2 * (lam ^ 2 * t) := by
      rw [ha_def]; ring
    rw [this]
    have h1 : lam ^ 2 * t ≤ lam ^ 2 * (t * u ^ 2) := mul_le_mul_of_nonneg_left htt hQ0
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hL (sq_nonneg R))
    linarith
  have c2 : Lam * (4 * (a ^ 3 + (lam * R) ^ 3) + ((lam * R) * a + (lam * R) ^ 2 / 2)) ≤
      Lam * (4 * R ^ 3 + R + R ^ 2 / 2) * (lam ^ 2 * (t * u ^ 2)) + 4 * Lam * (lam ^ 3 * u ^ 3) := by
    have h1 : lam ^ 2 ≤ lam ^ 2 * (t * u ^ 2) := le_mul_of_one_le_right hQ0 htu2
    have h2 : lam ^ 2 * u ≤ lam ^ 2 * (t * u ^ 2) := mul_le_mul_of_nonneg_left hutu hQ0
    have h3 : lam ^ 3 ≤ lam ^ 2 * (t * u ^ 2) := hl3.trans h1
    have e : 4 * (a ^ 3 + (lam * R) ^ 3) + ((lam * R) * a + (lam * R) ^ 2 / 2) =
        4 * (lam ^ 3 * u ^ 3) + (4 * R ^ 3 * lam ^ 3 + R * (lam ^ 2 * u) + R ^ 2 / 2 * lam ^ 2) := by
      rw [ha_def]; ring
    rw [e]
    have hR3 : 0 ≤ R ^ 3 := by positivity
    have h4 : 4 * R ^ 3 * lam ^ 3 + R * (lam ^ 2 * u) + R ^ 2 / 2 * lam ^ 2 ≤
        (4 * R ^ 3 + R + R ^ 2 / 2) * (lam ^ 2 * (t * u ^ 2)) := by
      nlinarith [mul_le_mul_of_nonneg_left h3 hR3, mul_le_mul_of_nonneg_left h2 hR,
        mul_le_mul_of_nonneg_left h1 (sq_nonneg R)]
    have h5 := mul_le_mul_of_nonneg_left h4 hLam
    linarith
  linarith

theorem l49_pointwise_inner {u lam gam R Lam rw : ℝ} (hu1 : 1 ≤ u) (hlam0 : 0 < lam)
    (hg0 : 0 ≤ gam) (hgu : |gam - u| ≤ R) (hR : 0 ≤ R) (hrw : 0 ≤ rw) (hrwL : rw ≤ Lam)
    (hLam : 0 ≤ Lam) :
    |rw * taylorH (lam * gam)| ≤ Lam * (1 + R) * (lam * u) := by
  have hH0 := l49_H_nonneg (lam * gam)
  have hHs := l49_H_le_self (by positivity : 0 ≤ lam * gam)
  have hgle : gam ≤ u * (1 + R) := by
    have := (abs_le.1 hgu).2
    nlinarith
  rw [abs_of_nonneg (mul_nonneg hrw hH0)]
  calc rw * taylorH (lam * gam) ≤ Lam * (lam * gam) :=
        mul_le_mul hrwL hHs hH0 hLam
    _ ≤ Lam * (lam * (u * (1 + R))) := by gcongr
    _ = Lam * (1 + R) * (lam * u) := by ring

end L49

end HRS

end
