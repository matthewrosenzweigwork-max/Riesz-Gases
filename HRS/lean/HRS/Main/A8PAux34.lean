import HRS.Main.A8PAux33

/-!
# Packet A8P, part 34: the arithmetic of the rates (Wasserstein)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

theorem a8p_arith_wass {K ε σ E E' q sm u T Cq cT Ca Cp dd : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hσ : 0 ≤ σ) (hE : 0 < E) (hE' : 0 ≤ E') (hq0 : 0 ≤ q) (hsm0 : 0 ≤ sm) (hsm : sm ≤ u ^ 2)
    (hu : 0 ≤ u) (hT : 0 ≤ T) (hCq : 0 ≤ Cq) (hcT : 0 ≤ cT) (hCp : 0 ≤ Cp) (hdd : 0 ≤ dd) :
    ε * K + K * Real.sqrt (2 * q * T * Cq * (2 * dd * Ca ^ 2 * sm + Cp * Real.sqrt E)) +
        σ * ((1 / 2) * (Cq * cT)) * K * (T * E') ≤
      ((1 / 2) * Cq * cT * T + 1 + Real.sqrt (2 * T * Cq * (2 * dd * Ca ^ 2 + Cp))) * (K + K ^ 2) *
        (ε + Real.sqrt q * (E ^ ((1 : ℝ) / 4) + u) + σ * E') := by
  set b : ℝ := E ^ ((1 : ℝ) / 4) with hb
  have hb0 : 0 ≤ b := Real.rpow_nonneg hE.le _
  set a : ℝ := Real.sqrt q with ha
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have haq : a ^ 2 = q := Real.sq_sqrt hq0
  set r : ℝ := ε + a * (b + u) + σ * E' with hrdef
  have hσE : 0 ≤ σ * E' := mul_nonneg hσ hE'
  have hxy0 : 0 ≤ a * (b + u) := mul_nonneg ha0 (add_nonneg hb0 hu)
  have hr0 : 0 ≤ r := by linarith
  have hA : 2 * q * T * Cq * (2 * dd * Ca ^ 2 * sm + Cp * Real.sqrt E) ≤
      (2 * T * Cq * (2 * dd * Ca ^ 2 + Cp)) * (a * (b + u)) ^ 2 := by
    have h1 : q * sm ≤ (a * u) ^ 2 := by rw [mul_pow, haq]; exact mul_le_mul_of_nonneg_left hsm hq0
    have h2 : q * Real.sqrt E = (a * b) ^ 2 := by rw [mul_pow, haq, hb, a8p_fourth_sq hE.le]
    have hau := mul_nonneg ha0 hu
    have hab := mul_nonneg ha0 hb0
    have hsum : a * (b + u) = a * b + a * u := by ring
    have c3 : (a * u) ^ 2 ≤ (a * (b + u)) ^ 2 :=
      pow_le_pow_left₀ hau (by rw [hsum]; linarith) 2
    have c4 : (a * b) ^ 2 ≤ (a * (b + u)) ^ 2 :=
      pow_le_pow_left₀ hab (by rw [hsum]; linarith) 2
    have e : 2 * q * T * Cq * (2 * dd * Ca ^ 2 * sm + Cp * Real.sqrt E) =
        2 * T * Cq * (2 * dd * Ca ^ 2 * (q * sm) + Cp * (q * Real.sqrt E)) := by ring
    rw [e]
    have h4 : 2 * dd * Ca ^ 2 * (q * sm) + Cp * (q * Real.sqrt E) ≤
        (2 * dd * Ca ^ 2 + Cp) * (a * (b + u)) ^ 2 := by
      rw [h2]
      have d1 := mul_le_mul_of_nonneg_left (h1.trans c3) (by positivity : 0 ≤ 2 * dd * Ca ^ 2)
      have d2 := mul_le_mul_of_nonneg_left c4 hCp
      linarith
    calc 2 * T * Cq * (2 * dd * Ca ^ 2 * (q * sm) + Cp * (q * Real.sqrt E))
        ≤ 2 * T * Cq * ((2 * dd * Ca ^ 2 + Cp) * (a * (b + u)) ^ 2) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = _ := by ring
  have hs : Real.sqrt (2 * q * T * Cq * (2 * dd * Ca ^ 2 * sm + Cp * Real.sqrt E)) ≤
      Real.sqrt (2 * T * Cq * (2 * dd * Ca ^ 2 + Cp)) * (a * (b + u)) := by
    refine (Real.sqrt_le_sqrt hA).trans (le_of_eq ?_)
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hxy0]
  set Mw : ℝ := Real.sqrt (2 * T * Cq * (2 * dd * Ca ^ 2 + Cp)) with hMw
  have hMw0 : 0 ≤ Mw := Real.sqrt_nonneg _
  have t1 : σ * ((1 / 2) * (Cq * cT)) * K * (T * E') ≤ ((1 / 2) * Cq * cT * T) * K * r := by
    have : σ * ((1 / 2) * (Cq * cT)) * K * (T * E') = ((1 / 2) * Cq * cT * T) * K * (σ * E') := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith [mul_nonneg hε hε]) (by positivity)
  have t2 : ε * K ≤ K * r := by nlinarith
  have t3 : K * Real.sqrt (2 * q * T * Cq * (2 * dd * Ca ^ 2 * sm + Cp * Real.sqrt E)) ≤
      Mw * K * r := by
    calc K * Real.sqrt (2 * q * T * Cq * (2 * dd * Ca ^ 2 * sm + Cp * Real.sqrt E))
        ≤ K * (Mw * (a * (b + u))) := mul_le_mul_of_nonneg_left hs hK
      _ ≤ K * (Mw * r) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hMw0) hK
      _ = Mw * K * r := by ring
  have hc1 : 0 ≤ (1 / 2) * Cq * cT * T := by positivity
  have hdiff : 0 ≤ ((1 / 2) * Cq * cT * T + 1 + Mw) * K ^ 2 * r := by positivity
  linarith [t1, t2, t3, hdiff]

end HRS.Main.A8P
