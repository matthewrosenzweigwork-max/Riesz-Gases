import HRS.Main.A8PAux32

/-!
# Packet A8P, part 33: the arithmetic of the rates
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

theorem a8p_covCost_eq (S : MainData d) (N : ℕ) (Cq Cp Ca Λ₁ Λ E : ℝ) {q : ℕ} (ts : Fin q → ℝ)
    (φ : Fin q → Torus d → ℝ) :
    a8pCovCost S N Cq Cp Ca Λ₁ Λ E ts φ =
      2 * (S.sigma N ^ 2 * S.invβ N / N) * S.T * Cq *
        (2 * d * Ca ^ 2 * smearScale d N Λ + Cp * Real.sqrt E) *
        (∑ a, a8pK Λ₁ (ts a) (φ a)) ^ 2 := by
  unfold a8pCovCost
  rw [show (∑ a, a8pK Λ₁ (ts a) (φ a)) ^ 2 =
    (∑ a, a8pK Λ₁ (ts a) (φ a)) * (∑ b, a8pK Λ₁ (ts b) (φ b)) from sq _,
    Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem a8p_covCostTriv_eq (S : MainData d) (N : ℕ) (Ca Λ₁ : ℝ) {q : ℕ} (ts : Fin q → ℝ)
    (φ : Fin q → Torus d → ℝ) :
    a8pCovCostTriv S N Ca Λ₁ ts φ =
      4 * (S.sigma N ^ 2 * S.invβ N / N) * S.T * d * Ca ^ 2 * (∑ a, a8pK Λ₁ (ts a) (φ a)) ^ 2 := by
  unfold a8pCovCostTriv
  rw [show (∑ a, a8pK Λ₁ (ts a) (φ a)) ^ 2 =
    (∑ a, a8pK Λ₁ (ts a) (φ a)) * (∑ b, a8pK Λ₁ (ts b) (φ b)) from sq _,
    Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem a8p_remConst_eq (S : MainData d) (N : ℕ) (Cq cT Λ₁ : ℝ) {q : ℕ} (ts : Fin q → ℝ)
    (φ : Fin q → Torus d → ℝ) :
    ∑ a, S.sigma N * ((1 / 2) * (Cq * (cT * a8pK Λ₁ (ts a) (φ a)))) =
      S.sigma N * ((1 / 2) * (Cq * cT)) * ∑ a, a8pK Λ₁ (ts a) (φ a) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- `(E^{1/4})^2 = √E`. -/
theorem a8p_fourth_sq {E : ℝ} (hE : 0 ≤ E) : (E ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt E := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hE, Real.sqrt_eq_rpow]
  norm_num

theorem a8p_arith_smooth_cost {K ε σ E q sm u T Cq cT Ca Cp dd : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hσ : 0 ≤ σ) (hE : 0 < E) (hq0 : 0 ≤ q) (hsm0 : 0 ≤ sm) (hsm : sm ≤ u ^ 2) (hu : 0 ≤ u)
    (hT : 0 ≤ T) (hCq : 0 ≤ Cq) (hcT : 0 ≤ cT) (hCp : 0 ≤ Cp) (hdd : 0 ≤ dd)
    (hr : ε + Real.sqrt q * (E ^ ((1 : ℝ) / 4) + u) + σ * E < 1) :
    σ * ((1 / 2) * (Cq * cT)) * K * (T * E) + ε * K +
        (1 / 2) * (2 * q * T * Cq * (2 * dd * Ca ^ 2 * sm + Cp * Real.sqrt E) * K ^ 2) ≤
      ((1 / 2) * Cq * cT * T + 1 + 2 * T * Cq * (2 * dd * Ca ^ 2 + Cp)) * (K + K ^ 2) *
        (ε + Real.sqrt q * (E ^ ((1 : ℝ) / 4) + u) + σ * E) := by
  set b : ℝ := E ^ ((1 : ℝ) / 4) with hb
  have hb0 : 0 ≤ b := Real.rpow_nonneg hE.le _
  set a : ℝ := Real.sqrt q with ha
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have haq : a ^ 2 = q := Real.sq_sqrt hq0
  set r : ℝ := ε + a * (b + u) + σ * E with hrdef
  have hx : a * u ≤ r := by nlinarith [mul_nonneg ha0 hb0, mul_nonneg hσ hE.le]
  have hy : a * b ≤ r := by nlinarith [mul_nonneg ha0 hu, mul_nonneg hσ hE.le]
  have hr0 : 0 ≤ r := by
    have := mul_nonneg ha0 (add_nonneg hb0 hu)
    have := mul_nonneg hσ hE.le
    linarith
  have hqsm : q * sm ≤ r := by
    have h1 : q * sm ≤ (a * u) ^ 2 := by
      rw [mul_pow, haq]; exact mul_le_mul_of_nonneg_left hsm hq0
    have hxx : a * u ≤ 1 := by linarith
    have h2 : (a * u) ^ 2 ≤ a * u := by
      have := mul_nonneg ha0 hu
      nlinarith
    linarith
  have hqE : q * Real.sqrt E ≤ r := by
    have h0 : q * Real.sqrt E = (a * b) ^ 2 := by rw [mul_pow, haq, hb, a8p_fourth_sq hE.le]
    have hyy : a * b ≤ 1 := by linarith
    have h2 : (a * b) ^ 2 ≤ a * b := by
      have := mul_nonneg ha0 hb0
      nlinarith
    linarith
  have hσE : σ * E ≤ r := by nlinarith [mul_nonneg ha0 (add_nonneg hb0 hu)]
  have hεr : ε ≤ r := by nlinarith [mul_nonneg ha0 (add_nonneg hb0 hu), mul_nonneg hσ hE.le]
  have hCa2 : 0 ≤ Ca ^ 2 := sq_nonneg _
  have t1 : σ * ((1 / 2) * (Cq * cT)) * K * (T * E) ≤ ((1 / 2) * Cq * cT * T) * K * r := by
    have : σ * ((1 / 2) * (Cq * cT)) * K * (T * E) = ((1 / 2) * Cq * cT * T) * K * (σ * E) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hσE (by positivity)
  have t2 : ε * K ≤ K * r := by nlinarith
  have t3 : (1 / 2) * (2 * q * T * Cq * (2 * dd * Ca ^ 2 * sm + Cp * Real.sqrt E) * K ^ 2) ≤
      T * Cq * (2 * dd * Ca ^ 2 + Cp) * K ^ 2 * r := by
    have e : (1 / 2) * (2 * q * T * Cq * (2 * dd * Ca ^ 2 * sm + Cp * Real.sqrt E) * K ^ 2) =
        T * Cq * K ^ 2 * (2 * dd * Ca ^ 2 * (q * sm) + Cp * (q * Real.sqrt E)) := by ring
    rw [e]
    have h1 : 2 * dd * Ca ^ 2 * (q * sm) + Cp * (q * Real.sqrt E) ≤ (2 * dd * Ca ^ 2 + Cp) * r := by
      have := mul_le_mul_of_nonneg_left hqsm (by positivity : 0 ≤ 2 * dd * Ca ^ 2)
      have := mul_le_mul_of_nonneg_left hqE hCp
      nlinarith
    calc T * Cq * K ^ 2 * (2 * dd * Ca ^ 2 * (q * sm) + Cp * (q * Real.sqrt E))
        ≤ T * Cq * K ^ 2 * ((2 * dd * Ca ^ 2 + Cp) * r) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  have hdiff : 0 ≤ ((1 / 2) * Cq * cT * T + 1) * K ^ 2 * r + 2 * (T * Cq * (2 * dd * Ca ^ 2 + Cp)) * K * r +
      (T * Cq * (2 * dd * Ca ^ 2 + Cp)) * K ^ 2 * r := by positivity
  linarith [t1, t2, t3, hdiff]

theorem a8p_arith_smooth_triv {K ε σ E q T Cq cT Ca dd r : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hσ : 0 ≤ σ) (hE : 0 < E) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hT : 0 ≤ T) (hCq : 0 ≤ Cq) (hcT : 0 ≤ cT)
    (hdd : 0 ≤ dd) (hr : ε + σ * E ≤ r) (hr1 : 1 ≤ r) :
    σ * ((1 / 2) * (Cq * cT)) * K * (T * E) + ε * K + (1 / 2) * (4 * q * T * dd * Ca ^ 2 * K ^ 2) ≤
      ((1 / 2) * Cq * cT * T + 1 + 4 * T * dd * Ca ^ 2) * (K + K ^ 2) * r := by
  have hσE : 0 ≤ σ * E := mul_nonneg hσ hE.le
  have t1 : σ * ((1 / 2) * (Cq * cT)) * K * (T * E) ≤ ((1 / 2) * Cq * cT * T) * K * r := by
    have : σ * ((1 / 2) * (Cq * cT)) * K * (T * E) = ((1 / 2) * Cq * cT * T) * K * (σ * E) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have t2 : ε * K ≤ K * r := by nlinarith
  have t3 : (1 / 2) * (4 * q * T * dd * Ca ^ 2 * K ^ 2) ≤ (4 * T * dd * Ca ^ 2) * K ^ 2 * r := by
    have h1 : q ≤ r := by linarith
    have : (1 / 2) * (4 * q * T * dd * Ca ^ 2 * K ^ 2) = (2 * T * dd * Ca ^ 2 * K ^ 2) * q := by ring
    rw [this]
    have h3 : 0 ≤ 2 * T * dd * Ca ^ 2 * K ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 h3, mul_nonneg h3 (by linarith : 0 ≤ r)]
  have hr0 : 0 ≤ r := by linarith
  have hdiff : 0 ≤ ((1 / 2) * Cq * cT * T + 1) * K ^ 2 * r + (4 * T * dd * Ca ^ 2) * K * r := by positivity
  linarith [t1, t2, t3, hdiff]

end HRS.Main.A8P
