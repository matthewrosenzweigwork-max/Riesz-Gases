import HRS.MS.FixEqP1Aux1
import HRS.MS.S111K2B02

/-!
# S11.1 continuation, B04 (part 1): the weighted `E_{r,P}` norm and dual bound for functions of linear growth

A function `g` with `|g x| ≤ A (1+|x|)` and `‖D^j g‖ ≤ A` (`1 ≤ j ≤ r`) has `‖g‖_{E_{r,P}} ≤ c A` when `2P > d + 2`,
and for a bounded linear functional `η` on `E_{r,P}` and a qualitatively bounded `g`, `|η g| ≤ ‖η‖_{F_{r,P}} c A`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K2

open HRS HRS.Whole HRS.MS.FixEq

variable {d : ℕ}

/-- `∫ ⟨x⟩^{-2P} (1+|x|)²` is finite for `2P > d+2`. -/
lemma s111k2_Wlin_integrable {P : ℝ} (hP : (d : ℝ) + 2 < 2 * P) :
    Integrable (fun x : Euc d => s57pW d P x * (1 + ‖x‖) ^ 2) (volume : Measure (Euc d)) := by
  have hP0 : 0 ≤ P := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hint : Integrable (fun x : Euc d => (1 + ‖x‖) ^ (-(2 * P - 2))) (volume : Measure (Euc d)) :=
    integrable_one_add_norm (by simpa using (by linarith : (d : ℝ) < 2 * P - 2))
  refine Integrable.mono' (hint.const_mul (2 ^ P)) ?_ (Filter.Eventually.of_forall fun x => ?_)
  · have : Continuous fun x : Euc d => s57pW d P x * (1 + ‖x‖) ^ 2 := by
      have h1 : Continuous (s57pW d P) := by
        unfold s57pW
        refine Continuous.rpow_const ?_ (fun x => Or.inl (s57p_jbracket_pos x).ne')
        unfold jbracket
        fun_prop
      exact h1.mul (by fun_prop)
    exact this.aestronglyMeasurable
  · have h0 : 0 ≤ s57pW d P x * (1 + ‖x‖) ^ 2 := mul_nonneg (s57pW_nonneg P x) (sq_nonneg _)
    rw [Real.norm_of_nonneg h0]
    have h1 := s57pW_le hP0 x
    have h2 : (1 + ‖x‖) ^ (-(2 * P - 2)) = (1 + ‖x‖) ^ (-(2 * P)) * (1 + ‖x‖) ^ 2 := by
      have hpos : (0 : ℝ) < 1 + ‖x‖ := by positivity
      rw [show -(2 * P - 2) = -(2 * P) + (2 : ℕ) by push_cast; ring, Real.rpow_add hpos, Real.rpow_natCast]
    rw [h2, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)

/-- The constant of the linear-growth `E`-bound. -/
def s111k2_CE (d r : ℕ) (P : ℝ) : ℝ :=
  ((s57pN d r : ℝ) * ∫ x : Euc d, s57pW d P x * (1 + ‖x‖) ^ 2) ^ (1 / 2 : ℝ)

lemma s111k2_CE_nonneg (r : ℕ) (P : ℝ) : 0 ≤ s111k2_CE d r P := by
  unfold s111k2_CE
  refine Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _) (integral_nonneg fun x => ?_)) _
  exact mul_nonneg (s57pW_nonneg P x) (sq_nonneg _)

lemma s111k2_S_le_lin {r : ℕ} {P : ℝ} (hP : (d : ℝ) + 2 < 2 * P) {f : Euc d → ℝ} {B : ℝ}
    (hB : ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x, |partialDeriv i f x| ≤ B * (1 + ‖x‖)) :
    s57pS d r P f ≤ ENNReal.ofReal ((s57pN d r : ℝ) *
      (B ^ 2 * ∫ x : Euc d, s57pW d P x * (1 + ‖x‖) ^ 2)) := by
  have hW := s111k2_Wlin_integrable (d := d) hP
  have key : ∀ j ≤ r, ∀ i : Fin j → Fin d,
      ∫⁻ x, ENNReal.ofReal (jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2) ≤
        ENNReal.ofReal (B ^ 2 * ∫ x : Euc d, s57pW d P x * (1 + ‖x‖) ^ 2) := by
    intro j hj i
    have h1 : ∀ x, ENNReal.ofReal (jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2) ≤
        ENNReal.ofReal (B ^ 2 * (s57pW d P x * (1 + ‖x‖) ^ 2)) := by
      intro x
      apply ENNReal.ofReal_le_ofReal
      have h2 : (partialDeriv i f x) ^ 2 ≤ (B * (1 + ‖x‖)) ^ 2 := by
        have := hB j hj i x
        exact sq_le_sq' (by linarith [abs_nonneg (partialDeriv i f x), neg_abs_le (partialDeriv i f x)])
          (le_trans (le_abs_self _) this)
      have h3 : 0 ≤ jbracket x ^ (-2 * P) := (Real.rpow_pos_of_pos (s57p_jbracket_pos x) _).le
      calc jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2 ≤ jbracket x ^ (-2 * P) * (B * (1 + ‖x‖)) ^ 2 :=
            mul_le_mul_of_nonneg_left h2 h3
        _ = B ^ 2 * (s57pW d P x * (1 + ‖x‖) ^ 2) := by unfold s57pW; ring
    calc ∫⁻ x, ENNReal.ofReal (jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2)
        ≤ ∫⁻ x, ENNReal.ofReal (B ^ 2 * (s57pW d P x * (1 + ‖x‖) ^ 2)) := lintegral_mono h1
      _ = ENNReal.ofReal (∫ x, B ^ 2 * (s57pW d P x * (1 + ‖x‖) ^ 2)) := by
          rw [ofReal_integral_eq_lintegral_ofReal (hW.const_mul _)
            (Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg B)
              (mul_nonneg (s57pW_nonneg P x) (sq_nonneg _)))]
      _ = ENNReal.ofReal (B ^ 2 * ∫ x : Euc d, s57pW d P x * (1 + ‖x‖) ^ 2) := by rw [integral_const_mul]
  unfold s57pS
  calc ∑ j ∈ Finset.range (r + 1), ∑ i : Fin j → Fin d,
        ∫⁻ x, ENNReal.ofReal (jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2)
      ≤ ∑ j ∈ Finset.range (r + 1), ∑ _i : Fin j → Fin d,
          ENNReal.ofReal (B ^ 2 * ∫ x : Euc d, s57pW d P x * (1 + ‖x‖) ^ 2) := by
        refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun i _ => ?_
        exact key j (by simpa [Nat.lt_succ_iff] using hj) i
    _ = ENNReal.ofReal ((s57pN d r : ℝ) * (B ^ 2 * ∫ x : Euc d, s57pW d P x * (1 + ‖x‖) ^ 2)) := by
        have hnn : 0 ≤ B ^ 2 * ∫ x : Euc d, s57pW d P x * (1 + ‖x‖) ^ 2 :=
          mul_nonneg (sq_nonneg B) (integral_nonneg fun x => mul_nonneg (s57pW_nonneg P x) (sq_nonneg _))
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        unfold s57pN
        push_cast
        rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [ENNReal.ofReal_mul (by positivity)]
        simp

lemma s111k2_E_le_lin {r : ℕ} {P : ℝ} (hP : (d : ℝ) + 2 < 2 * P) {f : Euc d → ℝ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x, |partialDeriv i f x| ≤ B * (1 + ‖x‖)) :
    weightedSobolevE r P f ≤ ENNReal.ofReal (s111k2_CE d r P * B) := by
  have hS := s111k2_S_le_lin hP hB
  rw [s57p_E_eq]
  have hW : 0 ≤ ∫ x : Euc d, s57pW d P x * (1 + ‖x‖) ^ 2 :=
    integral_nonneg fun x => mul_nonneg (s57pW_nonneg P x) (sq_nonneg _)
  calc (s57pS d r P f) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal ((s57pN d r : ℝ) * (B ^ 2 * ∫ x : Euc d, s57pW d P x * (1 + ‖x‖) ^ 2))) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hS (by norm_num)
    _ = ENNReal.ofReal (((s57pN d r : ℝ) * (B ^ 2 * ∫ x : Euc d, s57pW d P x * (1 + ‖x‖) ^ 2)) ^ (1 / 2 : ℝ)) :=
        ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (sq_nonneg B) hW)) (by norm_num)
    _ = ENNReal.ofReal (s111k2_CE d r P * B) := by
        congr 1
        unfold s111k2_CE
        rw [show (s57pN d r : ℝ) * (B ^ 2 * ∫ x : Euc d, s57pW d P x * (1 + ‖x‖) ^ 2) =
          ((s57pN d r : ℝ) * ∫ x : Euc d, s57pW d P x * (1 + ‖x‖) ^ 2) * B ^ 2 by ring,
          Real.mul_rpow (mul_nonneg (Nat.cast_nonneg _) hW) (sq_nonneg B)]
        congr 1
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hB0]

/-- The dual bound for a bounded linear functional on a function of linear growth (qualitatively bounded). -/
lemma s111k2_dual_lin {r : ℕ} {P : ℝ} (hP : (d : ℝ) + 2 < 2 * P) {η : (Euc d → ℝ) → ℝ}
    (hη : IsBoundedLinearOnE r P η) (hdual : dualNormE r P η < ⊤) {g : Euc d → ℝ}
    (hg : ContDiff ℝ r g) {B0 : ℝ} (hB0 : ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ B0)
    {A : ℝ} (hA : 0 ≤ A) (hlin : ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x, |partialDeriv i g x| ≤ A * (1 + ‖x‖)) :
    |η g| ≤ (dualNormE r P η).toReal * (s111k2_CE d r P * A) := by
  have hP' : (d : ℝ) < 2 * P := by linarith
  have h1 := s57p_dual_bound hP' hη hg hB0
  have h2 := s111k2_E_le_lin hP hA hlin
  have h3 : ENNReal.ofReal |η g| ≤ dualNormE r P η * ENNReal.ofReal (s111k2_CE d r P * A) :=
    h1.trans (mul_le_mul' le_rfl h2)
  have h4 := ENNReal.toReal_mono (ENNReal.mul_ne_top hdual.ne ENNReal.ofReal_ne_top) h3
  rw [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (mul_nonneg (s111k2_CE_nonneg r P) hA)] at h4
  exact h4

end HRS.MS.S111K2
