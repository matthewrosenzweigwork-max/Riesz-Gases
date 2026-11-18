import HRS.MC.CepH2Aux31

/-!
# CEPH2, S2a (part 1): the partition function is finite and positive; the Gibbs reference is a probability measure
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

theorem h2_alcove_nonempty : (cep_Alcove N).Nonempty := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
  refine ⟨WithLp.toLp 2 fun k : Fin N => (k : ℝ) / N, ?_, ?_⟩
  · intro k l hkl
    show (k : ℝ) / N < (l : ℝ) / N
    exact div_lt_div_of_pos_right (by exact_mod_cast hkl) hN
  · intro k l
    show (l : ℝ) / N < (k : ℝ) / N + 1
    have : (l : ℝ) < N := by exact_mod_cast l.2
    have h2 : (l : ℝ) / N < 1 := (div_lt_one hN).2 this
    have : (0 : ℝ) ≤ (k : ℝ) / N := by positivity
    linarith

theorem h2_alcove_perp_le {w : Ch N} (hw : w ∈ cep_Alcove N) : ‖h2_perp w‖ ≤ Real.sqrt N := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
  have hd : ∀ k l : Fin N, |w k - w l| ≤ 1 := by
    intro k l
    rcases lt_trichotomy k l with h | h | h
    · have h1 := hw.1 k l h; have h2 := hw.2 l k; have h3 := hw.2 k l; rw [abs_le]; constructor <;> linarith
    · subst h; simp
    · have h1 := hw.1 l k h; have h2 := hw.2 l k; have h3 := hw.2 k l; rw [abs_le]; constructor <;> linarith
  have hk : ∀ k, |w k - h2_mean w| ≤ 1 := by
    intro k
    have e : w k - h2_mean w = (∑ l, (w k - w l)) / N := by
      unfold h2_mean
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    rw [e, abs_div, abs_of_pos hN, div_le_one hN]
    calc |∑ l, (w k - w l)| ≤ ∑ l, |w k - w l| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : Fin N, (1 : ℝ) := Finset.sum_le_sum fun l _ => hd k l
      _ = N := by simp
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc ∑ k, ‖(h2_perp w) k‖ ^ 2 ≤ ∑ _k : Fin N, (1 : ℝ) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have : (h2_perp w) k = w k - h2_mean w := by
          simp [h2_perp_eq, cep_diag_apply]
        rw [this, Real.norm_eq_abs]
        have h1 := hk k
        nlinarith [abs_nonneg (w k - h2_mean w)]
    _ = N := by simp

theorem h2_infDist_ge (z : Ch N) : ‖h2_perp z‖ - Real.sqrt N ≤ Metric.infDist z (cep_Alcove N) := by
  rw [Metric.le_infDist h2_alcove_nonempty]
  intro w hw
  rw [dist_eq_norm]
  have h1 : h2_perp z = h2_perp (z - w) + h2_perp w := by rw [← h2_perp_add]; simp
  have h2 := norm_add_le (h2_perp (z - w)) (h2_perp w)
  have h3 := h2_norm_perp_le (z - w)
  have h4 := h2_alcove_perp_le hw
  rw [h1]
  linarith

/-- A quadratic lower bound for `U` in the transverse variable. -/
theorem h2_U_lower {U : Ch N → ℝ}
    (hconf : ∃ c C : ℝ, 0 < c ∧ ∀ z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ U z) :
    ∃ c C : ℝ, 0 < c ∧ ∀ z, c * ‖h2_perp z‖ ^ 2 - C ≤ U z := by
  obtain ⟨c, C, hc, h⟩ := hconf
  refine ⟨c / 2, C + c * N, by positivity, fun z => ?_⟩
  have h1 := h z
  have h2 := h2_infDist_ge z
  have hs : Real.sqrt N ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg _)
  have h3 : ‖h2_perp z‖ ^ 2 / 2 - N ≤ Metric.infDist z (cep_Alcove N) ^ 2 := by
    set x := ‖h2_perp z‖
    set s := Real.sqrt N
    set d := Metric.infDist z (cep_Alcove N)
    have hd : 0 ≤ d := Metric.infDist_nonneg
    by_cases hx : x ≤ s
    · have hx0 : 0 ≤ x := norm_nonneg _
      nlinarith [sq_nonneg d, mul_self_le_mul_self hx0 hx]
    · push_neg at hx
      have : x - s ≤ d := h2
      nlinarith [sq_nonneg (x - 2 * s), mul_self_le_mul_self (by linarith : 0 ≤ x - s) this]
  nlinarith [mul_le_mul_of_nonneg_left h3 hc.le]

theorem h2_cell_sq_ge {z : Ch N} (hz : z ∈ cep_cell N) :
    ‖z‖ ^ 2 / 2 - N ≤ (1 + Real.sqrt N) ^ 2 * ‖h2_perp z‖ ^ 2 := by
  have h := h2_cell_norm_le hz
  set r := ‖h2_perp z‖
  set s := Real.sqrt N
  have hs : s ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg _)
  have hr : 0 ≤ r := norm_nonneg _
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have h1 : ‖z‖ ≤ (1 + s) * r + s := by linarith
  have h2 : ‖z‖ ^ 2 ≤ ((1 + s) * r + s) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg ((1 + s) * r - s)]

/-- Gaussian decay of the transverse variable is integrable over the cell. -/
theorem h2_lintegral_cell_gauss {a : ℝ} (ha : 0 < a) :
    ∫⁻ z in cep_cell N, ENNReal.ofReal (Real.exp (-a * ‖h2_perp z‖ ^ 2)) < ⊤ := by
  set κ := (1 + Real.sqrt N) ^ 2 with hκ
  have hκ1 : 1 ≤ κ := by
    rw [hκ]; nlinarith [Real.sqrt_nonneg (N : ℝ)]
  have hκ0 : 0 < κ := by linarith
  set b := a / (2 * κ) with hb
  have hb0 : 0 < b := by positivity
  have hint := h2_integrable_gauss (N := N) hb0
  have hle : ∀ z ∈ cep_cell N, ENNReal.ofReal (Real.exp (-a * ‖h2_perp z‖ ^ 2)) ≤
      ENNReal.ofReal (Real.exp (a * N / κ) * Real.exp (-b * ‖z‖ ^ 2)) := by
    intro z hz
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h := h2_cell_sq_ge hz
    rw [← hκ] at h
    have h2 : (‖z‖ ^ 2 / 2 - N) / κ ≤ ‖h2_perp z‖ ^ 2 := by
      rw [div_le_iff₀ hκ0]; linarith
    have h3 : a * ((‖z‖ ^ 2 / 2 - N) / κ) ≤ a * ‖h2_perp z‖ ^ 2 := mul_le_mul_of_nonneg_left h2 ha.le
    have e : a * ((‖z‖ ^ 2 / 2 - N) / κ) = b * ‖z‖ ^ 2 - a * N / κ := by
      rw [hb]; field_simp
    nlinarith [e, h3]
  calc ∫⁻ z in cep_cell N, ENNReal.ofReal (Real.exp (-a * ‖h2_perp z‖ ^ 2))
      ≤ ∫⁻ z in cep_cell N, ENNReal.ofReal (Real.exp (a * N / κ) * Real.exp (-b * ‖z‖ ^ 2)) :=
        setLIntegral_mono' h2_cell_measurable hle
    _ ≤ ∫⁻ z, ENNReal.ofReal (Real.exp (a * N / κ) * Real.exp (-b * ‖z‖ ^ 2)) := setLIntegral_le_lintegral _ _
    _ < ⊤ := by
        rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _) (ae_of_all _ fun z => by positivity)]
        exact ENNReal.ofReal_lt_top

end HRS.MC.CepH2
