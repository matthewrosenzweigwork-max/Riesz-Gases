import HRS.MS.Fp81S21WeightedRellich

/-!
The local tail seminorm here is the square of the target weighted `L²`
jet norm, integrated only where `jbracket x ≥ ρ`.  Taking `q = r - 2`
gives the requested source/target orders `(r, Pw)` and `(r - 2, Pw + 2)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.FixEq

variable {d : ℕ}

/-- The weighted jet energy on the spatial tail `jbracket x ≥ ρ`. -/
def fp81s21_weightedRellich_tailEnergy (q : ℕ) (P ρ : ℝ)
    (f : Euc d → ℝ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (q + 1), ∑ i : Fin j → Fin d,
    ∫⁻ x, if ρ ≤ jbracket x then
      ENNReal.ofReal (jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2)
    else 0

/-- Integrating over the tail, the target weight gains a factor `ρ⁻⁴`
in squared norm. -/
lemma fp81s21_weightedRellich_tailIntegral
    {q : ℕ} {P ρ : ℝ} (hρ : 1 ≤ ρ) (f : Euc d → ℝ)
    (i : Fin q → Fin d) :
    (∫⁻ x, if ρ ≤ jbracket x then
      ENNReal.ofReal (jbracket x ^ (-2 * (P + 2)) * (partialDeriv i f x) ^ 2)
    else 0) ≤
      ENNReal.ofReal (ρ ^ (-4 : ℝ)) *
        ∫⁻ x, ENNReal.ofReal (jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2) := by
  have hρpos : 0 < ρ := lt_of_lt_of_le (by norm_num) hρ
  have hcoef : 0 ≤ ρ ^ (-4 : ℝ) := Real.rpow_nonneg hρpos.le _
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (ρ ^ (-4 : ℝ)) *
        ENNReal.ofReal (jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2) := by
      apply lintegral_mono
      intro x
      by_cases hx : ρ ≤ jbracket x
      · simp only [hx, if_pos]
        calc
          ENNReal.ofReal
              (jbracket x ^ (-2 * (P + 2)) * (partialDeriv i f x) ^ 2)
              ≤ ENNReal.ofReal (ρ ^ (-4 : ℝ) *
                  (jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2)) :=
                ENNReal.ofReal_le_ofReal (by
                  calc
                    jbracket x ^ (-2 * (P + 2)) * (partialDeriv i f x) ^ 2
                        ≤ (ρ ^ (-4 : ℝ) * jbracket x ^ (-2 * P)) *
                            (partialDeriv i f x) ^ 2 :=
                          mul_le_mul_of_nonneg_right
                            (fp81s21_weightedRellich_tail_weight hρ hx)
                            (sq_nonneg _)
                    _ = ρ ^ (-4 : ℝ) *
                        (jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2) := by ring)
          _ = ENNReal.ofReal (ρ ^ (-4 : ℝ)) *
              ENNReal.ofReal (jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2) := by
                rw [ENNReal.ofReal_mul hcoef]
      · simp [hx]
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The tail contribution in the weak weighted norm is bounded by the
strong weighted jet energy with the explicit squared decay `ρ⁻⁴`.  Setting
`q = r - 2` gives exactly the pair `(r, Pw)` to `(r - 2, Pw + 2)`. -/
theorem fp81s21_weightedRellich_tailEnergy_le
    {q : ℕ} {P ρ : ℝ} (hρ : 1 ≤ ρ) (f : Euc d → ℝ) :
    fp81s21_weightedRellich_tailEnergy (d := d) q (P + 2) ρ f ≤
      ENNReal.ofReal (ρ ^ (-4 : ℝ)) * s57pS d (q + 2) P f := by
  calc
    _ ≤ ∑ j ∈ Finset.range (q + 1), ∑ i : Fin j → Fin d,
        ENNReal.ofReal (ρ ^ (-4 : ℝ)) *
          ∫⁻ x, ENNReal.ofReal (jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2) := by
      unfold fp81s21_weightedRellich_tailEnergy
      refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun i hi => ?_
      exact fp81s21_weightedRellich_tailIntegral hρ f i
    _ = ENNReal.ofReal (ρ ^ (-4 : ℝ)) *
        (∑ j ∈ Finset.range (q + 1), ∑ i : Fin j → Fin d,
          ∫⁻ x, ENNReal.ofReal (jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2)) := by
      calc
        _ = ∑ j ∈ Finset.range (q + 1), ENNReal.ofReal (ρ ^ (-4 : ℝ)) *
              (∑ i : Fin j → Fin d,
                ∫⁻ x, ENNReal.ofReal (jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2)) := by
            refine Finset.sum_congr rfl fun j hj => ?_
            rw [← Finset.univ.mul_sum]
        _ = _ := by rw [← Finset.mul_sum]
    _ ≤ ENNReal.ofReal (ρ ^ (-4 : ℝ)) * s57pS d (q + 2) P f := by
      calc
        _ = (∑ j ∈ Finset.range (q + 1), ∑ i : Fin j → Fin d,
              ∫⁻ x, ENNReal.ofReal (jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2)) *
              ENNReal.ofReal (ρ ^ (-4 : ℝ)) := mul_comm _ _
        _ ≤ s57pS d (q + 2) P f * ENNReal.ofReal (ρ ^ (-4 : ℝ)) := by
          apply mul_le_mul_left
          unfold s57pS
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.2 (by omega))
            (fun _ _ _ => bot_le)
        _ = _ := mul_comm _ _

#print axioms HRS.Fp81.S21.fp81s21_weightedRellich_tailIntegral
#print axioms HRS.Fp81.S21.fp81s21_weightedRellich_tailEnergy_le

end HRS.Fp81.S21
