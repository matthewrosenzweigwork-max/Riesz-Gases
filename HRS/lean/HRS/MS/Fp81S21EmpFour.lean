import HRS.MS.Fp81S21GaussMomRep10

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- Fourth increment control for a coefficient-valued process, with the
constant fixed after the horizon. -/
def fp81s21_Inc4 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (q : ℝ → Ω → r26t6_Coeff) (H C : ℝ) : Prop :=
  ∀ a : ℝ, 0 ≤ a → ∀ s t : Icc (0 : ℝ) H,
    MemLp (fun ω => q (a + t) ω - q (a + s) ω) 4 P ∧
    (∫ ω, ‖q (a + t) ω - q (a + s) ω‖ ^ 4 ∂P) ≤ C * |(t : ℝ) - s| ^ 2

/-- The vector drift in the empirical coefficient equation. -/
def fp81s21_empFour_drift {Ω : Type*} [MeasurableSpace Ω] (N : ℕ)
    (L : ℝ → r26t6_Coeff →L[ℝ] r26t6_Coeff)
    (qs qB0 : ℝ → Ω → r26t6_Coeff) (u : ℝ) (ω : Ω) : r26t6_Coeff :=
  L u (qs u ω) - (Real.sqrt (N : ℝ))⁻¹ • qB0 u ω

private theorem fp81s21_empFour_norm_add_fourth
    {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x + y‖ ^ 4 ≤ 8 * (‖x‖ ^ 4 + ‖y‖ ^ 4) := by
  calc
    ‖x + y‖ ^ 4 ≤ (‖x‖ + ‖y‖) ^ 4 := by
      gcongr
      exact norm_add_le x y
    _ ≤ (2 : ℝ) ^ 3 * (‖x‖ ^ 4 + ‖y‖ ^ 4) :=
      add_pow_le (norm_nonneg x) (norm_nonneg y) 4
    _ = 8 * (‖x‖ ^ 4 + ‖y‖ ^ 4) := by norm_num

/-- B6-ii plus a fourth-moment bound for the time-integrated drift and B7's
martingale bound imply the empirical fourth-increment estimate.  The explicit
`hB6ii` premise is the final simultaneous vector equation; `hDrift` is the
remaining analytic drift estimate needed before this bridge can yield B8. -/
theorem fp81s21_empirical_fourth_increments_from_components
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) (N : ℕ)
    (A : Particle R N)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (qs qB0 m : ℝ → A.Ω → r26t6_Coeff)
    (L : ℝ → r26t6_Coeff →L[ℝ] r26t6_Coeff)
    (CD Cm : ℝ) (hCD : 0 ≤ CD) (hCm : 0 ≤ Cm)
    (hB6ii : ∀ a : ℝ, 0 ≤ a → ∀ H : ℝ, 0 < H →
      ∀ᵐ ω ∂A.P, ∀ s t : Icc (0 : ℝ) H, s ≤ t →
        fp81s21_gaussian_chartEmbed p Es E (qs (a + t) ω) -
          fp81s21_gaussian_chartEmbed p Es E (qs (a + s) ω) =
        (∫ v in Icc (s : ℝ) (t : ℝ),
          fp81s21_empFour_drift N L qs qB0 (a + v) ω) +
          (m (a + t) ω - m (a + s) ω))
    (hDrift : ∀ H : ℝ, 0 < H → ∀ a : ℝ, 0 ≤ a →
      ∀ s t : Icc (0 : ℝ) H, s ≤ t →
        MemLp (fun ω => ∫ v in Icc (s : ℝ) (t : ℝ),
          fp81s21_empFour_drift N L qs qB0 (a + v) ω) 4 A.P ∧
        (∫ ω, ‖∫ v in Icc (s : ℝ) (t : ℝ),
          fp81s21_empFour_drift N L qs qB0 (a + v) ω‖ ^ 4 ∂A.P) ≤
          CD * |(t : ℝ) - s| ^ 4)
    (hB7 : ∀ H : ℝ, 0 < H → ∀ a : ℝ, 0 ≤ a →
      ∀ s t : Icc (0 : ℝ) H,
        MemLp (fun ω => m (a + t) ω - m (a + s) ω) 4 A.P ∧
        (∫ ω, ‖m (a + t) ω - m (a + s) ω‖ ^ 4 ∂A.P) ≤
          Cm * |(t : ℝ) - s| ^ 2) :
    ∀ H : ℝ, 0 < H →
      fp81s21_Inc4 A.P
        (fun u ω => fp81s21_gaussian_chartEmbed p Es E (qs u ω)) H
        (8 * (CD * H ^ 2 + Cm)) := by
  intro H hH
  change ∀ a : ℝ, 0 ≤ a → ∀ s t : Icc (0 : ℝ) H,
    MemLp (fun ω => fp81s21_gaussian_chartEmbed p Es E (qs (a + t) ω) -
      fp81s21_gaussian_chartEmbed p Es E (qs (a + s) ω)) 4 A.P ∧
    (∫ ω, ‖fp81s21_gaussian_chartEmbed p Es E (qs (a + t) ω) -
      fp81s21_gaussian_chartEmbed p Es E (qs (a + s) ω)‖ ^ 4 ∂A.P) ≤
      8 * (CD * H ^ 2 + Cm) * |(t : ℝ) - s| ^ 2
  intro a ha s t
  have hordered : ∀ s t : Icc (0 : ℝ) H, s ≤ t →
      MemLp (fun ω =>
        fp81s21_gaussian_chartEmbed p Es E (qs (a + t) ω) -
          fp81s21_gaussian_chartEmbed p Es E (qs (a + s) ω)) 4 A.P ∧
      (∫ ω, ‖fp81s21_gaussian_chartEmbed p Es E (qs (a + t) ω) -
        fp81s21_gaussian_chartEmbed p Es E (qs (a + s) ω)‖ ^ 4 ∂A.P) ≤
        8 * (CD * H ^ 2 + Cm) * |(t : ℝ) - s| ^ 2 := by
    intro s t hst
    have hD := hDrift H hH a ha s t hst
    have hM := hB7 H hH a ha s t
    have hEq : (fun ω =>
        fp81s21_gaussian_chartEmbed p Es E (qs (a + t) ω) -
          fp81s21_gaussian_chartEmbed p Es E (qs (a + s) ω)) =ᵐ[A.P]
        (fun ω => (∫ v in Icc (s : ℝ) (t : ℝ),
          fp81s21_empFour_drift N L qs qB0 (a + v) ω) +
          (m (a + t) ω - m (a + s) ω)) := by
      filter_upwards [hB6ii a ha H hH] with ω hω
      exact hω s t hst
    have hsum : MemLp (fun ω =>
        (∫ v in Icc (s : ℝ) (t : ℝ),
          fp81s21_empFour_drift N L qs qB0 (a + v) ω) +
          (m (a + t) ω - m (a + s) ω)) 4 A.P := hD.1.add hM.1
    have hmem : MemLp (fun ω =>
        fp81s21_gaussian_chartEmbed p Es E (qs (a + t) ω) -
          fp81s21_gaussian_chartEmbed p Es E (qs (a + s) ω)) 4 A.P :=
      (memLp_congr_ae hEq).2 hsum
    have hsumInt : Integrable (fun ω => ‖
        (∫ v in Icc (s : ℝ) (t : ℝ),
          fp81s21_empFour_drift N L qs qB0 (a + v) ω) +
          (m (a + t) ω - m (a + s) ω)‖ ^ 4) A.P :=
      hsum.integrable_norm_pow (by norm_num)
    have hrightInt : Integrable (fun ω => 8 * (
        ‖∫ v in Icc (s : ℝ) (t : ℝ),
          fp81s21_empFour_drift N L qs qB0 (a + v) ω‖ ^ 4 +
        ‖m (a + t) ω - m (a + s) ω‖ ^ 4)) A.P := by
      have hbase := (hD.1.integrable_norm_pow (by norm_num)).add
        (hM.1.integrable_norm_pow (by norm_num))
      exact hbase.const_mul 8
    have hpoint : ∀ ω, ‖
        (∫ v in Icc (s : ℝ) (t : ℝ),
          fp81s21_empFour_drift N L qs qB0 (a + v) ω) +
          (m (a + t) ω - m (a + s) ω)‖ ^ 4 ≤
        8 * (‖∫ v in Icc (s : ℝ) (t : ℝ),
          fp81s21_empFour_drift N L qs qB0 (a + v) ω‖ ^ 4 +
          ‖m (a + t) ω - m (a + s) ω‖ ^ 4) := by
      intro ω
      exact fp81s21_empFour_norm_add_fourth _ _
    have hsumBound : (∫ ω, ‖
        (∫ v in Icc (s : ℝ) (t : ℝ),
          fp81s21_empFour_drift N L qs qB0 (a + v) ω) +
          (m (a + t) ω - m (a + s) ω)‖ ^ 4 ∂A.P) ≤
        8 * (CD * |(t : ℝ) - s| ^ 4 + Cm * |(t : ℝ) - s| ^ 2) := by
      calc
        _ ≤ ∫ ω, 8 * (‖∫ v in Icc (s : ℝ) (t : ℝ),
            fp81s21_empFour_drift N L qs qB0 (a + v) ω‖ ^ 4 +
            ‖m (a + t) ω - m (a + s) ω‖ ^ 4) ∂A.P :=
          integral_mono_ae hsumInt hrightInt (Filter.Eventually.of_forall hpoint)
        _ = 8 * ((∫ ω, ‖∫ v in Icc (s : ℝ) (t : ℝ),
            fp81s21_empFour_drift N L qs qB0 (a + v) ω‖ ^ 4 ∂A.P) +
            (∫ ω, ‖m (a + t) ω - m (a + s) ω‖ ^ 4 ∂A.P)) := by
          rw [integral_const_mul]
          congr 1
          exact integral_add (hD.1.integrable_norm_pow (by norm_num))
            (hM.1.integrable_norm_pow (by norm_num))
        _ ≤ _ := by
          exact mul_le_mul_of_nonneg_left (add_le_add hD.2 hM.2) (by norm_num)
    have hell : |(t : ℝ) - s| ≤ H := by
      rw [abs_le]
      constructor <;> linarith [s.property.1, s.property.2, t.property.1, t.property.2]
    have hpow : |(t : ℝ) - s| ^ 4 ≤ H ^ 2 * |(t : ℝ) - s| ^ 2 := by
      have hsq : |(t : ℝ) - s| ^ 2 ≤ H ^ 2 := by
        exact (sq_le_sq₀ (abs_nonneg _) hH.le).2 hell
      calc
        |(t : ℝ) - s| ^ 4 = |(t : ℝ) - s| ^ 2 * |(t : ℝ) - s| ^ 2 := by ring
        _ ≤ H ^ 2 * |(t : ℝ) - s| ^ 2 :=
          mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    have hfinal : 8 * (CD * |(t : ℝ) - s| ^ 4 + Cm * |(t : ℝ) - s| ^ 2) ≤
        8 * (CD * H ^ 2 + Cm) * |(t : ℝ) - s| ^ 2 := by
      have hlen : 0 ≤ |(t : ℝ) - s| ^ 2 := sq_nonneg _
      calc
        _ ≤ 8 * (CD * (H ^ 2 * |(t : ℝ) - s| ^ 2) +
            Cm * |(t : ℝ) - s| ^ 2) := by gcongr
        _ = _ := by ring
    refine ⟨hmem, ?_⟩
    calc
      _ = ∫ ω, ‖(∫ v in Icc (s : ℝ) (t : ℝ),
          fp81s21_empFour_drift N L qs qB0 (a + v) ω) +
          (m (a + t) ω - m (a + s) ω)‖ ^ 4 ∂A.P := by
        apply integral_congr_ae
        filter_upwards [hEq] with ω hω
        rw [hω]
      _ ≤ 8 * (CD * |(t : ℝ) - s| ^ 4 + Cm * |(t : ℝ) - s| ^ 2) := hsumBound
      _ ≤ 8 * (CD * H ^ 2 + Cm) * |(t : ℝ) - s| ^ 2 := hfinal
  by_cases hst : (s : ℝ) ≤ t
  · exact hordered s t hst
  · have hts : (t : ℝ) ≤ s := le_of_lt (lt_of_not_ge hst)
    have hrev := hordered t s hts
    have hnegEq : (fun ω =>
        fp81s21_gaussian_chartEmbed p Es E (qs (a + t) ω) -
          fp81s21_gaussian_chartEmbed p Es E (qs (a + s) ω)) =ᵐ[A.P]
        (fun ω => -(fp81s21_gaussian_chartEmbed p Es E (qs (a + s) ω) -
          fp81s21_gaussian_chartEmbed p Es E (qs (a + t) ω))) := by
      filter_upwards [] with ω
      abel
    have hmem : MemLp (fun ω =>
        fp81s21_gaussian_chartEmbed p Es E (qs (a + t) ω) -
          fp81s21_gaussian_chartEmbed p Es E (qs (a + s) ω)) 4 A.P := by
      exact (memLp_congr_ae hnegEq).2 hrev.1.neg
    have hmoment : (∫ ω, ‖
        fp81s21_gaussian_chartEmbed p Es E (qs (a + t) ω) -
          fp81s21_gaussian_chartEmbed p Es E (qs (a + s) ω)‖ ^ 4 ∂A.P) =
        (∫ ω, ‖fp81s21_gaussian_chartEmbed p Es E (qs (a + s) ω) -
          fp81s21_gaussian_chartEmbed p Es E (qs (a + t) ω)‖ ^ 4 ∂A.P) := by
      apply integral_congr_ae
      filter_upwards [] with ω
      simp [norm_sub_rev]
    refine ⟨hmem, ?_⟩
    rw [hmoment]
    have hlen : |(t : ℝ) - s| = |(s : ℝ) - t| := abs_sub_comm _ _
    simpa [hlen] using hrev.2

#print axioms HRS.Fp81.S21.fp81s21_empirical_fourth_increments_from_components

end HRS.Fp81.S21
