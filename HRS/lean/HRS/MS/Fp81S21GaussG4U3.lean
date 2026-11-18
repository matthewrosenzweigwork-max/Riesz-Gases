import HRS.MS.S21F_D00
import HRS.MS.ProClosureS111ChartTrace
import HRS.MS.R26T6CD01

/-!
The S2.1(iii) G4 auxiliary cost is the square of the frozen weighted
Sobolev norm at order two and weight `2d + 4`.  The chart trace gives a
summable diagonal cost for the physical chart.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.FixEq HRS.MS.ProClosureS111

/-- The real squared weighted Sobolev cost used in the G4 chart trace. -/
def fp81s21_g4_J (d : ℕ) (f : Euc d → ℝ) : ℝ :=
  (weightedSobolevE 2 (2 * (d : ℝ) + 4) f).toReal ^ 2

private abbrev fp81s21_g4JetIndex (d : ℕ) :=
  Σ j : Fin 3, (Fin (j : ℕ) → Fin d)

private theorem fp81s21_g4_J_eq_s57pS (d : ℕ) (f : Euc d → ℝ) :
    fp81s21_g4_J d f =
      (HRS.MS.FixEq.s57pS d 2 (2 * (d : ℝ) + 4) f).toReal := by
  unfold fp81s21_g4_J
  rw [HRS.MS.FixEq.s57p_E_eq, ← ENNReal.toReal_rpow,
    ← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt (ENNReal.toReal_nonneg :
    0 ≤ (HRS.MS.FixEq.s57pS d 2 (2 * (d : ℝ) + 4) f).toReal)

private theorem fp81s21_g4_s57pS_as_jet_sum (d : ℕ) (P : ℝ)
    (f : Euc d → ℝ) :
    HRS.MS.FixEq.s57pS d 2 P f =
      ∑ a : fp81s21_g4JetIndex d,
        ∫⁻ x, ENNReal.ofReal
          (jbracket x ^ (-2 * P) * (partialDeriv a.2 f x) ^ 2) := by
  unfold HRS.MS.FixEq.s57pS fp81s21_g4JetIndex
  rw [← Fin.sum_univ_eq_sum_range
    (fun j : ℕ => ∑ i : Fin j → Fin d,
      ∫⁻ x, ENNReal.ofReal (jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2)) 3,
    Fintype.sum_sigma]

theorem fp81s21_g4_cost_trace (p : Parameters)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) :
    Summable (fun j => fp81s21_g4_J p.d (E.test j)) := by
  let P : ℝ := 2 * (p.d : ℝ) + 4
  let Pw : ℝ := (p.d : ℝ) + 2
  have hd0 : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
  have hP : (p.d : ℝ) < 2 * Pw := by
    dsimp [Pw]
    nlinarith
  have hr : (2 : ℝ) + (p.d : ℝ) / 2 < (2 * p.d + 8 : ℕ) := by
    push_cast
    nlinarith
  obtain ⟨C, hC, htrace⟩ :=
    physical_chart_partial_trace p.d (2 * p.d + 8) Pw hr hP
  have hWint : Integrable (s57pW p.d Pw) (volume : Measure (Euc p.d)) := by
    apply s57pW_integrable
    dsimp [Pw]
    nlinarith
  have hWcont : Continuous (s57pW p.d Pw) := by
    unfold s57pW
    apply Continuous.rpow_const
    · unfold jbracket
      fun_prop
    · intro x
      exact Or.inl (s57p_jbracket_pos x).ne'
  have hK0 : 0 ≤ C ^ 2 * ∫ x : Euc p.d, s57pW p.d Pw x :=
    mul_nonneg (sq_nonneg C) (integral_nonneg fun x => s57pW_nonneg Pw x)
  let K : ℝ := C ^ 2 * ∫ x : Euc p.d, s57pW p.d Pw x
  have hK : 0 ≤ K := hK0
  have hpow (x : Euc p.d) :
      s57pW p.d P x * jbracket x ^ (2 * Pw) = s57pW p.d Pw x := by
    unfold s57pW
    rw [← Real.rpow_add (s57p_jbracket_pos x)]
    congr 1
    dsimp [P, Pw]
    ring
  have hcoord (S : Finset ℕ) (a : fp81s21_g4JetIndex p.d) :
      (∑ n ∈ S, ∫⁻ x, ENNReal.ofReal
        (s57pW p.d P x * (partialDeriv a.2 (E.test n) x) ^ 2)) ≤
        ENNReal.ofReal K := by
    let j : ℕ := a.1
    have hj : j ≤ 2 := by
      dsimp [j]
      exact Nat.lt_succ_iff.mp a.1.isLt
    have hpart (n : ℕ) :
        Continuous (fun x : Euc p.d => partialDeriv a.2 (E.test n) x) := by
      have hreg : ContDiff ℝ 2 (E.test n) :=
        (E.test_smooth n).1.of_le (by norm_num)
      exact (s57p_partialDeriv_contDiff hreg 0 (by dsimp [j]; omega) a.2).continuous
    have hmeas (n : ℕ) : Measurable (fun x : Euc p.d =>
        ENNReal.ofReal (s57pW p.d P x *
          (partialDeriv a.2 (E.test n) x) ^ 2)) := by
      have hweight : Continuous (fun x : Euc p.d => s57pW p.d P x) := by
        unfold s57pW
        apply Continuous.rpow_const
        · unfold jbracket
          fun_prop
        · intro x
          exact Or.inl (s57p_jbracket_pos x).ne'
      exact ENNReal.measurable_ofReal.comp
        (hweight.mul ((hpart n).pow 2)).measurable
    have htraceX (x : Euc p.d) := htrace E j hj a.2 x
    have hsumX (x : Euc p.d) :
        (∑ n ∈ S, (partialDeriv a.2 (E.test n) x) ^ 2) ≤
          ∑' n, (partialDeriv a.2 (E.test n) x) ^ 2 := by
      simpa using (htraceX x).1.sum_le_tsum S
        (fun n _ => sq_nonneg (partialDeriv a.2 (E.test n) x))
    have hsumWeighted (x : Euc p.d) :
        (∑ n ∈ S, s57pW p.d P x *
          (partialDeriv a.2 (E.test n) x) ^ 2) ≤
          C ^ 2 * s57pW p.d Pw x := by
      calc
        _ = s57pW p.d P x *
            (∑ n ∈ S, (partialDeriv a.2 (E.test n) x) ^ 2) := by
              rw [Finset.mul_sum]
        _ ≤ s57pW p.d P x *
            (∑' n, (partialDeriv a.2 (E.test n) x) ^ 2) :=
              mul_le_mul_of_nonneg_left (hsumX x) (s57pW_nonneg P x)
        _ ≤ s57pW p.d P x *
            (C ^ 2 * jbracket x ^ (2 * Pw)) :=
              mul_le_mul_of_nonneg_left (htraceX x).2 (s57pW_nonneg P x)
        _ = C ^ 2 * s57pW p.d Pw x := by
              calc
                _ = C ^ 2 * (s57pW p.d P x * jbracket x ^ (2 * Pw)) := by ring
                _ = C ^ 2 * s57pW p.d Pw x := by rw [hpow]
    have hpoint (x : Euc p.d) :
        (∑ n ∈ S, ENNReal.ofReal
          (s57pW p.d P x * (partialDeriv a.2 (E.test n) x) ^ 2)) ≤
          ENNReal.ofReal (C ^ 2 * s57pW p.d Pw x) := by
      rw [← ENNReal.ofReal_sum_of_nonneg
        (fun n hn => mul_nonneg (s57pW_nonneg P x)
          (sq_nonneg (partialDeriv a.2 (E.test n) x)))]
      exact ENNReal.ofReal_le_ofReal (hsumWeighted x)
    calc
      _ = ∫⁻ x : Euc p.d, ∑ n ∈ S, ENNReal.ofReal
          (s57pW p.d P x * (partialDeriv a.2 (E.test n) x) ^ 2) := by
            symm
            exact lintegral_finsetSum S (fun n _ => hmeas n)
      _ ≤ ∫⁻ x : Euc p.d, ENNReal.ofReal (C ^ 2 * s57pW p.d Pw x) :=
            lintegral_mono hpoint
      _ = ENNReal.ofReal K := by
            rw [← ofReal_integral_eq_lintegral_ofReal (hWint.const_mul (C ^ 2))
              (Filter.Eventually.of_forall fun x =>
                mul_nonneg (sq_nonneg C) (s57pW_nonneg Pw x))]
            congr 1
            simp [K, integral_const_mul]
  have hSbound (S : Finset ℕ) :
      (∑ n ∈ S, HRS.MS.FixEq.s57pS p.d 2 P (E.test n)) ≤
        ENNReal.ofReal ((HRS.MS.FixEq.s57pN p.d 2 : ℝ) * K) := by
    have hcard : Fintype.card (fp81s21_g4JetIndex p.d) =
        HRS.MS.FixEq.s57pN p.d 2 := by
      simp only [fp81s21_g4JetIndex, Fintype.card_sigma, Fintype.card_fun,
        Fintype.card_fin]
      rw [Fin.sum_univ_eq_sum_range]
      rfl
    calc
      _ = ∑ a : fp81s21_g4JetIndex p.d,
          ∑ n ∈ S, ∫⁻ x, ENNReal.ofReal
            (s57pW p.d P x * (partialDeriv a.2 (E.test n) x) ^ 2) := by
              simp_rw [fp81s21_g4_s57pS_as_jet_sum]
              rw [Finset.sum_comm]
              simp only [s57pW]
      _ ≤ ∑ _a : fp81s21_g4JetIndex p.d, ENNReal.ofReal K :=
            Finset.sum_le_sum fun a _ => hcoord S a
      _ = ENNReal.ofReal ((HRS.MS.FixEq.s57pN p.d 2 : ℝ) * K) := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcard]
            rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
            simp
  have hJsum (S : Finset ℕ) :
      (∑ n ∈ S, fp81s21_g4_J p.d (E.test n)) ≤
        (HRS.MS.FixEq.s57pN p.d 2 : ℝ) * K := by
    have hfinite : ∀ n ∈ S,
        HRS.MS.FixEq.s57pS p.d 2 P (E.test n) ≠ ⊤ := by
      intro n hn
      have hsingle : HRS.MS.FixEq.s57pS p.d 2 P (E.test n) ≤
          ∑ n ∈ S, HRS.MS.FixEq.s57pS p.d 2 P (E.test n) :=
        Finset.single_le_sum
          (f := fun m => HRS.MS.FixEq.s57pS p.d 2 P (E.test m))
          (fun _ _ => zero_le) hn
      exact ne_of_lt (lt_of_le_of_lt (hsingle.trans (hSbound S)) ENNReal.ofReal_lt_top)
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hSbound S)
    rw [ENNReal.toReal_ofReal (mul_nonneg
      (Nat.cast_nonneg _) hK)] at hreal
    calc
      _ = (∑ n ∈ S, HRS.MS.FixEq.s57pS p.d 2 P (E.test n)).toReal := by
            simp_rw [fp81s21_g4_J_eq_s57pS]
            rw [ENNReal.toReal_sum hfinite]
      _ ≤ (HRS.MS.FixEq.s57pN p.d 2 : ℝ) * K := hreal
  have hJnonneg : ∀ n, 0 ≤ fp81s21_g4_J p.d (E.test n) :=
    fun n => sq_nonneg _
  exact summable_of_sum_le hJnonneg hJsum

#print axioms fp81s21_g4_cost_trace

end HRS.Fp81.S21

