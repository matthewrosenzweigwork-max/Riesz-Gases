import HRS.Energy.PressureDV
import HRS.Energy.Modulated

/-!
# Packet Q40b, part 1: Hoeffding + Donsker–Varadhan for the empirical average

`q40b_dv_sqrt`: if `f` is a probability law on `Config d N` with `H(f | ν^{⊗N}) ≤ H` then
`E_f |N⁻¹ ∑ b(x_i) - ν(b)| ≤ ‖b‖_∞ √(2 (H + log 2)/N)`
(TeX `P:eq:linear-input`: Hoeffding's lemma, Mathlib `HasSubgaussianMGF`, then `dv_lintegral`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section
namespace HRS.Q40b

variable {d N : ℕ}

theorem q40b_subG_empirical (ν : Measure (Torus d)) [IsProbabilityMeasure ν] {b : Torus d → ℝ}
    (hb : Measurable b) {B : ℝ} (hB : ∀ x, |b x| ≤ B) :
    HasSubgaussianMGF (fun x : Config d N => ∑ i, (b (x i) - ∫ y, b y ∂ν))
      (∑ _i : Fin N, ((‖(B - ∫ y, b y ∂ν) - (-B - ∫ y, b y ∂ν)‖₊ / 2) ^ 2))
      (Measure.pi fun _ : Fin N => ν) := by
  have hint : Integrable b ν := Integrable.of_bound hb.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x => by simpa using hB x)
  have hindep : iIndepFun (fun (i : Fin N) (x : Config d N) => b (x i) - ∫ y, b y ∂ν)
      (Measure.pi fun _ : Fin N => ν) :=
    iIndepFun_pi (μ := fun _ : Fin N => ν) (X := fun _ y => b y - ∫ y, b y ∂ν)
      (fun i => (hb.sub_const _).aemeasurable)
  refine HasSubgaussianMGF.sum_of_iIndepFun hindep (s := Finset.univ) (c := fun _ => ((‖(B - ∫ y, b y ∂ν) - (-B - ∫ y, b y ∂ν)‖₊ / 2) ^ 2)) ?_
  intro i _
  refine hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (a := -B - ∫ y, b y ∂ν) (b := B - ∫ y, b y ∂ν) ?_ ?_ ?_
  · exact ((hb.comp (measurable_pi_apply i)).sub_const _).aemeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    have := abs_le.1 (hB (x i))
    constructor <;> linarith [this.1, this.2]
  · have hm : MeasurePreserving (fun x : Config d N => x i) (Measure.pi fun _ : Fin N => ν) ν :=
      measurePreserving_eval (fun _ : Fin N => ν) i
    have : ∫ x, (b (x i) - ∫ y, b y ∂ν) ∂(Measure.pi fun _ : Fin N => ν) = ∫ y, (b y - ∫ y, b y ∂ν) ∂ν := by
      have h1 := integral_map (μ := (Measure.pi fun _ : Fin N => ν)) (φ := fun x : Config d N => x i)
        (f := fun y => b y - ∫ y, b y ∂ν) (measurable_pi_apply i).aemeasurable
        ((hb.sub_const _).aestronglyMeasurable)
      rw [hm.map_eq] at h1
      exact h1.symm
    rw [this, integral_sub hint (integrable_const _)]
    simp


/-- The empirical average deviation `Y(x) = N⁻¹ ∑ b(x_i) - ν(b)`. -/
def q40bY (ν : Measure (Torus d)) (b : Torus d → ℝ) (x : Config d N) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, b (x i) - ∫ y, b y ∂ν

theorem q40b_mgf_Y (ν : Measure (Torus d)) [IsProbabilityMeasure ν] {b : Torus d → ℝ}
    (hb : Measurable b) {B : ℝ} (hB : ∀ x, |b x| ≤ B) (hN : 0 < N) (z : ℝ) :
    Integrable (fun x : Config d N => Real.exp (z * q40bY ν b x)) (Measure.pi fun _ : Fin N => ν) ∧
    ∫ x, Real.exp (z * q40bY ν b x) ∂(Measure.pi fun _ : Fin N => ν) ≤
      Real.exp (z ^ 2 * B ^ 2 / (2 * N)) := by
  have hS := q40b_subG_empirical (N := N) ν hb hB
  have hYS : ∀ x : Config d N, q40bY ν b x = (1 / (N : ℝ)) * ∑ i, (b (x i) - ∫ y, b y ∂ν) := by
    intro x
    unfold q40bY
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (N : ℝ) ≠ 0 := by positivity
    field_simp
  have hz : ∀ x : Config d N, z * q40bY ν b x = (z / N) * ∑ i, (b (x i) - ∫ y, b y ∂ν) := by
    intro x; rw [hYS]; ring
  simp_rw [hz]
  refine ⟨hS.integrable_exp_mul _, ?_⟩
  have h1 := hS.mgf_le (z / N)
  unfold mgf at h1
  refine h1.trans (le_of_eq ?_)
  congr 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h2 : ‖B - ∫ y, b y ∂ν - (-B - ∫ y, b y ∂ν)‖ = 2 * |B| := by
    rw [show B - ∫ y, b y ∂ν - (-B - ∫ y, b y ∂ν) = 2 * B by ring, Real.norm_eq_abs, abs_mul]
    norm_num
  have hNn : (N : ℝ) ≠ 0 := by positivity
  push_cast
  rw [h2]
  have : |B| ^ 2 = B ^ 2 := sq_abs B
  field_simp
  rw [this]
  ring


theorem q40b_measurable_Y (ν : Measure (Torus d)) {b : Torus d → ℝ} (hb : Measurable b) :
    Measurable (q40bY (N := N) ν b) := by
  unfold q40bY
  refine Measurable.sub (Measurable.const_mul ?_ _) measurable_const
  exact Finset.measurable_sum _ fun i _ => hb.comp (measurable_pi_apply i)

theorem q40b_abs_Y_le (ν : Measure (Torus d)) [IsProbabilityMeasure ν] {b : Torus d → ℝ}
    (hb : Measurable b) {B : ℝ} (hB : ∀ x, |b x| ≤ B) (hN : 0 < N) (x : Config d N) :
    |q40bY ν b x| ≤ 2 * B := by
  unfold q40bY
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (x ⟨0, hN⟩))
  have h1 : |(1 / (N : ℝ)) * ∑ i, b (x i)| ≤ B := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / N)]
    have : |∑ i, b (x i)| ≤ N * B := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i, |b (x i)| ≤ ∑ _i : Fin N, B := Finset.sum_le_sum fun i _ => hB _
        _ = N * B := by simp
    calc 1 / (N : ℝ) * |∑ i, b (x i)| ≤ 1 / (N : ℝ) * (N * B) := by gcongr
      _ = B := by field_simp
  have h2 : |∫ y, b y ∂ν| ≤ B := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := B) (Filter.Eventually.of_forall fun y => ?_)).trans ?_
    · simpa using hB y
    · simp
  calc |(1 / (N : ℝ)) * ∑ i, b (x i) - ∫ y, b y ∂ν|
      ≤ |(1 / (N : ℝ)) * ∑ i, b (x i)| + |∫ y, b y ∂ν| := abs_sub _ _
    _ ≤ 2 * B := by linarith

theorem q40b_dv_lambda (ν : Measure (Torus d)) [IsProbabilityMeasure ν]
    (f : Measure (Config d N)) [IsProbabilityMeasure f] {b : Torus d → ℝ}
    (hb : Measurable b) {B : ℝ} (hB : ∀ x, |b x| ≤ B) (hN : 0 < N) {H : ℝ} (hH0 : 0 ≤ H)
    (hKL : InformationTheory.klDiv f (Measure.pi fun _ : Fin N => ν) ≤ ENNReal.ofReal H)
    {lam : ℝ} (hlam : 0 < lam) :
    lam * ∫ x, |q40bY ν b x| ∂f ≤ H + Real.log 2 + lam ^ 2 * B ^ 2 / (2 * N) := by
  set Q : Measure (Config d N) := Measure.pi fun _ : Fin N => ν with hQ
  have hY := q40b_measurable_Y (N := N) ν hb
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (Classical.arbitrary _))
  set K : ℝ := Real.log 2 + lam ^ 2 * B ^ 2 / (2 * N) with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have : 0 ≤ lam ^ 2 * B ^ 2 / (2 * N) := by positivity
    linarith
  have hmgf1 := q40b_mgf_Y (N := N) ν hb hB hN lam
  have hmgf2 := q40b_mgf_Y (N := N) ν hb hB hN (-lam)
  have hZ : ∫⁻ x : Config d N, ENNReal.ofReal (Real.exp (lam * |q40bY ν b x|)) ∂Q ≤
      ENNReal.ofReal (Real.exp K) := by
    have hpt : ∀ x : Config d N, ENNReal.ofReal (Real.exp (lam * |q40bY ν b x|)) ≤
        ENNReal.ofReal (Real.exp (lam * q40bY ν b x)) +
          ENNReal.ofReal (Real.exp ((-lam) * q40bY ν b x)) := by
      intro x
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
      refine ENNReal.ofReal_le_ofReal ?_
      rcases abs_cases (q40bY ν b x) with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]
        have := Real.exp_pos ((-lam) * q40bY ν b x)
        linarith
      · rw [h]
        have e : lam * -q40bY ν b x = (-lam) * q40bY ν b x := by ring
        rw [e]
        have := Real.exp_pos (lam * q40bY ν b x)
        linarith
    calc ∫⁻ x : Config d N, ENNReal.ofReal (Real.exp (lam * |q40bY ν b x|)) ∂Q
        ≤ ∫⁻ x : Config d N, (ENNReal.ofReal (Real.exp (lam * q40bY ν b x)) +
          ENNReal.ofReal (Real.exp ((-lam) * q40bY ν b x))) ∂Q := lintegral_mono hpt
      _ = ENNReal.ofReal (∫ x, Real.exp (lam * q40bY ν b x) ∂Q) +
          ENNReal.ofReal (∫ x, Real.exp ((-lam) * q40bY ν b x) ∂Q) := by
        rw [lintegral_add_left (by fun_prop),
          ofReal_integral_eq_lintegral_ofReal hmgf1.1 (Filter.Eventually.of_forall fun x : Config d N => (Real.exp_pos _).le),
          ofReal_integral_eq_lintegral_ofReal hmgf2.1 (Filter.Eventually.of_forall fun x : Config d N => (Real.exp_pos _).le)]
      _ ≤ ENNReal.ofReal (Real.exp (lam ^ 2 * B ^ 2 / (2 * N))) +
          ENNReal.ofReal (Real.exp (lam ^ 2 * B ^ 2 / (2 * N))) := by
        have e : (-lam) ^ 2 = lam ^ 2 := by ring
        have h2 := hmgf2.2
        rw [e] at h2
        gcongr
        · exact hmgf1.2.trans (le_of_eq (by ring_nf))
      _ = ENNReal.ofReal (Real.exp K) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le, hK, Real.exp_add,
          Real.exp_log (by norm_num)]
        congr 1; ring
  have hDV := dv_lintegral Q f (le_top.trans_lt' (lt_of_le_of_lt hKL ENNReal.ofReal_lt_top) |>.ne)
    (F := fun x : Config d N => lam * |q40bY ν b x|) (by fun_prop) (fun x => by positivity) hK0 hZ
  have h1 : ∫⁻ x, ENNReal.ofReal (lam * |q40bY ν b x|) ∂f ≤ ENNReal.ofReal H + ENNReal.ofReal K :=
    hDV.trans (add_le_add hKL le_rfl)
  have hint : Integrable (fun x : Config d N => lam * |q40bY ν b x|) f :=
    Integrable.of_bound (C := lam * (2 * B)) (by fun_prop)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (q40b_abs_Y_le ν hb hB hN x) hlam.le)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => by positivity),
    ← ENNReal.ofReal_add hH0 hK0, ENNReal.ofReal_le_ofReal_iff (by linarith)] at h1
  rw [integral_const_mul] at h1
  rw [hK] at h1
  linarith

theorem q40b_dv_sqrt (ν : Measure (Torus d)) [IsProbabilityMeasure ν]
    (f : Measure (Config d N)) [IsProbabilityMeasure f] {b : Torus d → ℝ}
    (hb : Measurable b) {B : ℝ} (hB : ∀ x, |b x| ≤ B) (hN : 0 < N) {H : ℝ} (hH0 : 0 ≤ H)
    (hKL : InformationTheory.klDiv f (Measure.pi fun _ : Fin N => ν) ≤ ENNReal.ofReal H) :
    ∫ x, |q40bY ν b x| ∂f ≤ B * Real.sqrt (2 * (H + Real.log 2) / N) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (Classical.arbitrary _))
  have hI0 : 0 ≤ ∫ x, |q40bY ν b x| ∂f := integral_nonneg fun x => abs_nonneg _
  rcases hB0.eq_or_lt with h0 | hBpos
  · subst h0
    have : ∀ x : Config d N, q40bY ν b x = 0 := fun x => by
      have := q40b_abs_Y_le ν hb hB hN x
      have h2 := abs_nonneg (q40bY ν b x)
      exact abs_eq_zero.1 (le_antisymm (by linarith) h2)
    simp [this]
  · have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    set A : ℝ := H + Real.log 2 with hA
    have hApos : 0 < A := by linarith
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    set r : ℝ := Real.sqrt (2 * N * A) with hr
    have hrpos : 0 < r := Real.sqrt_pos.2 (by positivity)
    have hr2 : r ^ 2 = 2 * N * A := Real.sq_sqrt (by positivity)
    have hlam : 0 < r / B := by positivity
    have h1 := q40b_dv_lambda ν f hb hB hN hH0 hKL hlam
    have e : (r / B) ^ 2 * B ^ 2 / (2 * N) = A := by
      rw [div_pow, div_mul_cancel₀ _ (by positivity), hr2]
      field_simp
    rw [e] at h1
    have h2 : (r / B) * ∫ x, |q40bY ν b x| ∂f ≤ 2 * A := by linarith
    have h3 : ∫ x, |q40bY ν b x| ∂f ≤ 2 * A / (r / B) := by
      rw [le_div_iff₀ hlam]; linarith
    refine h3.trans (le_of_eq ?_)
    have hs : Real.sqrt (2 * A / N) = 2 * A / r := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
      field_simp
      nlinarith [hr2]
    rw [show 2 * (H + Real.log 2) / N = 2 * A / N from rfl, hs]
    field_simp

end HRS.Q40b