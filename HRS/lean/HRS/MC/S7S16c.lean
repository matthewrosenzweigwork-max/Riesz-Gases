import HRS.MC.Sec7Vocab

/-!
# Packet `s7_S16c_ratio_slope`: the scalar tilt algebra (variance positivity, slope, Lipschitz bound)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S16c

open HRS HRS.Sec7 HRS.MC.SEdge HRS.MC.Sec7

/-- the Gaussian-bump observable -/
def s7c_v (z : EuclideanSpace ℝ (Fin 2)) : ℝ := Real.exp (-‖z‖ ^ 2)

theorem s7c_v_cont : Continuous s7c_v := by
  unfold s7c_v; fun_prop

theorem s7c_v_pos (z : EuclideanSpace ℝ (Fin 2)) : 0 < s7c_v z := Real.exp_pos _

theorem s7c_v_le (z : EuclideanSpace ℝ (Fin 2)) : s7c_v z ≤ 1 := by
  unfold s7c_v
  rw [Real.exp_le_one_iff]
  nlinarith [sq_nonneg ‖z‖]

theorem s7c_int_pow_le (ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure ν] (n : ℕ) :
    Integrable (fun z => s7c_v z ^ n) ν := by
  refine Integrable.of_bound (C := 1) ((s7c_v_cont.pow n).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun z => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (s7c_v_pos z).le n)]
  exact pow_le_one₀ (s7c_v_pos z).le (s7c_v_le z)

/-- the variance identity and positivity -/
theorem s7c_var_pos (ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure ν]
    (hfull : ∀ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U → U.Nonempty → 0 < ν U) :
    0 < (∫ z, s7c_v z ^ 2 ∂ν) - (∫ z, s7c_v z ∂ν) ^ 2 := by
  set m₁ := ∫ z, s7c_v z ∂ν with hm₁
  have h1 : Integrable s7c_v ν := by simpa using s7c_int_pow_le ν 1
  have h2 : Integrable (fun z => s7c_v z ^ 2) ν := s7c_int_pow_le ν 2
  have hid : ∫ z, (s7c_v z - m₁) ^ 2 ∂ν = (∫ z, s7c_v z ^ 2 ∂ν) - m₁ ^ 2 := by
    have : (fun z => (s7c_v z - m₁) ^ 2) =
        fun z => (s7c_v z ^ 2 - 2 * m₁ * s7c_v z) + m₁ ^ 2 := by
      funext z; ring
    have hA : Integrable (fun z => s7c_v z ^ 2 - 2 * m₁ * s7c_v z) ν := h2.sub (h1.const_mul _)
    rw [this, integral_add hA (integrable_const _),
      integral_sub h2 (h1.const_mul _), integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rw [← hm₁]; ring
  rw [← hid]
  have hcont : Continuous (fun z => (s7c_v z - m₁) ^ 2) := (s7c_v_cont.sub continuous_const).pow 2
  have hint : Integrable (fun z => (s7c_v z - m₁) ^ 2) ν := by
    have : (fun z => (s7c_v z - m₁) ^ 2) =
        fun z => (s7c_v z ^ 2 - 2 * m₁ * s7c_v z) + m₁ ^ 2 := by
      funext z; ring
    rw [this]
    exact (h2.sub (h1.const_mul _)).add (integrable_const _)
  rw [integral_pos_iff_support_of_nonneg (fun z => sq_nonneg _) hint]
  have hopen : IsOpen (Function.support fun z => (s7c_v z - m₁) ^ 2) :=
    hcont.isOpen_support
  refine hfull _ hopen ?_
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hz : ∀ z, (s7c_v z - m₁) ^ 2 = 0 := by
    intro z
    by_contra h
    have : z ∈ Function.support fun z => (s7c_v z - m₁) ^ 2 := h
    rw [hne] at this; exact this
  have a0 := hz 0
  have a1 := hz (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
  have e0 : s7c_v 0 = 1 := by simp [s7c_v]
  have e1 : s7c_v (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) = Real.exp (-1) := by
    simp [s7c_v]
  rw [e0] at a0
  rw [e1] at a1
  have b0 : m₁ = 1 := by nlinarith [sq_nonneg (1 - m₁)]
  have b1 : Real.exp (-1) = m₁ := by nlinarith [sq_nonneg (Real.exp (-1) - m₁)]
  have : Real.exp (-1) < 1 := by
    exact Real.exp_lt_one_iff.2 (by norm_num)
  linarith


theorem s7c_int_nonneg (ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure ν] (n : ℕ) :
    0 ≤ ∫ z, s7c_v z ^ n ∂ν :=
  integral_nonneg fun z => pow_nonneg (s7c_v_pos z).le n

theorem s7c_int_le_one (ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure ν] (n : ℕ) :
    ∫ z, s7c_v z ^ n ∂ν ≤ 1 := by
  have := integral_mono (s7c_int_pow_le ν n) (integrable_const (1 : ℝ))
    (fun z => pow_le_one₀ ((s7c_v_pos z).le) (s7c_v_le z))
  simpa using this

/-- slope algebra -/
theorem s7c_slope {ε m₁ m₂ a : ℝ} (hε : 0 < ε) (h1 : 0 ≤ m₁) (h1' : m₁ ≤ 1)
    (hD : 0 < m₂ - m₁ ^ 2) (ha : 0 < a) (ha1 : a < 1) :
    (m₁ + (ε + a) * m₂) / (1 + (ε + a) * m₁) - (m₁ + (ε + 0) * m₂) / (1 + (ε + 0) * m₁) ≥
      2 * ((m₂ - m₁ ^ 2) / (2 * ((2 + ε) * (1 + ε)))) * a := by
  have hA : 0 < 1 + (ε + a) * m₁ := by positivity
  have hB : 0 < 1 + (ε + 0) * m₁ := by positivity
  have key : (m₁ + (ε + a) * m₂) / (1 + (ε + a) * m₁) - (m₁ + (ε + 0) * m₂) / (1 + (ε + 0) * m₁)
      = a * (m₂ - m₁ ^ 2) / ((1 + (ε + a) * m₁) * (1 + (ε + 0) * m₁)) := by
    field_simp
    ring
  rw [key]
  have hAB : (1 + (ε + a) * m₁) * (1 + (ε + 0) * m₁) ≤ (2 + ε) * (1 + ε) := by
    have e1 : 1 + (ε + a) * m₁ ≤ 2 + ε := by nlinarith
    have e2 : 1 + (ε + 0) * m₁ ≤ 1 + ε := by nlinarith
    exact mul_le_mul e1 e2 hB.le (by positivity)
  have hpos : 0 < (1 + (ε + a) * m₁) * (1 + (ε + 0) * m₁) := mul_pos hA hB
  have hnum : 0 ≤ a * (m₂ - m₁ ^ 2) := by positivity
  calc 2 * ((m₂ - m₁ ^ 2) / (2 * ((2 + ε) * (1 + ε)))) * a
      = a * (m₂ - m₁ ^ 2) / ((2 + ε) * (1 + ε)) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_left hnum hpos hAB

/-- Lipschitz algebra -/
theorem s7c_lip {ε M₁ M₂ m₁ m₂ a : ℝ} (hε : 0 < ε) (hM1 : 0 ≤ M₁) (hM2 : 0 ≤ M₂)
    (hM2' : M₂ ≤ 1) (hM1' : M₁ ≤ 1) (hm1 : 0 ≤ m₁) (hm2 : 0 ≤ m₂) (hm1' : m₁ ≤ 1) (hm2' : m₂ ≤ 1)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    |(M₁ + (ε + a) * M₂) / (1 + (ε + a) * M₁) - (m₁ + (ε + a) * m₂) / (1 + (ε + a) * m₁)| ≤
      (2 * (1 + (ε + 1) ^ 2)) * (|M₁ - m₁| + |M₂ - m₂|) := by
  set t := ε + a with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ ε + 1 := by linarith
  have hp : 1 ≤ 1 + t * M₁ := by nlinarith
  have hq : 1 ≤ 1 + t * m₁ := by nlinarith
  have key : (M₁ + t * M₂) / (1 + t * M₁) - (m₁ + t * m₂) / (1 + t * m₁) =
      ((M₁ - m₁) * (1 - t ^ 2 * m₂) + (M₂ - m₂) * (t + t ^ 2 * m₁)) /
        ((1 + t * M₁) * (1 + t * m₁)) := by
    field_simp
    ring
  rw [key, abs_div, abs_of_pos (by positivity : 0 < (1 + t * M₁) * (1 + t * m₁))]
  have hpq : 1 ≤ (1 + t * M₁) * (1 + t * m₁) := by nlinarith
  refine (div_le_self (abs_nonneg _) hpq).trans ?_
  have hT : t ^ 2 ≤ (ε + 1) ^ 2 := by nlinarith
  have f1 : |1 - t ^ 2 * m₂| ≤ 2 * (1 + (ε + 1) ^ 2) := by
    rw [abs_le]; constructor <;> nlinarith [mul_nonneg (sq_nonneg t) hm2, mul_le_mul_of_nonneg_left hm2' (sq_nonneg t)]
  have f2 : |t + t ^ 2 * m₁| ≤ 2 * (1 + (ε + 1) ^ 2) := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hm1' (sq_nonneg t), sq_nonneg (ε + 1 - 1)]
  calc _ ≤ |(M₁ - m₁) * (1 - t ^ 2 * m₂)| + |(M₂ - m₂) * (t + t ^ 2 * m₁)| := abs_add_le _ _
    _ = |M₁ - m₁| * |1 - t ^ 2 * m₂| + |M₂ - m₂| * |t + t ^ 2 * m₁| := by rw [abs_mul, abs_mul]
    _ ≤ |M₁ - m₁| * (2 * (1 + (ε + 1) ^ 2)) + |M₂ - m₂| * (2 * (1 + (ε + 1) ^ 2)) :=
        add_le_add (mul_le_mul_of_nonneg_left f1 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left f2 (abs_nonneg _))
    _ = _ := by ring

theorem s7_S16c_ratio_slope_proof (ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure ν]
    (hν : ProbabilityTheory.IsGaussian ν) (hfull : ∀ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U →
      U.Nonempty → 0 < ν U) (ε : ℝ) (hε : 0 < ε) :
    let v : EuclideanSpace ℝ (Fin 2) → ℝ := fun z => Real.exp (-‖z‖ ^ 2)
    let m₁ := ∫ z, v z ∂ν
    let m₂ := ∫ z, v z ^ 2 ∂ν
    let fr : ℝ → ℝ → ℝ → ℝ := fun M₁ M₂ a => (M₁ + (ε + a) * M₂) / (1 + (ε + a) * M₁)
    0 < m₂ - m₁ ^ 2 ∧ ∃ c a₀ C : ℝ, 0 < c ∧ 0 < a₀ ∧ 0 < C ∧
      (∀ a, 0 < a → a < a₀ → fr m₁ m₂ a - fr m₁ m₂ 0 ≥ 2 * c * a) ∧
      (∀ M₁ M₂ a, 0 ≤ M₁ → M₁ ≤ 1 → 0 ≤ M₂ → M₂ ≤ 1 → 0 ≤ a → a ≤ 1 →
        |fr M₁ M₂ a - fr m₁ m₂ a| ≤ C * (|M₁ - m₁| + |M₂ - m₂|)) := by
  intro v m₁ m₂ fr
  have hv : v = s7c_v := rfl
  have e1 : m₁ = ∫ z, s7c_v z ^ 1 ∂ν := by simp [m₁, hv]
  have e2 : m₂ = ∫ z, s7c_v z ^ 2 ∂ν := rfl
  have hD : 0 < m₂ - m₁ ^ 2 := by
    have := s7c_var_pos ν hfull
    simpa [m₁, m₂, hv] using this
  have h1 : 0 ≤ m₁ := by rw [e1]; exact s7c_int_nonneg ν 1
  have h1' : m₁ ≤ 1 := by rw [e1]; exact s7c_int_le_one ν 1
  have h2 : 0 ≤ m₂ := by rw [e2]; exact s7c_int_nonneg ν 2
  have h2' : m₂ ≤ 1 := by rw [e2]; exact s7c_int_le_one ν 2
  refine ⟨hD, (m₂ - m₁ ^ 2) / (2 * ((2 + ε) * (1 + ε))), 1, 2 * (1 + (ε + 1) ^ 2),
    by positivity, one_pos, by positivity, ?_, ?_⟩
  · intro a ha ha1
    exact s7c_slope hε h1 h1' hD ha ha1
  · intro M₁ M₂ a hM1 hM1' hM2 hM2' ha ha1
    exact s7c_lip hε hM1 hM2 hM2' hM1' h1 h2 h1' h2' ha ha1

end HRS.MC.Sec7.S16c
