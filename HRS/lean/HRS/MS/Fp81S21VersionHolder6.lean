import HRS.MS.Fp81S21VersionHolder5

set_option autoImplicit false
noncomputable section
open Classical MeasureTheory Filter
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS.MP.KC

/-- Uniform continuous versions with an L2 eighth-Hölder envelope. The
constant is selected before the probability space, process, and shift. -/
theorem fp81s21_exists_holder_version
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    (H M4 C : ℝ) (hH : 0 < H) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (q : ℝ → Ω → E) (a : ℝ),
      (∀ t, Measurable (q t)) → MemLp (q a) 4 P →
      (∫ ω, ‖q a ω‖ ^ 4 ∂P) ≤ M4 →
      (∀ s t : Set.Icc (0 : ℝ) H,
        MemLp (fun ω => q (a + t) ω - q (a + s) ω) 4 P ∧
        (∫ ω, ‖q (a + t) ω - q (a + s) ω‖ ^ 4 ∂P) ≤ C * |(t : ℝ) - s| ^ 2) →
      ∃ X : Ω → C(Set.Icc (0 : ℝ) H, E), Measurable X ∧ MemLp X 2 P ∧
        (∀ t : Set.Icc (0 : ℝ) H, (fun ω => X ω t) =ᵐ[P] q (a + t)) ∧
        ∃ B : Ω → ℝ, Measurable B ∧ (∀ ω, 0 ≤ B ω) ∧
          Integrable (fun ω => B ω ^ 2) P ∧ (∫ ω, B ω ^ 2 ∂P) ≤ D ∧
          ∀ᵐ ω ∂P, ∀ s t : Set.Icc (0 : ℝ) H,
            ‖X ω t - X ω s‖ ≤ B ω * |(t : ℝ) - s| ^ (1 / 8 : ℝ) := by
  let K : ℝ := C * H ^ 2 / (1 - 1 / (2 * (9 / 10 : ℝ) ^ 4))
  let A : ℝ := mkc_c (9 / 10 : ℝ) * (2 / H) ^ (1 / 8 : ℝ)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hA : 0 ≤ A := by dsimp [A, mkc_c]; positivity
  refine ⟨A ^ 2 * (1 + K), by positivity, ?_⟩
  intro Ω _ P _ q a hqm hq0 hM hinc
  let Z : ℝ → Ω → E := fun t => q (a + t)
  have hZm : ∀ t, Measurable (Z t) := fun t => hqm _
  have hZ0 : MemLp (Z 0) 4 P := by simpa [Z] using hq0
  have hZ0bound : (∫ ω, ‖Z 0 ω‖ ^ 4 ∂P) ≤ M4 := by simpa [Z] using hM
  have hmom : ∀ s ∈ Set.Icc (0 : ℝ) H, ∀ t ∈ Set.Icc (0 : ℝ) H,
      (∫⁻ ω, ENNReal.ofReal (‖Z t ω - Z s ω‖ ^ 4) ∂P) ≤
        ENNReal.ofReal (C * |t - s| ^ 2) := by
    intro s hs t ht
    have hh := hinc ⟨s, hs⟩ ⟨t, ht⟩
    have hi : Integrable (fun ω => ‖Z t ω - Z s ω‖ ^ 4) P :=
      hh.1.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun ω => by positivity)]
    exact ENNReal.ofReal_le_ofReal hh.2
  obtain ⟨X, hXm, hX4, hXeq, _, L, hL0, hL, hLbound, hdyad⟩ :=
    fp81s21_fourth_continuous_version P Z hH hC hZm hZ0 hZ0bound hmom
  obtain ⟨L', hLm, hL'0, hLeq, hLi, hLibound⟩ :=
    fp81s21_measurable_envelope_second_moment P L hL0 hL hLbound
  let B : Ω → ℝ := fun ω => A * L' ω
  have hBi : Integrable (fun ω => B ω ^ 2) P := by
    simpa only [B, mul_pow] using hLi.const_mul (A ^ 2)
  have hBbound : (∫ ω, B ω ^ 2 ∂P) ≤ A ^ 2 * (1 + K) := by
    simp only [B, mul_pow, integral_const_mul]
    exact mul_le_mul_of_nonneg_left hLibound (sq_nonneg A)
  refine ⟨X, hXm, hX4.mono_exponent (by norm_num), ?_, B, ?_, ?_, hBi, hBbound, ?_⟩
  · intro t
    simpa [Z] using hXeq t
  · exact measurable_const.mul hLm
  · intro ω
    exact mul_nonneg hA (hL'0 ω)
  · have hh := fp81s21_dyadic_modulus_holder P hH X L hL0 hdyad
    filter_upwards [hh, hLeq] with ω hω heq s t
    have ht := hω s t
    dsimp only [B, A]
    rw [← heq]
    convert ht using 1 <;> ring

#print axioms fp81s21_exists_holder_version

end HRS.Fp81.S21
