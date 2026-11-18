import HRS.MS.Fp81S21GaussianQuadraticHilbert11

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal BigOperators RealInnerProductSpace
open HRS HRS.MC.E213U13 HRS.MS.R26T6
namespace HRS.Fp81.S21

local instance fp81s21_GaussianQuadraticHilbert12_inst1 (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _
local instance fp81s21_GaussianQuadraticHilbert12_inst2 (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- One fourth-moment constant works for all shifts of the retained history. -/
theorem fp81s21_TimeL2Rep_uniform_L4_polynomials
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ)
    (q : ℝ → Ω → r26t6_Coeff) (M H : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (U : ℝ → Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hq : Measurable (Function.uncurry q))
    (hrep : ∀ a, 0 ≤ a → fp81s21_TimeL2Rep P q M a H (U a))
    (hcoord : ∀ u, 0 ≤ u → MemLp (q u) 2 P ∧ ∀ j, InQ2 hξ (fun ω => q u ω j)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a, 0 ≤ a → MemLp (U a) 4 P ∧
      (∫ ω, ‖U a ω‖ ^ 4 ∂P) ≤ C ∧
      ∃ (ι : Type) (b : HilbertBasis ι ℝ
          (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))))
        (S : ℕ → Finset ι) (N : ℕ → ι → ℕ) (c : ℕ → ι → ℕ → ℕ → ℝ),
        Tendsto (fun n => eLpNorm (fun ω =>
          (∑ s ∈ S n, quadSum (c n s) ξ (N n s) ω • b s) - U a ω) 4 P)
          atTop (𝓝 0) := by
  refine ⟨15 * (H * M) ^ 2, by positivity, ?_⟩
  intro a ha
  have hr := hrep a ha
  obtain ⟨h4, hb, hp⟩ := fp81s21_TimeL2Rep_L4_polynomials hξ q M a H ha hH
    (U a) hq hr hcoord
  refine ⟨h4, hb.trans ?_, hp⟩
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (integral_nonneg fun ω => sq_nonneg _) hr.2.2.1 2) (by norm_num)

#print axioms fp81s21_TimeL2Rep_uniform_L4_polynomials
end HRS.Fp81.S21
end
