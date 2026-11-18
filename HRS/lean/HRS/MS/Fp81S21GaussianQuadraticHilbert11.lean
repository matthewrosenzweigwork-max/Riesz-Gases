import HRS.MS.Fp81S21GaussianQuadraticHilbert10

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal BigOperators RealInnerProductSpace
open HRS HRS.MC.E213U13 HRS.MS.R26T6
namespace HRS.Fp81.S21

local instance fp81s21_GaussianQuadraticHilbert11_inst1 (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _
local instance fp81s21_GaussianQuadraticHilbert11_inst2 (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- The retained finite-horizon history is an L⁴ limit of finite quadratic
polynomials on the same Gaussian sequence, with a sharp fourth-moment bound. -/
theorem fp81s21_TimeL2Rep_L4_polynomials
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ)
    (q : ℝ → Ω → r26t6_Coeff) (M a H : ℝ) (ha : 0 ≤ a) (hH : 0 ≤ H)
    (U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hq : Measurable (Function.uncurry q))
    (hrep : fp81s21_TimeL2Rep P q M a H U)
    (hcoord : ∀ u, 0 ≤ u → MemLp (q u) 2 P ∧ ∀ j, InQ2 hξ (fun ω => q u ω j)) :
    MemLp U 4 P ∧ (∫ ω, ‖U ω‖ ^ 4 ∂P) ≤ 15 * (∫ ω, ‖U ω‖ ^ 2 ∂P) ^ 2 ∧
    ∃ (ι : Type) (b : HilbertBasis ι ℝ
        (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))))
      (S : ℕ → Finset ι) (N : ℕ → ι → ℕ) (c : ℕ → ι → ℕ → ℕ → ℝ),
      Tendsto (fun n => eLpNorm (fun ω =>
        (∑ s ∈ S n, quadSum (c n s) ξ (N n s) ω • b s) - U ω) 4 P)
        atTop (𝓝 0) := by
  letI : TopologicalSpace.SeparableSpace r26t6_Coeff := HRS.StaticLimitAux.separable_lp (ι := ℕ)
  letI : SecondCountableTopology r26t6_Coeff := UniformSpace.secondCountable_of_separable _
  obtain ⟨ι, hι, b, -⟩ := HRS.HilbertCLTAux.exists_hilbertBasis_type
    (H := Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
  letI : Countable ι := hι
  obtain ⟨h4, hb, S, N, c, ht⟩ := fp81s21_InQ2_hilbert_L4_polynomials hξ b U hrep.2.1
    (fun s => fp81s21_TimeL2Rep_InQ2_inner hξ q M a H ha hH U hq hrep hcoord (b s))
  exact ⟨h4, hb, ι, b, S, N, c, ht⟩

#print axioms fp81s21_TimeL2Rep_L4_polynomials
end HRS.Fp81.S21
end
