import HRS.MS.Fp81S21GaussianQuadraticHilbert14

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal BigOperators RealInnerProductSpace
open HRS HRS.MC.E213U13 HRS.MS.R26T6 HRS.MS.R26T3
namespace HRS.Fp81.S21

local instance fp81s21_GaussianQuadraticHilbert15_inst1 (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _
local instance fp81s21_GaussianQuadraticHilbert15_inst2 (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- The same retained history and each bounded linear correction of it lie
in second chaos in L³. -/
theorem fp81s21_TimeL2Rep_secondChaos
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ) (hm : ∀ i, Measurable (ξ i))
    (q : ℝ → Ω → r26t6_Coeff) (M a H : ℝ) (ha : 0 ≤ a) (hH : 0 ≤ H)
    (U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hq : Measurable (Function.uncurry q)) (hrep : fp81s21_TimeL2Rep P q M a H U)
    (hcoord : ∀ u, 0 ≤ u → MemLp (q u) 2 P ∧ ∀ j, InQ2 hξ (fun ω => q u ω j))
    (Λ : Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)) →L[ℝ] B) :
    InSecondChaos P ξ 3 U ∧ InSecondChaos P ξ 3 (fun ω => Λ (U ω)) := by
  letI : TopologicalSpace.SeparableSpace r26t6_Coeff := HRS.StaticLimitAux.separable_lp (ι := ℕ)
  letI : SecondCountableTopology r26t6_Coeff := UniformSpace.secondCountable_of_separable _
  have hc : InSecondChaos P ξ 3 U :=
    s21l_inSecondChaos_of_coords hξ hm hrep.2.1.aestronglyMeasurable hrep.2.1
      (fun v => fp81s21_TimeL2Rep_InQ2_inner hξ q M a H ha hH U hq hrep hcoord v)
  exact ⟨hc, HRS.MC.E213U13.InSecondChaos.clm Λ (by norm_num) hc⟩

#print axioms fp81s21_TimeL2Rep_secondChaos
end HRS.Fp81.S21
end
