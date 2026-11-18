import HRS.MS.Fp81S21GaussianQuadraticHilbert6

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal BigOperators
open HRS HRS.MC.E213U13 HRS.MS.R26T6
namespace HRS.Fp81.S21

local instance fp81s21_GaussianQuadraticHilbert7_inst1 (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _
local instance fp81s21_GaussianQuadraticHilbert7_inst2 (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- Bounded time-dependent scalar observations of a retained quadratic
history belong to the same second chaos. -/
theorem fp81s21_TimeL2Rep_InQ2_integral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ)
    (q : ℝ → Ω → r26t6_Coeff) (M a H : ℝ) (ha : 0 ≤ a) (hH : 0 ≤ H)
    (U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hq : Measurable (Function.uncurry q))
    (hrep : fp81s21_TimeL2Rep P q M a H U)
    (hcoord : ∀ u, 0 ≤ u → MemLp (q u) 2 P ∧ ∀ j, InQ2 hξ (fun ω => q u ω j))
    (ℓ : ℝ → r26t6_Coeff →L[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hℓ : ∀ t, ‖ℓ t‖ ≤ C)
    (hℓmeas : Measurable (fun p : ℝ × r26t6_Coeff => ℓ p.1 p.2))
    {Z : Ω → ℝ} (hZ : MemLp Z 2 P)
    (hZeq : Z =ᵐ[P] fun ω => ∫ t, ℓ t (q (a + t) ω)
      ∂(volume.restrict (Set.Icc (0 : ℝ) H))) : InQ2 hξ Z := by
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  have hg : Measurable (fun p : Ω × ℝ => q (a + p.2) p.1) :=
    hq.comp ((measurable_const.add measurable_snd).prodMk measurable_fst)
  have hc : ∀ᵐ t ∂dt, MemLp (q (a + t)) 2 P ∧
      ∀ j, InQ2 hξ (fun ω => q (a + t) ω j) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hcoord (a + t) (add_nonneg ha ht.1)
  obtain ⟨hi, hL2⟩ := fp81s21_TimeL2Rep_norm_integral P q M a H hH U hq hrep
  exact fp81s21_InQ2_coeff_time_integral hξ dt (fun t ω => q (a + t) ω)
    hg hc hi hL2 ℓ C hC hℓ hℓmeas hZ hZeq

#print axioms fp81s21_TimeL2Rep_InQ2_integral
end HRS.Fp81.S21
end
