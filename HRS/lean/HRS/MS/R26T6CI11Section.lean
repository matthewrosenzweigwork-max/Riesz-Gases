import HRS.MS.R26T6CI11Initial

/-!
# I11: every time-section of the derivative has a genuine L³ oscillator lift.
# No assumption on the smoothness of the time sections is used.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole
variable {d : ℕ}

theorem r26t6c_derivative_section_L3
    (m T : ℝ) (hT : 0 < T)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (g : MultiIndex d → ℝ → Omega → ℝ)
    (b : MultiIndex d → ℝ)
    (hb0 : ∀ i, 0 ≤ b i)
    (hb : Summable (fun i => b i ^ 2))
    (hb1 : (∑' i, b i ^ 2) ≤ 1)
    (A : ℝ) (hA : 0 ≤ A)
    (hf : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, MemLp (g i t) 3 P)
    (hfb : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫ w, |g i t w| ^ 3 ∂P) ≤ (A * b i) ^ 3) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      MemLp (fun w => ellVec (d := d) m (fun i => g i t w)) 3 P ∧
      (∀ᵐ w ∂P, ∀ i, OscDual.coord
        (ellVec (d := d) m (fun j => g j t w)) i = g i t w) ∧
      eLpNorm (fun w => ellVec (d := d) m (fun i => g i t w)) 3 P ≤
        ENNReal.ofReal A := by
  intro t ht
  exact r26t6c_initial_ellVec_L3 m P (fun i w => g i t w)
    b hb0 hb hb1 A hA
    (fun i => hf i t ht)
    (fun i => hfb i t ht)

end HRS.MS.R26T6C
