import HRS.MS.R26T6CI11Field
import HRS.MS.R26T6CI11Section

/-!
# I11: genuine jointly measurable L³ oscillator derivative

This is the key time–probability interface for constructing the
continuous Bochner primitive, without pointwise control or a finite
coordinate cutoff.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole
variable {d : ℕ}

theorem r26t6c_interval_oscillator_derivative_L3
    (m T : ℝ) (hT : 0 < T)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (g : MultiIndex d → ℝ → Omega → ℝ)
    (b : MultiIndex d → ℝ)
    (hb0 : ∀ i, 0 ≤ b i)
    (hb : Summable (fun i => b i ^ 2))
    (hb1 : (∑' i, b i ^ 2) ≤ 1)
    (A : ℝ) (hA : 0 ≤ A)
    (hgm : ∀ i, AEStronglyMeasurable
      (fun z : ℝ × Omega => g i z.1 z.2)
      ((volume.restrict (Set.Icc 0 T)).prod P))
    (hgLp : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, MemLp (g i t) 3 P)
    (hgBound : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫ w, |g i t w| ^ 3 ∂P) ≤ (A * b i) ^ 3) :
    MemLp (fun z : ℝ × Omega =>
        ellVec (d := d) m (fun i => g i z.1 z.2)) 3
        ((volume.restrict (Set.Icc 0 T)).prod P) ∧
    (∀ᵐ z ∂((volume.restrict (Set.Icc 0 T)).prod P),
        Summable (fun i => g i z.1 z.2 ^ 2)) := by
  let dt : Measure ℝ := volume.restrict (Set.Icc 0 T)
  have htime : ∀ᵐ t ∂dt, t ∈ Set.Icc (0 : ℝ) T :=
    ae_restrict_mem measurableSet_Icc
  have hLp : ∀ i, ∀ᵐ t ∂dt, MemLp (g i t) 3 P := by
    intro i
    filter_upwards [htime] with t ht
    exact hgLp i t ht
  have hBound : ∀ i, ∀ᵐ t ∂dt,
      (∫ w, |g i t w| ^ 3 ∂P) ≤ (A * b i) ^ 3 := by
    intro i
    filter_upwards [htime] with t ht
    exact hgBound i t ht
  have hfield := r26t6c_spacetime_ellVec_aesm
    m dt P (fun i (z : ℝ × Omega) => g i z.1 z.2)
    hgm b hb0 hb A hA hLp hBound
  have hsections : ∀ᵐ t ∂dt,
      MemLp (fun w => ellVec (d := d) m (fun i => g i t w)) 3 P ∧
      eLpNorm (fun w => ellVec (d := d) m (fun i => g i t w)) 3 P ≤
        ENNReal.ofReal A := by
    filter_upwards [htime] with t ht
    have hsec := r26t6c_derivative_section_L3 m T hT P g b hb0 hb hb1
      A hA hgLp hgBound t ht
    exact ⟨hsec.1, hsec.2.2⟩
  exact ⟨r26t6c_spacetime_L3_of_sections dt P
      (fun z : ℝ × Omega => ellVec (d := d) m (fun i => g i z.1 z.2))
      hfield.1 A hA hsections,
    hfield.2⟩

end HRS.MS.R26T6C
