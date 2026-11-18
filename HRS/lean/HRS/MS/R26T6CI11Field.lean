import HRS.MS.R26T6CI11ProdSq
import HRS.MS.R26T6CI11Moment

/-!
# I11: jointly measurable ℓ²-valued field from sectional cubic moments.

The original hypotheses provide countably many jointly measurable scalar
coordinates and a uniform-in-time ℓ² summable bound on their third moments.
This lemma produces the genuine jointly a.e.-measurable oscillator field.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole HRS.MS.Go HRS.MS.R2Chaos
variable {d : ℕ}

theorem r26t6c_spacetime_ellVec_aesm
    (m : ℝ) {Time Omega : Type*}
    [MeasurableSpace Time] [MeasurableSpace Omega]
    (dt : Measure Time) [IsFiniteMeasure dt]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (g : MultiIndex d → Time × Omega → ℝ)
    (hg : ∀ i, AEStronglyMeasurable (g i) (dt.prod P))
    (b : MultiIndex d → ℝ)
    (hb0 : ∀ i, 0 ≤ b i)
    (hb : Summable (fun i => b i ^ 2))
    (A : ℝ) (hA : 0 ≤ A)
    (hf : ∀ i, ∀ᵐ t ∂dt, MemLp (fun w => g i (t,w)) 3 P)
    (hfb : ∀ i, ∀ᵐ t ∂dt,
      (∫ w, |g i (t,w)| ^ 3 ∂P) ≤ (A * b i) ^ 3) :
    AEStronglyMeasurable
      (fun z : Time × Omega => ellVec (d := d) m (fun i => g i z))
      (dt.prod P) ∧
    (∀ᵐ z ∂dt.prod P, Summable (fun i => g i z ^ 2)) := by
  have hnonneg : ∀ i, 0 ≤ A * b i := fun i =>
    mul_nonneg hA (hb0 i)
  have hscale : Summable (fun i => (A * b i) ^ 2) := by
    have ht := hb.mul_left (A ^ 2)
    convert ht using 1
    funext i
    ring
  have hsec : ∀ i, ∀ᵐ t ∂dt,
      MemLp (fun w => g i (t,w)) 3 P ∧
      eLpNorm (fun w => g i (t,w)) 3 P ≤
        ENNReal.ofReal (A * b i) := by
    intro i
    filter_upwards [hf i, hfb i] with t ht hm
    exact ⟨ht, r26t6c_cube_bound_to_eLpNorm P
      (fun w => g i (t,w)) ht (A * b i) (hnonneg i) hm⟩
  have h2 : ∀ i, MemLp (g i) 2 (dt.prod P) := by
    intro i
    have h3 := r26t6c_spacetime_L3_of_sections dt P
      (g i) (hg i) (A * b i) (hnonneg i) (hsec i)
    exact h3.mono_exponent (by norm_num)
  have hsec2 : ∀ i, ∀ᵐ t ∂dt,
      (∫ w, g i (t,w) ^ 2 ∂P) ≤ (A * b i) ^ 2 := by
    intro i
    filter_upwards [hsec i] with t ht
    have ht2 : MemLp (fun w => g i (t,w)) 2 P :=
      ht.1.mono_exponent (by norm_num)
    have hn : eLpNorm (fun w => g i (t,w)) 2 P ≤
        ENNReal.ofReal (A * b i) :=
      (eLpNorm_le_eLpNorm_of_exponent_le
        (f := fun w => g i (t,w)) (μ := P)
        (by norm_num : (2 : ℝ≥0∞) ≤ 3)).trans ht.2
    exact s94_integral_sq_le_of_eLpNorm
      ht2.aestronglyMeasurable (hnonneg i) hn
  have haesq := r26t6c_spacetime_coordinate_square_ae
    dt P g (fun i => A * b i) hscale h2 hsec2
  exact ⟨r26t6c_ellVec_aesm (d := d) (P := dt.prod P)
    m (fun i z => g i z) hg haesq, haesq⟩

end HRS.MS.R26T6C
