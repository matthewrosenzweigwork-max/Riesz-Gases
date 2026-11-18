import HRS.MS.R26T6CI11Moment

/-! I11: a probability-valued initial oscillator vector from exact cubic coordinate bounds. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole
variable {d : ℕ}

theorem r26t6c_initial_ellVec_L3
    (m : ℝ) {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (f : MultiIndex d → Omega → ℝ) (b : MultiIndex d → ℝ)
    (hb0 : ∀ i, 0 ≤ b i) (hb : Summable (fun i => b i ^ 2))
    (hb1 : (∑' i, b i ^ 2) ≤ 1)
    (A : ℝ) (hA : 0 ≤ A)
    (hf : ∀ i, MemLp (f i) 3 P)
    (hfb : ∀ i, ∫ w, |f i w| ^ 3 ∂P ≤ (A * b i) ^ 3) :
    MemLp (fun w => ellVec (d := d) m (fun i => f i w)) 3 P ∧
    (∀ᵐ w ∂P, ∀ i,
      OscDual.coord (ellVec (d := d) m (fun j => f j w)) i = f i w) ∧
    eLpNorm (fun w => ellVec (d := d) m (fun i => f i w)) 3 P ≤ ENNReal.ofReal A := by
  have hscale : Summable (fun i => (A * b i) ^ 2) := by
    have hh := hb.mul_left (A ^ 2)
    convert hh using 1
    funext i
    ring
  have hnonneg : ∀ i, 0 ≤ A * b i := fun i => mul_nonneg hA (hb0 i)
  have hcoordinate : ∀ i, eLpNorm (f i) 3 P ≤ ENNReal.ofReal (A * b i) :=
    fun i => r26t6c_cube_bound_to_eLpNorm P (f i) (hf i)
      (A * b i) (hnonneg i) (hfb i)
  have hmain := r26t6c_ellVec_L3 m P f (fun i => A * b i)
    hnonneg hscale hf hcoordinate
  have hsum : (∑' i, (A * b i) ^ 2) = A ^ 2 * (∑' i, b i ^ 2) := by
    simp_rw [show ∀ i, (A * b i) ^ 2 = A ^ 2 * b i ^ 2 from
      fun i => by ring]
    rw [tsum_mul_left]
  have hbound : Real.sqrt (∑' i, (A * b i) ^ 2) ≤ A := by
    rw [hsum]
    have hm : A ^ 2 * (∑' i, b i ^ 2) ≤ A ^ 2 := by
      nlinarith [sq_nonneg A, hb1]
    calc
      _ ≤ Real.sqrt (A ^ 2) := Real.sqrt_le_sqrt hm
      _ = A := Real.sqrt_sq_eq_abs A |>.trans (abs_of_nonneg hA)
  exact ⟨hmain.1, hmain.2.1,
    hmain.2.2.trans (ENNReal.ofReal_le_ofReal hbound)⟩

end HRS.MS.R26T6C
