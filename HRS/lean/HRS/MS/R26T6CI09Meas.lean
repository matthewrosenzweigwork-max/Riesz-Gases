import HRS.MS.R26T6CI09Summable
import HRS.MS.S111K2B04i

/-! I09: the ellVec map is a.e.-strongly measurable whenever the coordinate squares sum a.e. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole HRS.MS.Go HRS.MS.CovMeas
variable {d : ℕ}

theorem r26t6c_ellVec_aesm {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) (m : ℝ)
    (f : MultiIndex d → Omega → ℝ)
    (hf : ∀ i, AEStronglyMeasurable (f i) P)
    (hsum : ∀ᵐ w ∂P, Summable fun i => f i w ^ 2) :
    AEStronglyMeasurable
      (fun w => ellVec (d := d) m (fun i => f i w)) P := by
  let ι : ∀ i : MultiIndex d, ℝ →L[ℝ] OscDual d m :=
    fun i => lp.singleContinuousLinearMap (𝕜 := ℝ)
      (E := fun _ : MultiIndex d => ℝ) 2 i
  refine aestronglyMeasurable_of_tendsto_ae
    (atTop : Filter (Finset (MultiIndex d)))
    (f := fun (s : Finset (MultiIndex d)) (w : Omega) =>
      ∑ i ∈ s, ι i (f i w)) ?_ ?_
  · intro s
    exact Finset.aestronglyMeasurable_fun_sum s fun i _ =>
      (ι i).continuous.comp_aestronglyMeasurable (hf i)
  · filter_upwards [hsum] with w hw
    have h : Memℓp (fun i => f i w) 2 := by
      rw [memℓp_two_iff]
      exact hw
    have h2 : HasSum
        (fun i => (lp.single 2 i (f i w) :
          lp (fun _ : MultiIndex d => ℝ) 2))
        (ellVec (d := d) m (fun i => f i w) :
          lp (fun _ : MultiIndex d => ℝ) 2) := by
      rw [s55f_ellVec_eq (m := m) h]
      exact lp.hasSum_single (by norm_num) ⟨fun i => f i w, h⟩
    exact h2

end HRS.MS.R26T6C
