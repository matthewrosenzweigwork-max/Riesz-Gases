import HRS.MS.R26T6CI09FiniteSum
import HRS.MS.R26T6CI09Coord
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# R26-T6C.I09: countable L3 square-summable coordinate lift

No pointwise coefficient bound is assumed. The sharp L3 bound follows from
finite-dimensional Minkowski and lower semicontinuity under a.e. convergence.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole HRS.MS.CovMeas HRS.MS.Go
variable {d : ℕ}

theorem r26t6c_ellVec_L3 (m : ℝ)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (f : MultiIndex d → Omega → ℝ) (b : MultiIndex d → ℝ)
    (hb0 : ∀ i, 0 ≤ b i) (hb : Summable (fun i => b i ^ 2))
    (hf : ∀ i, MemLp (f i) 3 P)
    (hfb : ∀ i, eLpNorm (f i) 3 P ≤ ENNReal.ofReal (b i)) :
    MemLp (fun w => ellVec (d := d) m (fun i => f i w)) 3 P ∧
    (∀ᵐ w ∂P, ∀ i,
      OscDual.coord (ellVec (d := d) m (fun j => f j w)) i = f i w) ∧
    eLpNorm (fun w => ellVec (d := d) m (fun i => f i w)) 3 P ≤
      ENNReal.ofReal (Real.sqrt (∑' i, b i ^ 2)) := by
  classical
  let U : Omega → OscDual d m :=
    fun w => ellVec (d := d) m (fun i => f i w)
  let V : Finset (MultiIndex d) → Omega → OscDual d m :=
    fun s w => ∑ i ∈ s, (lp.single 2 i (f i w) : OscDual d m)
  have hsq := r26t6c_coordinate_square_ae P f b hb0 hb hf hfb
  have hUmeas : AEStronglyMeasurable U P :=
    r26t6c_ellVec_aesm P m f (fun i => (hf i).aestronglyMeasurable) hsq
  have hVmeas : ∀ s, AEStronglyMeasurable (V s) P :=
    fun s => (r26t6c_finite_series_L3 P m s f b hb0 hf hfb).1.aestronglyMeasurable
  have hbound : ∀ s, eLpNorm (V s) 3 P ≤
      ENNReal.ofReal (Real.sqrt (∑' i, b i ^ 2)) := by
    intro s
    have hFs := (r26t6c_finite_series_L3 P m s f b hb0 hf hfb).2
    have hsum : (∑ i ∈ s, b i ^ 2) ≤ ∑' i, b i ^ 2 :=
      hb.sum_le_tsum s (fun i _ => sq_nonneg _)
    exact hFs.trans (ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt hsum))
  have hconv : ∀ᵐ w ∂P, Tendsto (fun s : Finset (MultiIndex d) => V s w)
      atTop (𝓝 (U w)) := by
    filter_upwards [hsq] with w hw
    have hm : Memℓp (fun i => f i w) 2 := by
      rw [memℓp_two_iff]
      exact hw
    have hs : HasSum (fun i => (lp.single 2 i (f i w) :
        lp (fun _ : MultiIndex d => ℝ) 2))
        (ellVec (d := d) m (fun i => f i w) :
          lp (fun _ : MultiIndex d => ℝ) 2) := by
      rw [s55f_ellVec_eq (m := m) hm]
      exact lp.hasSum_single (by norm_num) ⟨fun i => f i w, hm⟩
    exact hs
  have hL3 : eLpNorm U 3 P ≤ ENNReal.ofReal (Real.sqrt (∑' i, b i ^ 2)) :=
    Lp.eLpNorm_le_of_ae_tendsto (u := (atTop : Filter (Finset (MultiIndex d))))
      (f := V) (g := U) (p := 3)
      (Filter.Eventually.of_forall hbound) hVmeas hUmeas hconv
  refine ⟨?_, ?_, hL3⟩
  · exact (memLp_iff).2 (hL3.trans_lt ENNReal.ofReal_lt_top)
  · exact r26t6c_ellVec_coord_ae P m f hsq

end HRS.MS.R26T6C
