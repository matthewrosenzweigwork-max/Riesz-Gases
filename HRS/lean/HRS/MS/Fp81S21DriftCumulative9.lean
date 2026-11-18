import HRS.MS.Fp81S21DriftCumulative6
import HRS.MS.Fp81S21DriftCumulative7

/-! Measurability of oscillator paths from their scalar coordinates. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS.Whole HRS.MS.R2Interp

/-- Coordinate-wise a.e. measurability at all observation times determines
the a.e. measurability of the whole continuous oscillator path. -/
theorem fp81s21_oscPath_aemeasurable_of_coordinates
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ} {m H : ℝ}
    (F : Ω → OscPath d m H)
    (hm : ∀ t : Icc (0 : ℝ) H, ∀ α : MultiIndex d,
      AEMeasurable (fun ω => OscDual.coord (OscPath.at' (F ω) t) α) P) :
    AEMeasurable F P := by
  classical
  obtain ⟨s, hs, hd⟩ : ∃ s : Set (Icc (0 : ℝ) H), s.Countable ∧ Dense s :=
    TopologicalSpace.exists_countable_dense _
  have hm' : ∀ t ∈ s, AEMeasurable (fun ω => r2PathAt (F ω) t) P := by
    intro t ht
    have := fp81s21_oscDual_aemeasurable_of_coordinates P
      (fun ω => OscPath.at' (F ω) t) (hm t)
    simpa only [s102_r2PathAt_of_mem _ t.2] using this
  have hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => r2PathAt (F ω) t) (Icc 0 H) := by
    filter_upwards [] with ω
    have h : Continuous (fun t : Icc (0 : ℝ) H => r2PathAt (F ω) t) := by
      have he : (fun t : Icc (0 : ℝ) H => r2PathAt (F ω) t) =
          (fun t : Icc (0 : ℝ) H => OscPath.at' (F ω) t) := by
        funext t
        exact s102_r2PathAt_of_mem _ t.2
      rw [he]
      exact (show C(Icc (0 : ℝ) H, OscDual d m) from F ω).continuous
    exact continuousOn_iff_continuous_restrict.mpr h
  obtain ⟨Y, hYm, hYc, hYe⟩ := fp81s21_dense_measurable_continuous_version
    P H (fun ω t => r2PathAt (F ω) t) s hs hd hm' hc
  let G : Ω → OscPath d m H := fun ω =>
    (⟨fun t : Icc (0 : ℝ) H => Y ω t, (hYc ω).restrict⟩ : C(Icc (0 : ℝ) H, OscDual d m))
  have hG : Measurable G := by
    change Measurable (fun ω => (show C(Icc (0 : ℝ) H, OscDual d m) from G ω))
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact hYm t
  refine ⟨G, hG, ?_⟩
  filter_upwards [hYe] with ω hω
  change (show C(Icc (0 : ℝ) H, OscDual d m) from F ω) =
    (show C(Icc (0 : ℝ) H, OscDual d m) from G ω)
  ext t
  change OscPath.at' (F ω) t = Y ω t
  rw [← s102_r2PathAt_of_mem _ t.2]
  exact (hω t t.2).symm

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_oscPath_aemeasurable_of_coordinates
