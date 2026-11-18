import HRS.MS.R26T8AP07i
import HRS.MS.R26T8AP07g

/-!
# S8.2 local Newton layer, packet T8A.P07 (part j): series representation of the raw Newton integral
For `0 <= sigma < d`, `0 < |w| <= 2`: `z |-> K(w-z) chi(z) midPair F X z` is integrable and
`sum_n annularNewton nu chi (1/2)^n F X w` (absolutely summable by `r26t8a_p07_series_bound`) has the sum `∫ K(w-z) chi z midPair F X z dz`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_p07_ae_meas {m : Euc d → ℝ} (hm : ContinuousOn m {z : Euc d | z ≠ 0}) (hd : 2 ≤ d) :
    AEStronglyMeasurable m volume := by
  have h : AEStronglyMeasurable m (volume.restrict {z : Euc d | z ≠ 0}) :=
    hm.aestronglyMeasurable (isOpen_ne (x := (0 : Euc d))).measurableSet
  have e : (volume : Measure (Euc d)).restrict {z : Euc d | z ≠ 0} = volume :=
    Measure.restrict_eq_self_of_ae_mem (r26t8a_ae_ne_zero hd)
  rwa [e] at h

theorem r26t8a_p07_dom (hd : 2 ≤ d) (nu : ℝ) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) {w : Euc d} (hw : w ≠ 0)
    {m : Euc d → ℝ} (hm : ContinuousOn m {z : Euc d | z ≠ 0}) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ z : Euc d, 0 < ‖z‖ → ‖z‖ ≤ 2 → |m z| ≤ c * ‖z‖ ^ (-s))
    (θ : Euc d → ℝ) (hθc : Continuous θ) (hθ1 : ∀ z, |θ z| ≤ 1) (hθ2 : ∀ z, 2 < ‖z‖ → θ z = 0) :
    Integrable (fun z => newtonKernel d nu (w - z) * θ z * m z) ∧
    ∀ z : Euc d, z ≠ 0 → ‖newtonKernel d nu (w - z) * θ z * m z‖ ≤
      c * (|newtonKernel d nu (w - z)| * (closedBall (0 : Euc d) 2).indicator (fun z => ‖z‖ ^ (-s)) z) := by
  have hbd : ∀ z : Euc d, z ≠ 0 → ‖newtonKernel d nu (w - z) * θ z * m z‖ ≤
      c * (|newtonKernel d nu (w - z)| * (closedBall (0 : Euc d) 2).indicator (fun z => ‖z‖ ^ (-s)) z) := by
    intro z hz
    have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
    by_cases h2 : ‖z‖ ≤ 2
    · rw [Set.indicator_of_mem (by simpa using h2)]
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
      have := hc z hzn h2
      have h1 := hθ1 z
      calc |newtonKernel d nu (w - z)| * |θ z| * |m z|
          ≤ |newtonKernel d nu (w - z)| * 1 * (c * ‖z‖ ^ (-s)) := by
            gcongr
        _ = _ := by ring
    · rw [Set.indicator_of_notMem (by simpa using h2), hθ2 z (not_le.1 h2)]
      simp
  have hmeas : AEStronglyMeasurable (fun z => newtonKernel d nu (w - z) * θ z * m z) volume :=
    ((((r26t8a_K_measurable nu).comp (measurable_const.sub measurable_id)).aestronglyMeasurable).mul
      hθc.aestronglyMeasurable).mul (r26t8a_p07_ae_meas hm hd)
  refine ⟨?_, hbd⟩
  refine Integrable.mono' ((r26t8a_p07_major hd nu hs0 hsd hw).const_mul c) hmeas ?_
  filter_upwards [r26t8a_ae_ne_zero hd] with z hz using hbd z hz

end HRS.MS.R26T8A
