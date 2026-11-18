import HRS.MS.Fp81S21DriftCumulative10

/-! Measurable physical drift cumulative at a fixed horizon. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

/-- A measurable version of the actual moving drift cumulative, with a
simultaneous physical interval specification and an integrable variation bound. -/
theorem fp81s21_moving_drift_cumulative_fixed
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
      (2 * p.d + 8) c hH)
    (hphys : Fp81MovingPhysicalInputs R hN A H) :
    ∃ (Fd : A.Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) H) (V : A.Ω → ℝ),
      (∀ t : ℝ, Measurable (fun ω => Fd ω t)) ∧ Integrable V A.P ∧
      ∀ᵐ ω ∂A.P,
        Fd ω 0 = 0 ∧ ContinuousOn (Fd ω) (Icc 0 H) ∧
        BoundedVariationOn (Fd ω) (Icc 0 H) ∧
        (eVariationOn (Fd ω) (Icc 0 H)).toReal ≤ V ω ∧
        ∀ q r, 0 ≤ q → q ≤ r → r ≤ H → Fd ω r - Fd ω q =
          r2DriftInc (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
            (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) q r := by
  let F : A.Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) H := fun ω t =>
    r2DriftInc (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
      (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) 0 t
  have hc : ∀ᵐ ω ∂A.P, ContinuousOn (F ω) (Icc 0 H) :=
    fp81s21_moving_drift_cumulative_continuousOn p R hH hN A hstd hphys
  obtain ⟨s, hs, hd⟩ : ∃ s : Set (Icc (0 : ℝ) H), s.Countable ∧ Dense s :=
    TopologicalSpace.exists_countable_dense _
  have hm : ∀ t ∈ s, AEMeasurable (fun ω => F ω t) A.P := by
    intro t ht
    exact fp81s21_moving_drift_cumulative_section_aemeasurable p R hδ hδh hH hN A hstd hphys t t.2
  obtain ⟨Fd, hFd, hFdcont, hFde⟩ :=
    fp81s21_dense_measurable_continuous_version A.P H F s hs hd hm hc
  obtain ⟨Mb, hInt, hgood⟩ := fp81s21_moving_drift_cumulative_variation p R hH hN A hstd hphys
  refine ⟨Fd, fun ω => s102_KV p.d (2 * p.d + 8) ((p.d : ℝ) + 2) c *
    ∫ u in Ioc (0 : ℝ) H, Mb ω u, hFd, hInt, ?_⟩
  filter_upwards [hFde, hgood] with ω he hg
  have heq : EqOn (Fd ω) (F ω) (Icc 0 H) := fun t ht => he t ht
  have hv : eVariationOn (Fd ω) (Icc 0 H) = eVariationOn (F ω) (Icc 0 H) :=
    eVariationOn.congr heq
  refine ⟨?_, hFdcont ω, ?_, ?_, ?_⟩
  · rw [he 0 ⟨le_rfl, hH.le⟩]
    exact hg.1
  · unfold BoundedVariationOn at *
    rw [hv]
    exact hg.2.1
  · rw [hv]
    exact hg.2.2.2
  · intro q r hq hqr hr
    rw [he r ⟨hq.trans hqr, hr⟩, he q ⟨hq, hqr.trans hr⟩]
    exact hg.2.2.1 q r hq hqr hr

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_moving_drift_cumulative_fixed
