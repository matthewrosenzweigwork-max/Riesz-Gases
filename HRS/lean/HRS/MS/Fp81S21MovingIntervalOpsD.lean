import HRS.MS.Fp81S21MovingAllInputs
import HRS.MS.Fp81S21SLin
import HRS.MS.R2InterpAux108
import HRS.MS.ProClosureS111IntervalOperators
import HRS.MS.Fp81S21WeightedDrift2
import HRS.MS.Fp81S21DriftCumulative5

/-! Charted orbits for the moving coefficient, at a fixed horizon. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp
open HRS.MS.ProClosureS111 HRS.MS.S111K4J01 HRS.MS.R26T6

private theorem fp81s21_moving_combo_memCb
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
      (2 * p.d + 8) c hH)
    {t v : ℝ} (ht : t ∈ Icc (0 : ℝ) H) (hv : v ∈ Icc (0 : ℝ) t)
    {φ : Euc p.d → ℝ} (hφ : IsR2DualCombo (wholeSpaceIndex p.d : ℝ) φ) :
    MemCb (2 * p.d + 9) (propagatorW (r26t3_coeff R) v t φ) := by
  obtain ⟨S, coeff, rfl⟩ := hφ
  rw [s102_prop_sum (fp81s21_S102Lin p R H) hv.1 hv.2 ht.2 S coeff]
  have hb : ∀ α : MultiIndex p.d,
      MemCb (2 * p.d + 9)
        (propagatorW (r26t3_coeff R) v t (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) := by
    intro α
    have hvH : v ∈ Icc (0 : ℝ) H := ⟨hv.1, hv.2.trans ht.2⟩
    have hvt : t ∈ Icc v H := ⟨hv.2, ht.2⟩
    refine ⟨?_, ?_⟩
    · have heq : 2 * p.d + 9 = (2 * p.d + 8) + 1 := by omega
      rw [heq]
      exact hstd.hD.smoothU α v hvH t hvt
    ·
      intro j hj
      refine ⟨c α, ?_⟩
      rintro _ ⟨x, rfl⟩
      exact hstd.hD.bddU α v hvH t hvt j (by omega) x
  induction S using Finset.induction_on with
  | empty =>
      change MemCb (2 * p.d + 9) (0 : Euc p.d → ℝ)
      simpa using chart_memCb_smul (0 : ℝ) (hb (0 : MultiIndex p.d))
  | @insert α S hα ih =>
      have hs := chart_memCb_sub (chart_memCb_smul (coeff α) (hb α))
        (chart_memCb_smul (-1 : ℝ) ih)
      convert hs using 1
      funext x
      simp [Finset.sum_insert, hα, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]

private theorem fp81s21_moving_clamped_orbit
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
      (2 * p.d + 8) c hH)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) H)
    {φ : Euc p.d → ℝ} (hφ : IsR2DualCombo (wholeSpaceIndex p.d : ℝ) φ) :
    let F := fun v => propagatorW (r26t3_coeff R) (Set.projIcc 0 t ht.1 v) t φ
    StronglyMeasurable (fun q : ℝ × Euc p.d => F q.1 q.2) ∧
      ∀ v, MemCb (2 * p.d + 9) (F v) := by
  have hex := fp81s21_adjoint_of_hermite_combo p R hφ ht.1
  have hcl := HRS.MS.Fcau.propagatorW_isClassical hex
  have hc := (chart_classical_value_continuous hcl).comp
    (((continuous_projIcc (h := ht.1)).comp continuous_fst).prodMk continuous_snd)
  exact ⟨hc.stronglyMeasurable, fun v =>
    fp81s21_moving_combo_memCb p R hH hstd ht (Set.projIcc 0 t ht.1 v).property hφ⟩

/-- Moving chart measurability follows from the standing orbit data and the
finite-combination classical adjoints, for the actual trajectory coefficient. -/
theorem fp81s21_moving_charted_orbits
    (p : Parameters) {δ H Pw : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
      (2 * p.d + 8) c hH)
    (hP : (p.d : ℝ) < 2 * Pw)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) Pw) :
    r26t6_ChartedOrbits E (r26t3_coeff R) (wholeSpaceIndex p.d) H := by
  let E' := nativeChartOfFrozen E
  change ChartedOrbits E' (r26t3_coeff R) (wholeSpaceIndex p.d) H
  constructor
  · intro ta tb φ ψ hφ hψ hta htb
    let F : ℝ → Euc p.d → ℝ := fun v =>
      propagatorW (r26t3_coeff R) (Set.projIcc 0 ta hta.1 v) ta φ
    let G : ℝ → Euc p.d → ℝ := fun v =>
      propagatorW (r26t3_coeff R) (Set.projIcc 0 tb htb.1 v) tb ψ
    obtain ⟨hF, hFr⟩ := fp81s21_moving_clamped_orbit p R hH hstd hta hφ
    obtain ⟨hG, hGr⟩ := fp81s21_moving_clamped_orbit p R hH hstd htb hψ
    have hgF := chart_joint_gradient F hF
      (fun v => (hFr v).1.differentiable (by positivity))
    have hgG := chart_joint_gradient G hG
      (fun v => (hGr v).1.differentiable (by positivity))
    have hpair : StronglyMeasurable (fun q : ℝ × Euc p.d =>
        inner ℝ (gradient (F q.1) q.2) (gradient (G q.1) q.2)) :=
      (hgF.measurable.inner hgG.measurable).stronglyMeasurable
    have henc := chart_encode_stronglyMeasurable E' hP
      (fun v x => inner ℝ (gradient (F v) x) (gradient (G v) x)) hpair
      (fun v => chart_memCb_gradient_inner (hFr v) (hGr v))
    apply henc.aestronglyMeasurable.congr
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with v hv
    have hva : v ∈ Icc (0 : ℝ) ta := ⟨hv.1, hv.2.trans (min_le_left _ _)⟩
    have hvb : v ∈ Icc (0 : ℝ) tb := ⟨hv.1, hv.2.trans (min_le_right _ _)⟩
    simp only [F, G, Set.projIcc_of_mem hta.1 hva, Set.projIcc_of_mem htb.1 hvb]
  · intro t ht φ hφ
    let F : ℝ → Euc p.d → ℝ := fun v =>
      propagatorW (r26t3_coeff R) (Set.projIcc 0 t ht.1 v) t φ
    obtain ⟨hF, hFr⟩ := fp81s21_moving_clamped_orbit p R hH hstd ht hφ
    have henc := chart_encode_stronglyMeasurable E' hP F hF
      (fun v => chart_memCb_mono (show 2 * p.d + 8 ≤ 2 * p.d + 9 by omega) (hFr v))
    apply henc.aestronglyMeasurable.congr
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with v hv
    simp only [F, Set.projIcc_of_mem ht.1 hv]

/-- The interval drift agrees with the packet-14 physical window increment
when the L¹ representative matches its field on the propagated basis tests. -/
theorem fp81s21_interval_drift_eq_physical
    {d r : ℕ} {Pw T a c K : ℝ} {C : WholeCoeff d}
    {E : r26t6_WeightedChart d r Pw}
    (O : r26t6_IntervalOperators E C T a c K)
    (q : r26t6_TimeCoeff (a + T)) {b : ℝ → (Euc d → ℝ) → ℝ} {Mb : ℝ → ℝ}
    {coef : MultiIndex d → ℝ}
    (ha : 0 ≤ a) (hT : 0 ≤ T) (hP : (d : ℝ) < 2 * Pw)
    (hD : HRS.MS.CovMeas.S101Data C (wholeSpaceIndex d) (a + T) r coef)
    (hlin : S102Lin C (wholeSpaceIndex d) (a + T))
    (hb : S102Drift C (wholeSpaceIndex d) (a + T) r Pw b Mb)
    (hq0 : ∀ᵐ s ∂volume.restrict (Icc 0 (a + T)),
      inner ℝ (q s) (E.encode (fun _ => 1)) = 0)
    {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) (hw : w ≤ a + T)
    (hrep : ∀ (τ : Icc (0 : ℝ) T) (α : MultiIndex d),
      ∀ᵐ s ∂volume.restrict (Ioc v (min w (a + τ))),
        r26t6_coefficientField E q s
          (propagatorW C s (a + τ) (oscTestFun (wholeSpaceIndex d) α)) =
        b s (propagatorW C s (a + τ) (oscTestFun (wholeSpaceIndex d) α))) :
    O.drift v w q = fp81s21_weightedDrift_windowInc ha le_rfl C b v w := by
  apply ContinuousMap.ext
  intro τ
  apply s102_ext
  intro α
  have ht : a + (τ : ℝ) ∈ Icc (0 : ℝ) (a + T) :=
    ⟨add_nonneg ha τ.property.1, by linarith [τ.property.2]⟩
  have hcoord := O.drift_coordinate q hq0 v w hv hvw hw τ
    (oscTestFun (wholeSpaceIndex d) α) (s102_isDualCombo α)
  rw [OscDual.eval_oscTestFun] at hcoord
  change OscDual.coord (OscPath.at' (O.drift v w q) τ) α =
    OscDual.coord (OscPath.at' (fp81s21_weightedDrift_windowInc ha le_rfl C b v w) τ) α
  rw [hcoord]
  have hset : Ioc v w ∩ Icc 0 (a + (τ : ℝ)) = Ioc v (min w (a + τ)) := by
    ext s
    simp only [mem_inter_iff, mem_Ioc, mem_Icc, le_min_iff]
    constructor
    · rintro ⟨⟨hvs, hsw⟩, h0, hst⟩
      exact ⟨hvs, hsw, hst⟩
    · rintro ⟨hvs, hsw, hst⟩
      exact ⟨⟨hvs, hsw⟩, hv.trans hvs.le, hst⟩
  rw [hset, integral_congr_ae (hrep τ α)]
  have hp := fp81s21_drift_increment_coord hP hD hlin hb
    (add_nonneg ha hT) hv (hv.trans hvw) ht α
  change (∫ s in Ioc v (min w (a + ↑τ)),
      b s (propagatorW C s (a + ↑τ) (oscTestFun (wholeSpaceIndex d) α))) =
    OscDual.coord (OscPath.at' (physicalWindowRestriction ha le_rfl
      (r2DriftInc C (wholeSpaceIndex d) (a + T) b v w)) τ) α
  rw [physicalWindowRestriction_apply]
  simpa [r2PathAt, ht, physicalWindowTime] using hp.symm

#print axioms fp81s21_interval_drift_eq_physical
#print axioms fp81s21_moving_charted_orbits
end HRS.Fp81.S21
end
