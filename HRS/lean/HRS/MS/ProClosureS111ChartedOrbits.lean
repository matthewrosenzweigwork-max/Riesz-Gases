import HRS.MS.ProClosureS111ChartMeas
import HRS.MS.ProClosureS111OscOrbitApprox
import HRS.MS.R26T6CD03

/-!
The actual thermal propagator satisfies the charted-orbit measurability
premise of the accepted interval construction, for every weighted chart.
The chart axioms themselves imply continuity in the weighted test norm;
jointly measurable spatial derivatives imply measurability of that norm.
No physical charted-orbit premise is assumed here.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.S111X1 HRS.MS.S111K4J01

variable {d : ℕ}

theorem dualCombo_isOscTest {m : ℝ} {phi : Euc d → ℝ}
    (hphi : IsR2DualCombo m phi) : IsOscTest m phi := by
  obtain ⟨S, c, rfl⟩ := hphi
  have he : (fun x : Euc d => ∑ alpha ∈ S, c alpha * oscTestFun m alpha x) =
      ∑ alpha ∈ S, c alpha • oscTestFun m alpha := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he, ← mem_oscSub]
  exact Submodule.sum_mem _ fun alpha _ => Submodule.smul_mem _ _
    (mem_oscSub.2 (HRS.MS.GenPath.s56_isOscTest m alpha))

theorem chart_classical_value_continuous {C : WholeCoeff d} {t : ℝ}
    {phi : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t phi f) :
    Continuous (fun p : Icc (0 : ℝ) t × Euc d => f p.1 p.2) := by
  have h := (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).continuous.comp
    (hf.cont_c2 0 (by norm_num))
  convert h using 1
  funext p
  simp

theorem chart_joint_gradient {A : Type*} [MeasurableSpace A]
    (F : A → Euc d → ℝ)
    (hF : StronglyMeasurable (fun p : A × Euc d => F p.1 p.2))
    (hreg : ∀ a, Differentiable ℝ (F a)) :
    StronglyMeasurable (fun p : A × Euc d => gradient (F p.1) p.2) := by
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp_stronglyMeasurable
    (HRS.MS.PoisSg.sg_stronglyMeasurable_fderiv F hF hreg)

/-- Extending the initial-time parameter by clamping retains joint
measurability and every bounded spatial jet needed by the chart. -/
theorem physical_clamped_orbit (hd : 2 ≤ d)
    {s a beta : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ))
    (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d s a beta rho)
    {H t : ℝ} (ht : t ∈ Icc (0 : ℝ) H)
    {phi : Euc d → ℝ} (hphi : IsOscTest (wholeSpaceIndex d) phi) :
    let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
    let F := fun v => propagatorW C (Set.projIcc 0 t ht.1 v) t phi
    StronglyMeasurable (fun p : ℝ × Euc d => F p.1 p.2) ∧
      ∀ v, MemCb (2 * d + 9) (F v) := by
  let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
  obtain ⟨B, hB, hb⟩ := physical_oscillator_cb_bound hd hs0 hsd ha hbeta hrho
    (ht.1.trans ht.2)
  have hex := (hb phi hphi 0 t le_rfl ht.1 ht.2).1
  have hcl : IsClassicalAdjointW C t phi (fun v => propagatorW C v t phi) :=
    HRS.MS.S52B.s52b_prop_isClassical hex
  have hcont : Continuous (fun p : ℝ × Euc d =>
      propagatorW C (Set.projIcc 0 t ht.1 p.1) t phi p.2) :=
    (chart_classical_value_continuous hcl).comp
      (((continuous_projIcc (h := ht.1)).comp continuous_fst).prodMk continuous_snd)
  refine ⟨hcont.stronglyMeasurable, fun v => ?_⟩
  exact (hb phi hphi (Set.projIcc 0 t ht.1 v) t
    (Set.projIcc 0 t ht.1 v).property.1
    (Set.projIcc 0 t ht.1 v).property.2 ht.2).2.1

/-- Actual charted orbits, uniformly in the choice of weighted chart. The
only weight restriction is the integrability needed for bounded jets. -/
theorem physical_charted_orbits (hd : 2 ≤ d)
    {s a beta : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ))
    (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d s a beta rho)
    {H Pw : ℝ} (hH : 0 ≤ H) (hP : (d : ℝ) < 2 * Pw)
    (E : WeightedChart d (2 * d + 8) Pw) :
    ChartedOrbits E ((quadraticGradientDyn d s a beta).coeff (fun _ => rho))
      (wholeSpaceIndex d) H := by
  let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
  constructor
  · intro ta tb phi psi hphi hpsi hta htb
    let F : ℝ → Euc d → ℝ := fun v => propagatorW C (Set.projIcc 0 ta hta.1 v) ta phi
    let G : ℝ → Euc d → ℝ := fun v => propagatorW C (Set.projIcc 0 tb htb.1 v) tb psi
    obtain ⟨hF, hFr⟩ := physical_clamped_orbit hd hs0 hsd ha hbeta hrho hta
      (dualCombo_isOscTest hphi)
    obtain ⟨hG, hGr⟩ := physical_clamped_orbit hd hs0 hsd ha hbeta hrho htb
      (dualCombo_isOscTest hpsi)
    have hgF := chart_joint_gradient F hF
      (fun v => (hFr v).1.differentiable (by positivity))
    have hgG := chart_joint_gradient G hG
      (fun v => (hGr v).1.differentiable (by positivity))
    have hpair : StronglyMeasurable (fun p : ℝ × Euc d =>
        inner ℝ (gradient (F p.1) p.2) (gradient (G p.1) p.2)) :=
      (hgF.measurable.inner hgG.measurable).stronglyMeasurable
    have henc := chart_encode_stronglyMeasurable E hP
      (fun v x => inner ℝ (gradient (F v) x) (gradient (G v) x)) hpair
      (fun v => chart_memCb_gradient_inner (hFr v) (hGr v))
    apply henc.aestronglyMeasurable.congr
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with v hv
    have hva : v ∈ Icc (0 : ℝ) ta := ⟨hv.1, hv.2.trans (min_le_left _ _)⟩
    have hvb : v ∈ Icc (0 : ℝ) tb := ⟨hv.1, hv.2.trans (min_le_right _ _)⟩
    simp only [F, G, C, Set.projIcc_of_mem hta.1 hva, Set.projIcc_of_mem htb.1 hvb]
  · intro t ht phi hphi
    let F : ℝ → Euc d → ℝ := fun v => propagatorW C (Set.projIcc 0 t ht.1 v) t phi
    obtain ⟨hF, hFr⟩ := physical_clamped_orbit hd hs0 hsd ha hbeta hrho ht
      (dualCombo_isOscTest hphi)
    have henc := chart_encode_stronglyMeasurable E hP F hF
      (fun v => chart_memCb_mono (show 2 * d + 8 ≤ 2 * d + 9 by omega) (hFr v))
    apply henc.aestronglyMeasurable.congr
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with v hv
    simp only [F, C, Set.projIcc_of_mem ht.1 hv]

/-- The frozen chart and the accepted interval chart have identical data.
This conversion changes only the structure name. -/
def nativeChartOfFrozen {r : ℕ} {Pw : ℝ}
    (E : HRS.MS.R26T6.r26t6_WeightedChart d r Pw) : WeightedChart d r Pw where
  encode := E.encode
  test := E.test
  add := E.add
  smul := E.smul
  norm := E.norm
  test_smooth := E.test_smooth
  test_coord := E.test_coord
  dense := E.dense

theorem physical_frozen_charted_orbits (hd : 2 ≤ d)
    {s a beta : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ))
    (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d s a beta rho)
    {H Pw : ℝ} (hH : 0 ≤ H) (hP : (d : ℝ) < 2 * Pw)
    (E : HRS.MS.R26T6.r26t6_WeightedChart d (2 * d + 8) Pw) :
    HRS.MS.R26T6.r26t6_ChartedOrbits E
      ((quadraticGradientDyn d s a beta).coeff (fun _ => rho))
      (wholeSpaceIndex d) H :=
  physical_charted_orbits hd hs0 hsd ha hbeta hrho hH hP (nativeChartOfFrozen E)

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.physical_charted_orbits
#print axioms HRS.MS.ProClosureS111.physical_frozen_charted_orbits
