import HRS.ME.UIPath
import HRS.ME.UIPathShiftedQ1
import HRS.ME.UIPathShiftedQ2
import HRS.ME.UIPathShiftedQ3
import HRS.ME.UIPathShiftedQ4
import HRS.ME.UIPathTightP1

/-!
# Packet Q5b of `HRS.ui_path_shifted`: finite-dimensional distributions of the shifted windows converge

Statement copied verbatim from `HRS/ME/UIPathShiftedSpec.lean` (sorried there, independently reviewed).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.ME.UIPathShifted

open HRS HRS.Main

variable {d : ℕ}

/-- **Q5b** (finite-dimensional distributions of the shifted windows converge; scope note Q5). -/
theorem shifted_fidi_converge (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) (T : ℝ) (hT : 0 ≤ T) (S : ParticleSeq d)
    (hS : ∀ T' : ℝ, 0 ≤ T' → S.IsSolutionOn (PDE.mfData d s hs0 hsd V β hβ) T')
    (hSF : ∀ n, ∃ (ℱ : MeasureTheory.Filtration ℝ (S.mΩ n))
      (W' : ℝ≥0 → S.Ω n → (Fin (n + 2) × Fin d) → ℝ),
      IsFilteredSolution (S.P n) ℱ W' (S.W n) (S.X n))
    (hν : ∀ n, (S.P n).map (S.X₀ n) ≪ canonicalGibbs (periodicRiesz d s) V (n + 2) β)
    (hUI : Tendsto (uiTail d s β V (fun n => (S.P n).map (S.X₀ n))) atTop (𝓝 0))
    (m : ℝ) (hm : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m)
    (u : ℕ → ℝ) (hu0 : ∀ n, 0 ≤ u n) (hu : Tendsto u atTop atTop)
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → NegSobolev d m)
    (hZ : IsStationaryGaussianField P' s β hs0 hsd hβ V ρβ m Z)
    (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T)
    (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    TendstoInDistribution
      (fun n ω => (WithLp.toLp 2 fun a =>
        NegSobolev.eval
          ((windowGibbs m T (u n)
            (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) (S.X n) ω).at'
            ⟨ts a, hts a⟩) (φ a) : EuclideanSpace ℝ (Fin p)))
      atTop
      (fun ω' => (WithLp.toLp 2 fun a =>
        NegSobolev.eval ((windowPath m T 0 Z ω').at' ⟨ts a, hts a⟩) (φ a) :
        EuclideanSpace ℝ (Fin p)))
      S.P P' := by
  have hdm : (d : ℝ) < 2 * m := by
    have h1 : (d : ℝ) + 1 < m := lt_of_le_of_lt (le_max_left _ _) hm
    have h0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    linarith
  -- probability measures
  have hGp : ∀ n, IsProbabilityMeasure
      (canonicalGibbs (periodicRiesz d s) V (n + 2) β) := fun n =>
    HRS.MD.EQLawFlow.eqlaw_gibbs_prob hd hs0 hsd hV hβ (by omega)
  have hFp : ∀ n, IsProbabilityMeasure
      (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) := fun n => by
    haveI := hGp n
    unfold firstMarginal
    rw [dif_pos (by omega)]
    infer_instance
  -- the three vectors
  set Y : ∀ n, S.Ω n → EuclideanSpace ℝ (Fin p) := fun n ω => (WithLp.toLp 2 fun a =>
    linCoord (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) (φ a)
      (S.X n (u n + ts a).toNNReal ω) : EuclideanSpace ℝ (Fin p)) with hY
  set Zs : Ω' → EuclideanSpace ℝ (Fin p) := fun ω => (WithLp.toLp 2 fun a =>
    NegSobolev.eval (Z (ts a) ω) (φ a) : EuclideanSpace ℝ (Fin p)) with hZs
  have hevc : ∀ a, Continuous fun z : NegSobolev d m => NegSobolev.eval z (φ a) := fun a =>
    HRS.MD.EQGaussWindow.eqgw_eval_continuous (hφ a)
  have hZsm : Measurable Zs :=
    (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp
      (measurable_pi_iff.2 fun a => (hevc a).measurable.comp (hZ.meas _))
  have hYm : ∀ n, Measurable (Y n) := fun n => by
    haveI := hFp n
    refine (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp
      (measurable_pi_iff.2 fun a => ?_)
    have hφc : Continuous (φ a) := Torus.continuous_of_continuous_lift
      (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift (φ a)) from hφ a).continuous
    have hXm : Measurable (S.X n (u n + ts a).toNNReal) := ((hS T hT n).sol.adapted _)
    unfold linCoord
    refine Measurable.const_mul (Measurable.sub (Measurable.const_mul ?_ _) measurable_const) _
    exact Finset.measurable_sum _ fun i _ => hφc.measurable.comp (measurable_pi_apply i |>.comp hXm)
  -- Q4
  obtain ⟨hae4, hlaw4⟩ := windowPath_fidi_law hs0 hsd hβ V ρβ T P' Z hZ p ts hts φ hφ
  have hlawZs : law P' Zs = ProbabilityTheory.multivariateGaussian 0
      (PDE.stationaryLagCov d s β (PDE.mfData d s hs0 hsd V β hβ) ρβ ts φ) :=
    hZ.gaussian p ts φ (fun a => (hts a).1) hφ
  haveI : IsProbabilityMeasure (ProbabilityTheory.multivariateGaussian 0
      (PDE.stationaryLagCov d s β (PDE.mfData d s hs0 hsd V β hβ) ρβ ts φ)) := by
    rw [← hlawZs]; exact inferInstance
  -- Q2
  have hconv : TendstoInDistribution Y atTop Zs S.P P' := by
    refine tendstoInDistribution_of_smoothDist S.P Y (fun n => (hYm n).aemeasurable) P' Zs
      hZsm.aemeasurable
      (fun _ => ProbabilityTheory.multivariateGaussian 0
        (PDE.stationaryLagCov d s β (PDE.mfData d s hs0 hsd V β hβ) ρβ ts φ)) ?_ ?_
    · intro f
      refine tendsto_const_nhds.congr fun _ => ?_
      rw [← hlawZs]
      unfold law
      rw [integral_map hZsm.aemeasurable f.continuous.aestronglyMeasurable]
    · exact shifted_smoothDist_tendsto hd hs0 hsd hβ V hV ρβ hρβ hρS hρpos T hT p φ hφ S hS hSF hν
        hUI ts hts u hu0 hu
  -- glue
  refine hconv.congr (fun n => ?_) hae4.symm
  haveI := hFp n
  exact (windowGibbs_fidi_ae_eq (N := n + 2) (by omega) hdm T (u n)
    (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) (S.P n) (S.X n)
    (hS T hT n).sol.cont p ts hts φ hφ).symm

end HRS.ME.UIPathShifted
