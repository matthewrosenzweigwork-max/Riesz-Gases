import HRS.ME.UIPath
import HRS.ME.UIPathShiftedQ3
import HRS.ME.UIFinal
import HRS.MD.EQTransShift

/-!
# Packet IR2: `window_vector_vs_comparison`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.ME.UIPathInitial

open HRS HRS.Main

variable {d : ℕ}

/-- **R2** (path-form window vector vs. the comparison vector; scope note, R2 together with the a.s. identity
of the fidi vector).  For fixed smooth tests `φ_a` and times `t_a ∈ [0,T]` and for ANY choice of independent
Gaussian vectors `G n` with the noise covariance (hypotheses `hG, hGm, hGi` exactly as in `ui_qualitative`),
the `d_{C²}` distance between the law of the finite-dimensional vector of the Gibbs-centred window
`(⟨(windowGibbs m T 0 μ_N^* (S.X n)) t_a, φ_a⟩)_a` (the evaluation in `E_m` of the path `at' t_a`, which is the
quantity used by `adjk_convergence_of_tight_fidi_proof`) and the law of the comparison vector
`(⟨U^{0,t_a}φ_a, η_N^0⟩ + G_n)_a` (`linCoord` form, as in `ui_comparison`) tends to `0`.  Both laws are those
of AEMeasurable maps, so no junk Dirac masses (`windowGibbs` is a.e. equal to the continuous window).
Route: `ui_qualitative_proof` clause 1 (`HRS/ME/UIFinal.lean:28`); the window vector equals
`linCoord μ_N^* φ_a (S.X n t_a)` a.s. by `mp_linCoord_eq_eval` (needs `d < 2m` and `φ_a` smooth) and the a.s.
continuity of the window (`IsStrongSolution`, as in `UIPathTight.windowGibbs_aemeasurable`); laws of a.e.
equal maps agree (`Measure.map_congr`). -/
theorem window_vector_vs_comparison (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
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
    (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T)
    (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a))
    (G : ∀ n, S.Ω n → EuclideanSpace ℝ (Fin p))
    (hG : ∀ n, law (S.P n) (G n) = ProbabilityTheory.multivariateGaussian 0
      (noiseCovMatrix (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) β⁻¹ ts φ))
    (hGm : ∀ n, AEMeasurable (G n) (S.P n))
    (hGi : ∀ n, ProbabilityTheory.IndepFun (S.X₀ n) (G n) (S.P n)) :
    Tendsto (fun n => smoothDist 2
        (law (S.P n) fun ω => (WithLp.toLp 2 fun a =>
          NegSobolev.eval ((windowGibbs m T 0
            (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) (S.X n) ω).at'
              ⟨ts a, hts a⟩) (φ a) : EuclideanSpace ℝ (Fin p)))
        (law (S.P n) fun ω => (WithLp.toLp 2 fun a =>
          linCoord (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β))
            (propagator (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) 0 (ts a) (φ a))
            (S.X₀ n ω) + G n ω a : EuclideanSpace ℝ (Fin p)))) atTop (𝓝 0) := by
  have hq := HRS.ME.Ret.ui_qualitative_proof (d := d) hd hs0 hsd hβ V hV ρβ hρβ hρS hρpos T hT p φ hφ S hS hSF hν hUI
    ts hts G hG hGm hGi (fun n => (n : ℝ)) (fun n => Nat.cast_nonneg n) tendsto_natCast_atTop_atTop
  refine hq.1.congr (fun n => ?_)
  have hmd : (d : ℝ) < 2 * m := by
    have h1 : (d : ℝ) / 2 + 2 < m := lt_of_le_of_lt (le_max_right _ _) hm
    linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hc := (hS T hT n).sol.cont
  haveI := HRS.MD.EQTransShift.et_gibbs_prob hd hs0 hsd V hV hβ hρβ (N := n + 2) (by omega)
  haveI : IsProbabilityMeasure
      (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) :=
    HRS.MD.EQTransShift.et_firstMarginal_isProb (by omega) _
  have hae := HRS.ME.UIPathShifted.windowGibbs_fidi_ae_eq (N := n + 2) (by omega) hmd T 0
    (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) (S.P n) (S.X n) hc p ts hts φ hφ
  have : (S.P n).map (fun ω => (WithLp.toLp 2 fun a =>
          NegSobolev.eval ((windowGibbs m T 0
            (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) (S.X n) ω).at'
              ⟨ts a, hts a⟩) (φ a) : EuclideanSpace ℝ (Fin p))) =
      (S.P n).map (fun ω => (WithLp.toLp 2 fun a =>
          linCoord (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) (φ a)
            (S.X n (ts a).toNNReal ω) : EuclideanSpace ℝ (Fin p))) := by
    refine Measure.map_congr ?_
    simpa only [zero_add] using hae
  exact congrArg (fun μ => smoothDist 2 μ _) this.symm

end HRS.ME.UIPathInitial
