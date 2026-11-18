import HRS.ME.UIPath
import HRS.ME.UIPathInitialR1
import HRS.ME.UIPathInitialR2
import HRS.ME.UIPathInitialR3
import HRS.ME.UIPathInitialR4
import HRS.ME.UIPathShiftedQ2
import HRS.ME.UIPathTightP1
import HRS.ME.UIPathTightP6

/-!
# Packet IR5: `tendstoInDistribution_of_smoothDist`, `fidi_converges`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.ME.UIPathInitial

open HRS HRS.Main

variable {d : ℕ}

/-- **R5a** (generalised Q2: `d_{C²}`-closeness transfers convergence in law, in finite dimension).
If `Y_n ⇒ Z` in `ℝ^p`, `X_n` are a.e. measurable and `d_{C²}(law X_n, law Y_n) → 0`, then `X_n ⇒ Z`.
(AEMeasurability of `Y_n` and of `Z` is part of `TendstoInDistribution`; AEMeasurability of `X_n` is needed,
otherwise `law (P n) (X n)` is a Dirac mass.)  Route: `a9_fd_converges` (`HRS/Main/A9Aux29.lean:73`) with
`T = id` and the characteristic-function criterion `ProbabilityMeasure.tendsto_of_tendsto_charFun`. -/
theorem tendstoInDistribution_of_smoothDist {p : ℕ} {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Ω n → EuclideanSpace ℝ (Fin p)) (hX : ∀ n, AEMeasurable (X n) (P n))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : Ω' → EuclideanSpace ℝ (Fin p))
    (hYZ : TendstoInDistribution Y atTop Z P P')
    (hdist : Tendsto (fun n => smoothDist 2 (law (P n) (X n)) (law (P n) (Y n))) atTop (𝓝 0)) :
    TendstoInDistribution X atTop Z P P' := by
  have hZ := hYZ.aemeasurable_limit
  haveI : ∀ n, IsProbabilityMeasure (law (P n) (Y n)) := fun n =>
    (Measure.isProbabilityMeasure_map_iff (hYZ.forall_aemeasurable n)).2 inferInstance
  refine HRS.ME.UIPathShifted.tendstoInDistribution_of_smoothDist P X hX P' Z hZ
    (fun n => law (P n) (Y n)) ?_ hdist
  intro f
  have h := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ hYZ.forall_aemeasurable hZ).mp hYZ f
  simpa [law, integral_map (hYZ.forall_aemeasurable _) f.continuous.aestronglyMeasurable] using h

/-- **R5** (finite-dimensional convergence of the window; scope note, R5).  Under all hypotheses of
`ui_path_initial`, for fixed `p`, times `t_a ∈ [0,T]` and smooth tests `φ_a`, the finite-dimensional vector of the
Gibbs-centred window `(⟨(windowGibbs m T 0 μ_N^* (S.X n)) t_a, φ_a⟩)_a` converges in law to the finite-dimensional
vector `(⟨(toPath m T Y) t_a, φ_a⟩)_a` of the limit path.  This is exactly the `hfidi` hypothesis of
`adjk_convergence_of_tight_fidi_proof` for `Φ n = windowGibbs m T 0 μ_N^* (S.X n)`, `Ψ = toPath m T Y`.
Route: `R1` at each `n` (with `hS 0`, `Γ = noiseCovMatrix …`, `choose`) gives `G n`; `R4` gives `G'`; `R3`
gives `R3`-convergence of the comparison vector; `R2` gives the `d_{C²}` distance `→ 0`; `R5a` transfers the
convergence to the window vector; the limit vector is replaced by the path vector by `R4` (a.e. equality, laws
agree by `Measure.map_congr`, `TendstoInDistribution` is invariant by a.e. equality of the limit map). -/
theorem fidi_converges (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
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
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η₀ : Ω' → NegSobolev d m)
    (hlaw : TendstoInDistribution
      (fun n ω => etaE m (S.X₀ n ω)
        (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)))
      atTop η₀ S.P P')
    (Y : ℝ → Ω' → NegSobolev d m)
    (hY : IsLinearFluctuationSolution P' (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) m β⁻¹ T η₀ Y)
    (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T)
    (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    TendstoInDistribution
      (fun n ω => (WithLp.toLp 2 fun a =>
        NegSobolev.eval ((windowGibbs m T 0
          (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) (S.X n) ω).at'
            ⟨ts a, hts a⟩) (φ a) : EuclideanSpace ℝ (Fin p)))
      atTop
      (fun ω' => (WithLp.toLp 2 fun a =>
        NegSobolev.eval ((toPath m T Y ω').at' ⟨ts a, hts a⟩) (φ a) : EuclideanSpace ℝ (Fin p)))
      S.P P' := by
  classical
  have hmn : (d : ℝ) < 2 * m := by
    have := lt_of_le_of_lt (le_max_right ((d : ℝ) + 1) ((d : ℝ) / 2 + 2)) hm
    linarith
  -- independent Gaussian vectors
  have hex : ∀ n, ∃ G : S.Ω n → EuclideanSpace ℝ (Fin p), AEMeasurable G (S.P n) ∧
      law (S.P n) G = ProbabilityTheory.multivariateGaussian 0
        (noiseCovMatrix (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) β⁻¹ ts φ) ∧
      ProbabilityTheory.IndepFun (S.X₀ n) G (S.P n) := fun n =>
    exists_indep_gaussian (by omega) S n _ 0 (hS 0 le_rfl n) _
  choose G hGm hG hGi using hex
  obtain ⟨G', hG'm, hG', hG'i, hae⟩ := limit_vector_identification hd hs0 hsd hβ V hV ρβ hρβ hρS hρpos
    T hT m hm Ω' P' η₀ Y hY p ts hts φ hφ
  have hR3 := comparison_vector_converges hd hs0 hsd hβ V hV ρβ hρβ hρS hρpos T S m hm Ω' P' η₀ hlaw
    p ts hts φ hφ G hG hGm hGi G' hG' hG'm hG'i
  have hR2 := window_vector_vs_comparison hd hs0 hsd hβ V hV ρβ hρβ hρS hρpos T hT S hS hSF hν hUI m hm
    p ts hts φ hφ G hG hGm hGi
  -- measurability of the window vector
  have hX : ∀ n, AEMeasurable (fun ω => (WithLp.toLp 2 fun a =>
        NegSobolev.eval ((windowGibbs m T 0
          (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) (S.X n) ω).at'
            ⟨ts a, hts a⟩) (φ a) : EuclideanSpace ℝ (Fin p))) (S.P n) := by
    intro n
    haveI : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V (n + 2) β) :=
      HRS.MD.EQLawFlow.eqlaw_gibbs_prob (by omega) hs0 hsd hV hβ (by omega)
    haveI : IsProbabilityMeasure
        (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) :=
      HRS.MD.EQTransShift.et_firstMarginal_isProb (by omega) _
    have hw := HRS.ME.UIPathTight.windowGibbs_aemeasurable (by omega : 1 ≤ n + 2) hmn T 0
      (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) (S.P n)
      (PDE.mfData d s hs0 hsd V β hβ) T (S.X₀ n) (S.W n) (S.X n) (hS T hT n).sol
    have hc : Continuous fun w : PathSpace d m T => (WithLp.toLp 2 fun a =>
        NegSobolev.eval (w.at' ⟨ts a, hts a⟩) (φ a) : EuclideanSpace ℝ (Fin p)) := by
      have hat : ∀ a, Continuous fun w : PathSpace d m T => w.at' ⟨ts a, hts a⟩ := fun a => by
        show Continuous fun w : C(Set.Icc (0 : ℝ) T, NegSobolev d m) => w ⟨ts a, hts a⟩
        exact continuous_eval_const _
      exact (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).comp
        (continuous_pi fun a => (HRS.MD.EQGaussWindow.eqgw_eval_continuous (hφ a)).comp (hat a))
    exact hc.measurable.comp_aemeasurable hw
  have h5 := tendstoInDistribution_of_smoothDist S.P _ _ hX P' _ hR3 hR2
  exact h5.congr (fun n => Filter.EventuallyEq.rfl) hae

end HRS.ME.UIPathInitial
