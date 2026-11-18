import HRS.ME.UIPath
import HRS.MD.EQGaussLyapDet
import HRS.MD.EQTransShift
import HRS.MD.EQLawPath
import HRS.Main.MeanPartMetricEval
import HRS.Uniform.Q54cAux43
import HRS.PDE.MeanFieldSemigroup

/-!
# Packet IR3 of `HRS.ui_path_initial`: convergence in law of the comparison vector

Proof of `comparison_vector_converges` (statement frozen in `HRS/ME/UIPathInitialSpec.lean`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.ME.UIPathInitial

open HRS HRS.Main

variable {d : ℕ}

/-- `TendstoInDistribution` only depends on the maps pointwise. -/
theorem p_ir3_congr {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X X' : ∀ n, Ω n → E} {Z Z' : Ω' → E} (hX : ∀ n ω, X n ω = X' n ω) (hZ : ∀ ω, Z ω = Z' ω)
    (h : TendstoInDistribution X atTop Z P P') : TendstoInDistribution X' atTop Z' P P' := by
  obtain rfl : X = X' := funext fun n => funext (hX n)
  obtain rfl : Z = Z' := funext hZ
  exact h

/-- Sum of a convergent sequence and an independent fixed-law summand (characteristic functions). -/
theorem p_ir3_tendsto_add {p : ℕ} {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    (U G : ∀ n, Ω n → EuclideanSpace ℝ (Fin p)) (U' G' : Ω' → EuclideanSpace ℝ (Fin p))
    (hU : TendstoInDistribution U atTop U' P P')
    (hGm : ∀ n, AEMeasurable (G n) (P n)) (hG'm : AEMeasurable G' P')
    (hGi : ∀ n, IndepFun (U n) (G n) (P n))
    (hlaw : ∀ n, (P n).map (G n) = P'.map G')
    (hG'i : IndepFun U' G' P') :
    TendstoInDistribution (fun n ω => U n ω + G n ω) atTop (fun ω' => U' ω' + G' ω') P P' := by
  refine TendstoInDistribution.of_tendsto_charFun
    (fun n => (hU.forall_aemeasurable n).add (hGm n)) (hU.aemeasurable_limit.add hG'm) fun t => ?_
  have h1 : ∀ n, charFun ((P n).map (fun ω => U n ω + G n ω)) t =
      charFun ((P n).map (U n)) t * charFun (P'.map G') t := by
    intro n
    rw [(hGi n).charFun_map_fun_add_eq_mul (hU.forall_aemeasurable n) (hGm n), ← hlaw n]
    rfl
  have h2 : charFun (P'.map (fun ω => U' ω + G' ω)) t =
      charFun (P'.map U') t * charFun (P'.map G') t := by
    rw [hG'i.charFun_map_fun_add_eq_mul hU.aemeasurable_limit hG'm]
    rfl
  simp_rw [h1, h2]
  exact (hU.tendsto_charFun t).mul_const _

/-- **R3** (convergence in law of the comparison vector; scope note, R3).  If the initial fields
`η_N^0 = √N(μ_N^0 - m_{N,β})` converge in law to `η₀` (`hlaw`), and `G n` (independent of `S.X₀ n`, with the
noise-covariance Gaussian law) and `G'` (independent of `η₀`, same law) are Gaussian vectors, then the
comparison vectors `(⟨U^{0,t_a}φ_a, η_N^0⟩ + G_n)_a` (`linCoord` form) converge in law to
`(⟨U^{0,t_a}φ_a, η₀⟩ + G')_a`.  AEMeasurability of every term is part of `TendstoInDistribution`
(`η_N^0` through `hlaw.forall_aemeasurable`, `η₀` through `hlaw.aemeasurable_limit`).  The propagator is
smooth for smooth `φ_a` (`eqgld_prop_smooth`, `HRS/MD/EQGaussLyapDet.lean`), so `η ↦ ⟨U^{0,t_a}φ_a, η⟩` is a
continuous linear functional on `E_m`.  Route: `mp_linCoord_eq_eval` (centre `μ_N^*` both for `linCoord` and for
`etaE`), continuous mapping of `hlaw`, the pair `(η_N^0, G_n)` has the product law (independence) and
`law (G n) = law G'` is fixed, so the product converges; the sum is continuous. -/
theorem comparison_vector_converges (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) (T : ℝ) (S : ParticleSeq d)
    (m : ℝ) (hm : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m)
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η₀ : Ω' → NegSobolev d m)
    (hlaw : TendstoInDistribution
      (fun n ω => etaE m (S.X₀ n ω)
        (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)))
      atTop η₀ S.P P')
    (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T)
    (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a))
    (G : ∀ n, S.Ω n → EuclideanSpace ℝ (Fin p))
    (hG : ∀ n, law (S.P n) (G n) = ProbabilityTheory.multivariateGaussian 0
      (noiseCovMatrix (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) β⁻¹ ts φ))
    (hGm : ∀ n, AEMeasurable (G n) (S.P n))
    (hGi : ∀ n, ProbabilityTheory.IndepFun (S.X₀ n) (G n) (S.P n))
    (G' : Ω' → EuclideanSpace ℝ (Fin p))
    (hG' : law P' G' = ProbabilityTheory.multivariateGaussian 0
      (noiseCovMatrix (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) β⁻¹ ts φ))
    (hG'm : AEMeasurable G' P')
    (hG'i : ProbabilityTheory.IndepFun η₀ G' P') :
    TendstoInDistribution
      (fun n ω => (WithLp.toLp 2 fun a =>
        linCoord (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β))
          (propagator (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) 0 (ts a) (φ a))
          (S.X₀ n ω) + G n ω a : EuclideanSpace ℝ (Fin p)))
      atTop
      (fun ω' => (WithLp.toLp 2 fun a =>
        NegSobolev.eval (η₀ ω') (propagator (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) 0 (ts a) (φ a))
          + G' ω' a : EuclideanSpace ℝ (Fin p)))
      S.P P' := by
  classical
  have hm2 : (d : ℝ) < 2 * m := by
    have h1 := lt_of_le_of_lt (le_max_right ((d : ℝ) + 1) ((d : ℝ) / 2 + 2)) hm
    linarith
  set ψ : Fin p → Torus d → ℝ := fun a =>
    propagator (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) 0 (ts a) (φ a) with hψ
  have hψs : ∀ a, Torus.IsSmooth (ψ a) := fun a =>
    HRS.MD.EQGaussLyapDet.eqgld_prop_smooth (by omega) hs0 hsd V hV hβ ρβ hρβ.1 hρS hρpos (φ a)
      (hφ a) 0 (ts a) le_rfl (hts a).1
  set Φ : NegSobolev d m → EuclideanSpace ℝ (Fin p) := fun η =>
    WithLp.toLp 2 fun a => NegSobolev.eval η (ψ a) with hΦ
  have hΦc : Continuous Φ :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun a =>
      HRS.Uniform.Q54c.continuous_eval_const (HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (hψs a) m))
  have hU := hlaw.continuous_comp hΦc
  -- the pointwise identification of the comparison vector
  have hlin : ∀ n ω, (WithLp.toLp 2 fun a =>
        linCoord (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) (ψ a)
          (S.X₀ n ω) : EuclideanSpace ℝ (Fin p)) =
      Φ (etaE m (S.X₀ n ω) (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β))) := by
    intro n ω
    have := HRS.MD.EQTransShift.et_gibbs_prob hd hs0 hsd V hV hβ hρβ (by omega : 0 < n + 2)
    have := HRS.MD.EQTransShift.et_firstMarginal_isProb (by omega : 0 < n + 2)
      (canonicalGibbs (periodicRiesz d s) V (n + 2) β)
    refine congrArg (WithLp.toLp 2) (funext fun a => ?_)
    have key := mp_linCoord_eq_eval (d := d) hm2 (by omega : 0 < n + 2)
      (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β))
      (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) (ψ a) (hψs a) (S.X₀ n ω)
    rw [key, sub_self, mul_zero, add_zero]
    first | rfl | simp [etaE, flucE, NegSobolev.scaledFluc]
  have hη : ∀ n, Continuous fun Y : Config d (n + 2) => Φ (etaE m Y
      (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β))) := by
    intro n
    have := HRS.MD.EQTransShift.et_gibbs_prob hd hs0 hsd V hV hβ hρβ (by omega : 0 < n + 2)
    have := HRS.MD.EQTransShift.et_firstMarginal_isProb (by omega : 0 < n + 2)
      (canonicalGibbs (periodicRiesz d s) V (n + 2) β)
    exact hΦc.comp ((HRS.MD.EQLawPath.eqlaw_continuous_ofMeasureDiff_empirical hm2 _
      (by omega : 0 < n + 2)).const_smul (Real.sqrt (n + 2 : ℕ)))
  have hmain := p_ir3_tendsto_add
    (fun n ω => Φ (etaE m (S.X₀ n ω)
      (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β))))
    G (fun ω' => Φ (η₀ ω')) G' hU hGm hG'm ?_ ?_ ?_
  · refine p_ir3_congr (fun n ω => ?_) (fun ω' => ?_) hmain
    · rw [← hlin n ω]
      ext a
      simp
      rfl
    · ext a
      simp [hΦ]
      rfl
  · intro n
    exact (hGi n).comp (hη n).measurable measurable_id
  · intro n
    exact (hG n).trans hG'.symm
  · exact hG'i.comp hΦc.measurable measurable_id

end HRS.ME.UIPathInitial
