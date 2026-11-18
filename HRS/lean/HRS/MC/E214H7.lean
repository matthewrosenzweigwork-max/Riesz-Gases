import HRS.MC.E214H6
import HRS.MD.EQGaussLyap

/-!
# E214H7: the bridge `BridgeHyp`

The stationary half `η̄` of a coupled pair (initial field `Ys₀` centred Gaussian with covariance
`susceptibilityCov(ρβ)`, a linear fluctuation solution for the frozen coefficients `ρ ≡ ρβ`) is a
`HRS.IsStationaryGaussianField`: its finite-dimensional vectors are `A + G` with `A = (⟨Ys₀, ψ_a⟩)_a` centred
Gaussian, `G` the Gaussian noise part independent of `Ys₀`, and the sum of the covariance matrices is
`stationaryLagCov` (`eqgld_cov_total`); the noise matrix is positive semidefinite (`noise_psd`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Matrix

namespace HRS.MC.E214H

open HRS HRS.Main HRS.Sec7 HRS.MC.E213Plan HRS.MD.EQGaussLyap HRS.MD.EQGaussLyapDet HRS.MD.EQGaussLyapDet2
  HRS.Uniform.Q54c

variable {d : ℕ}

theorem ae_continuousOn_Ici_of_nat' {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {E : Type*}
    [TopologicalSpace E] (Y : ℝ → Ω → E)
    (h : ∀ n : ℕ, ∀ᵐ ω ∂P, ContinuousOn (fun t => Y t ω) (Set.Icc (0 : ℝ) n)) :
    ∀ᵐ ω ∂P, ContinuousOn (fun t => Y t ω) (Set.Ici 0) := by
  have := ae_all_iff.2 h
  filter_upwards [this] with ω hω t ht
  obtain ⟨n, hn⟩ := exists_nat_gt t
  have hmem : Set.Icc (0 : ℝ) n ∈ 𝓝[Set.Ici 0] t := by
    have h3 := inter_mem_nhdsWithin (Set.Ici (0 : ℝ)) (Iio_mem_nhds hn)
    exact Filter.mem_of_superset h3 fun x hx => ⟨hx.1, hx.2.le⟩
  exact ((hω n).continuousWithinAt ⟨ht, hn.le⟩).mono_of_mem_nhdsWithin hmem

theorem bridge_proof (S : PreparedData d) (β₀ : ℝ) {m : ℝ} (hE : EdgeworthHyp S β₀ m) :
    BridgeHyp S β₀ hE := by
  classical
  intro Ω _ P _ Y₀ Ys₀ η ηs hpd
  set R := HRS.MC.E213A.regimeOfPrepared S β₀ hE with hR
  obtain ⟨hth, hsm, hpos⟩ := R.thermal
  have hd : 2 ≤ d := S.hd
  have hd1 : 1 ≤ d := by omega
  have hinit := hpd.2.1
  have hlin : ∀ T : ℝ, IsLinearFluctuationSolution P (PDE.mfData d S.s S.hs0 S.hsd S.V S.β S.hβ)
      (fun _ => R.ρβ) (rLvl d) S.β⁻¹ T Ys₀ ηs := hpd.2.2.2
  have hYm : Measurable (ηs 0) := (hlin 0).meas 0
  have hlin' : ∀ T : ℝ, IsLinearFluctuationSolution P (PDE.mfData d S.s S.hs0 S.hsd S.V S.β S.hβ)
      (fun _ => R.ρβ) (rLvl d) S.β⁻¹ T (ηs 0) ηs :=
    fun T => HRS.MC.E213P.e213p_linSol_init_zero _ _ (hlin T)
  have hinit' : IsCenteredGaussianWithCov (rLvl d) (P.map (ηs 0))
      (susceptibilityCov (periodicRiesz d S.s) (withDensityReal R.ρβ) S.β) := by
    rw [Measure.map_congr (hlin 0).init]; exact hinit
  refine ⟨fun t => (hlin 0).meas t, ?_, ?_⟩
  · exact ae_continuousOn_Ici_of_nat' P ηs fun n => (hlin n).cont
  intro p τ φ hτ hφ
  set D := PDE.mfData d S.s S.hs0 S.hsd S.V S.β S.hβ with hD
  set ρβ := R.ρβ with hρβdef
  have hρth : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ := hth
  have hprob : IsProbDensity ρβ := hρth.1
  set T' : ℝ := 1 + ∑ a, τ a with hT'
  have hsum0 : 0 ≤ ∑ a, τ a := Finset.sum_nonneg fun a _ => hτ a
  have hτS : ∀ a, τ a ∈ Set.Icc (0 : ℝ) T' := fun a =>
    ⟨hτ a, by
      have := Finset.single_le_sum (f := τ) (fun b _ => hτ b) (Finset.mem_univ a)
      rw [hT']; linarith⟩
  obtain ⟨hind, hlawG⟩ := (hlin' T').gaussian_part p τ φ hτS hφ
  set ψ : Fin p → Torus d → ℝ := fun a => propagator D (fun _ => ρβ) 0 (τ a) (φ a) with hψdef
  have hψ : ∀ a, Torus.IsSmooth (ψ a) := fun a =>
    eqgld_prop_smooth hd1 S.hs0 S.hsd S.V S.hV S.hβ ρβ hprob hsm hpos (φ a) (hφ a) 0 (τ a) le_rfl (hτ a)
  have hmφ : ∀ a, MemSobolev (rLvl d) (φ a) := fun a =>
    HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (hφ a) _
  have hmψ : ∀ a, MemSobolev (rLvl d) (ψ a) := fun a =>
    HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (hψ a) _
  obtain ⟨hPSDA, hcharA⟩ := eqgl_A_gauss P (ηs 0) hYm _ hinit' ψ hψ
  set A : Ω → EuclideanSpace ℝ (Fin p) := fun ω =>
    (WithLp.toLp 2 fun a => NegSobolev.eval (ηs 0 ω) (ψ a) : EuclideanSpace ℝ (Fin p)) with hA
  set G : Ω → EuclideanSpace ℝ (Fin p) := fun ω => WithLp.toLp 2 fun a =>
      NegSobolev.eval (ηs (τ a) ω) (φ a) - NegSobolev.eval (ηs 0 ω) (propagator D (fun _ => ρβ) 0 (τ a) (φ a))
    with hG
  set X : Ω → EuclideanSpace ℝ (Fin p) := fun ω =>
    (WithLp.toLp 2 fun a => NegSobolev.eval (ηs (τ a) ω) (φ a) : EuclideanSpace ℝ (Fin p)) with hXdef
  have hTm : Measurable (fun z : NegSobolev d (rLvl d) =>
      (WithLp.toLp 2 fun a => NegSobolev.eval z (ψ a) : EuclideanSpace ℝ (Fin p))) :=
    measurable_toLp_eval fun a => (eqgl_eval_cont (hmψ a)).measurable
  have hAm : Measurable A := hTm.comp hYm
  have hXm : Measurable X :=
    measurable_toLp_eval fun a => (eqgl_eval_cont (hmφ a)).measurable.comp ((hlin 0).meas _)
  have hGm : Measurable G := by
    refine measurable_toLp_eval fun a => ?_
    exact ((eqgl_eval_cont (hmφ a)).measurable.comp ((hlin 0).meas _)).sub
      ((eqgl_eval_cont (hmψ a)).measurable.comp hYm)
  have hindGA : IndepFun G A P := hind.comp measurable_id hTm
  have hXeq : X = fun ω => A ω + G ω := by
    funext ω
    refine PiLp.ext fun a => ?_
    simp only [hA, hG, hXdef, PiLp.add_apply, hψdef]
    ring
  -- the two covariance matrices
  set SA : Matrix (Fin p) (Fin p) ℝ := Matrix.of fun a b =>
    susceptibilityCov (periodicRiesz d S.s) (withDensityReal ρβ) S.β (ψ a) (ψ b) with hSA
  set Mn : Matrix (Fin p) (Fin p) ℝ := Matrix.of fun a b => 2 * S.β⁻¹ *
    ∫ σ in Set.Icc 0 (min (τ a) (τ b)), eqgld_E D ρβ (φ a) (φ b) (τ a) (τ b) σ with hMn
  have hPSDM : Mn.PosSemidef := noise_psd hd S.hs0 S.hsd S.V S.hV S.hβ ρβ hρth τ hτ φ hφ
  have hlawG' : P.map G = multivariateGaussian 0 Mn := hlawG
  have hcharG : ∀ ξ : EuclideanSpace ℝ (Fin p), charFun (P.map G) ξ =
      Complex.exp (-((ξ ⬝ᵥ Mn *ᵥ ξ : ℝ) : ℂ) / 2) := by
    intro ξ
    rw [hlawG', charFun_multivariateGaussian hPSDM]
    simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub, neg_div]
  have hPSD : (SA + Mn).PosSemidef := hPSDA.add hPSDM
  have hchar : ∀ ξ : EuclideanSpace ℝ (Fin p), charFun (P.map (fun ω => A ω + G ω)) ξ =
      Complex.exp (-((ξ ⬝ᵥ (SA + Mn) *ᵥ ξ : ℝ) : ℂ) / 2) := by
    intro ξ
    have h1 := congrFun (hindGA.symm.charFun_map_fun_add_eq_mul hAm.aemeasurable hGm.aemeasurable) ξ
    rw [h1, Pi.mul_apply, hcharA ξ, hcharG ξ, ← Complex.exp_add, Matrix.add_mulVec, dotProduct_add]
    congr 1
    push_cast
    ring
  have hlaw : P.map (fun ω => A ω + G ω) = multivariateGaussian 0 (SA + Mn) :=
    eq_multivariateGaussian P (hAm.add hGm) hPSD hchar
  have htot := eqgld_cov_total hd S.hs0 S.hsd S.V S.hV S.hβ ρβ hρth τ hτ φ hφ
  show P.map X = _
  rw [hXeq, hlaw]
  congr 1

end HRS.MC.E214H

end
