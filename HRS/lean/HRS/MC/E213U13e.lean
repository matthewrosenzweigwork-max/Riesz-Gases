import HRS.MC.E213U13d
import HRS.MC.E213U11e
import HRS.MC.E213P
import HRS.MC.S7PIF4A

/-!
# Packet e213u13, file e: finite-dimensional Gaussianity of the Fourier coefficients of the limit field

For an `IsGaussianLimitField` `η`, the vectors `(η_{t_a}(e_{k_a}))_a` (`t_a ≥ 0`) are centred Gaussian vectors:
`η_t(φ) = G_t(φ) + η_0(U^{0,t}φ)` with `G` a Gaussian family independent of the Gaussian `η_0`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U13

open HRS HRS.Main HRS.T25P HRS.Sec7

variable {d : ℕ}

theorem fdd_gaussian (S : PreparedData d) (β₀ r : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (η : ℝ → Ω → NegSobolev d r)
    (hη : IsGaussianLimitField S.dyn S.ρ (withDensityReal S.ρ0) β₀ r P η)
    (p : ℕ) (ts : Fin p → ℝ) (ks : Fin p → NonzeroLattice d) (hts : ∀ a, 0 ≤ ts a) :
    HasGaussianLaw (fun ω (a : Fin p) => NegSobolev.fourierCoeff (η (ts a) ω) (ks a)) P ∧
      ∀ a, ∫ ω, NegSobolev.fourierCoeff (η (ts a) ω) (ks a) ∂P = 0 := by
  classical
  obtain ⟨Y₀, hY₀cov, hlin⟩ := hη
  set T : ℝ := ∑ a, ts a + 1 with hTdef
  have hT : ∀ a, ts a ∈ Set.Icc 0 T := fun a =>
    ⟨hts a, by
      have : ts a ≤ ∑ b, ts b :=
        Finset.single_le_sum (f := ts) (fun b _ => hts b) (Finset.mem_univ a)
      linarith⟩
  have hsol := HRS.MC.E213P.e213p_linSol_init_zero S.dyn S.ρ (hlin T)
  have hae : η 0 =ᵐ[P] Y₀ := (hlin 0).init
  have hν₀ : IsCenteredGaussian (P.map (η 0)) := by
    rw [Measure.map_congr hae]; exact hY₀cov.1
  have hG0 : IsGaussian (P.map (η 0)) := hν₀.1
  have hmeas0 : Measurable (η 0) := (hlin 0).meas 0
  have hHG0 : HasGaussianLaw (η 0) P := IsGaussian.hasGaussianLaw hmeas0.aemeasurable
  set φ : Fin p → Torus d → ℝ := fun a => Torus.realMode (ks a) with hφdef
  have hφ : ∀ a, Torus.IsSmooth (φ a) := fun a => HRS.Uniform.Q48b.q48b_isSmooth_realMode (ks a)
  have htr := HRS.T25.t25_traj S
  obtain ⟨Cr, cr, hCr, hcr, VA, hdualA, -, hdecA, -⟩ :=
    HRS.AdjK.adjk_evolution_along_trajectory S.hd htr r
  have hKb : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖VA t u‖ ≤ Cr := by
    intro u t hu hut
    refine (hdecA u t hu hut).trans ?_
    have h1 : Real.exp (-cr * (t - u)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sub_nonneg.2 hut]
    nlinarith
  have hmemU : ∀ a, MemSobolev r (propagator htr.dyn S.ρ 0 (ts a) (φ a)) := fun a =>
    HRS.T25P.t25p_memSobolev_propagator S.hd htr hdualA hCr.le le_rfl (hts a) (hKb 0 (ts a) le_rfl (hts a))
      (hφ a)
  obtain ⟨hind, hlawG⟩ := hsol.gaussian_part p ts φ hT hφ
  have hWs : ∀ a, HRS.A33.A33WS r (propagator htr.dyn S.ρ 0 (ts a) (φ a)) := fun a =>
    HRS.A33.a33_ws_of_memSobolev (hmemU a)
  have hWφ : ∀ a, HRS.A33.A33WS r (φ a) := fun a => HRS.A33.a33_ws_smooth r (hφ a)
  set ℓ : Fin p → NegSobolev d r →L[ℝ] ℝ := fun a => HRS.MC.Sec7.S7PIF4.S7PIF4_evalCLM r (hWs a) with hℓ
  set ℓ' : Fin p → NegSobolev d r →L[ℝ] ℝ := fun a => HRS.MC.Sec7.S7PIF4.S7PIF4_evalCLM r (hWφ a) with hℓ'
  set G : Ω → EuclideanSpace ℝ (Fin p) := fun ω => WithLp.toLp 2 fun a =>
      NegSobolev.eval (η (ts a) ω) (φ a) -
        NegSobolev.eval (η 0 ω) (propagator htr.dyn S.ρ 0 (ts a) (φ a)) with hGdef
  have hind' : IndepFun G (η 0) P := hind
  have hlawG' : P.map G = multivariateGaussian 0 (Matrix.of fun a b =>
      2 * S.dyn.invβ * ∫ r in Set.Icc 0 (min (ts a) (ts b)), ∫ x,
        inner ℝ (Torus.grad (propagator htr.dyn S.ρ r (ts a) (φ a)) x)
          (Torus.grad (propagator htr.dyn S.ρ r (ts b) (φ b)) x) * S.ρ r x) := hlawG
  have hGm : Measurable G := by
    refine HRS.Uniform.Q54c.measurable_toLp_eval fun a => ?_
    have h1 : Measurable fun ω => NegSobolev.eval (η (ts a) ω) (φ a) :=
      (ℓ' a).continuous.measurable.comp ((hlin T).meas (ts a))
    have h2 : Measurable fun ω => NegSobolev.eval (η 0 ω) (propagator htr.dyn S.ρ 0 (ts a) (φ a)) :=
      (ℓ a).continuous.measurable.comp hmeas0
    exact h1.sub h2
  have hGG : HasGaussianLaw G P := by
    haveI : IsGaussian (P.map G) := by rw [hlawG']; infer_instance
    exact IsGaussian.hasGaussianLaw hGm.aemeasurable
  have hpair : HasGaussianLaw (fun ω => (G ω, η 0 ω)) P := IndepFun.hasGaussianLaw hGG hHG0 hind'
  set Ψ : (EuclideanSpace ℝ (Fin p) × NegSobolev d r) →L[ℝ] (Fin p → ℝ) := ContinuousLinearMap.pi fun a =>
      (EuclideanSpace.proj a : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ).comp (ContinuousLinearMap.fst ℝ _ _) +
        (ℓ a).comp (ContinuousLinearMap.snd ℝ _ _) with hΨ
  have hvec : (fun ω (a : Fin p) => NegSobolev.fourierCoeff (η (ts a) ω) (ks a)) =
      Ψ ∘ (fun ω => (G ω, η 0 ω)) := by
    funext ω a
    simp only [hΨ, Function.comp_apply, ContinuousLinearMap.pi_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      hGdef, hℓ, HRS.MC.Sec7.S7PIF4.S7PIF4_evalCLM_apply]
    rw [← HRS.MD.EQGaussWindow.eqgw_eval_realMode]
    simp [hφdef]
  refine ⟨?_, ?_⟩
  · rw [hvec]
    exact hpair.map Ψ
  · intro a
    have hpt : ∀ ω, NegSobolev.fourierCoeff (η (ts a) ω) (ks a) = (G ω) a + ℓ a (η 0 ω) := fun ω => by
      have := congrFun (congrFun hvec ω) a
      simpa [hΨ] using this
    simp_rw [hpt]
    have hint1 : Integrable (fun ω => (G ω) a) P := by
      have h1 : Integrable (fun x : EuclideanSpace ℝ (Fin p) => x a) (P.map G) := by
        haveI : IsGaussian (P.map G) := by rw [hlawG']; infer_instance
        exact IsGaussian.integrable_dual (P.map G) (EuclideanSpace.proj a)
      exact (integrable_map_measure h1.aestronglyMeasurable hGm.aemeasurable).1 h1
    have hint2 : Integrable (fun ω => ℓ a (η 0 ω)) P := by
      have h1 : Integrable (fun y => ℓ a y) (P.map (η 0)) := IsGaussian.integrable_dual _ (ℓ a)
      exact (integrable_map_measure h1.aestronglyMeasurable hmeas0.aemeasurable).1 h1
    rw [integral_add hint1 hint2]
    have e1 : ∫ ω, (G ω) a ∂P = 0 := by
      have : ∫ ω, (G ω) a ∂P = ∫ x, x a ∂(P.map G) := by
        rw [integral_map hGm.aemeasurable (by fun_prop)]
      rw [this, hlawG']
      haveI : IsGaussian (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) (Matrix.of fun a b =>
        2 * S.dyn.invβ * ∫ r in Set.Icc 0 (min (ts a) (ts b)), ∫ x,
        inner ℝ (Torus.grad (propagator htr.dyn S.ρ r (ts a) (φ a)) x)
          (Torus.grad (propagator htr.dyn S.ρ r (ts b) (φ b)) x) * S.ρ r x)) := inferInstance
      have := IsGaussian.integral_dual (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) (Matrix.of fun a b =>
        2 * S.dyn.invβ * ∫ r in Set.Icc 0 (min (ts a) (ts b)), ∫ x,
        inner ℝ (Torus.grad (propagator htr.dyn S.ρ r (ts a) (φ a)) x)
          (Torus.grad (propagator htr.dyn S.ρ r (ts b) (φ b)) x) * S.ρ r x)) (EuclideanSpace.proj a)
      rw [integral_id_multivariateGaussian] at this
      simpa using this
    have e2 : ∫ ω, ℓ a (η 0 ω) ∂P = 0 := by
      rw [← integral_map hmeas0.aemeasurable (ℓ a).continuous.aestronglyMeasurable]
      exact hν₀.2 (ℓ a)
    rw [e1, e2, add_zero]

end HRS.MC.E213U13
