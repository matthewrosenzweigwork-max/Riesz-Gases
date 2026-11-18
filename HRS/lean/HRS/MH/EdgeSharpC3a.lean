import HRS.Dynamics.Setup
import Mathlib

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.EdgeSharp

open HRS

variable {d : ℕ}

theorem gaussianPart_one {m q T' : ℝ} (D : DynData d) (ρ : ℝ → Torus d → ℝ)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m)
    (hsol : IsLinearFluctuationSolution P' D ρ m q T' Z₀ Z) {r : ℝ} (hr : r ∈ Set.Icc 0 T')
    {ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) :
    IndepFun (fun ω => NegSobolev.eval (Z r ω) ψ - NegSobolev.eval (Z₀ ω) (propagator D ρ 0 r ψ)) Z₀ P' ∧
      MemLp (fun ω => NegSobolev.eval (Z r ω) ψ - NegSobolev.eval (Z₀ ω) (propagator D ρ 0 r ψ)) 2 P' ∧
      ∫ ω, (NegSobolev.eval (Z r ω) ψ - NegSobolev.eval (Z₀ ω) (propagator D ρ 0 r ψ)) ∂P' = 0 := by
  obtain ⟨hind, hlaw⟩ := hsol.gaussian_part 1 (fun _ => r) (fun _ => ψ)
    (fun _ => hr) (fun _ => hψ)
  set G : Ω' → EuclideanSpace ℝ (Fin 1) := fun ω => WithLp.toLp 2 fun _ : Fin 1 =>
      NegSobolev.eval (Z r ω) ψ - NegSobolev.eval (Z₀ ω) (propagator D ρ 0 r ψ) with hG
  generalize hS : (Matrix.of fun _ _ : Fin 1 => (2 * q * ∫ s in Set.Icc 0 (min r r), ∫ x,
        inner ℝ (Torus.grad (propagator D ρ s r ψ) x)
          (Torus.grad (propagator D ρ s r ψ) x) * ρ s x)) = S at hlaw
  have hX : (fun ω => NegSobolev.eval (Z r ω) ψ - NegSobolev.eval (Z₀ ω) (propagator D ρ 0 r ψ))
      = (fun v : EuclideanSpace ℝ (Fin 1) => v 0) ∘ G := by
    funext ω; simp [hG]
  have hmeasc : Measurable (fun v : EuclideanSpace ℝ (Fin 1) => v 0) := by fun_prop
  have hevm : ∀ f : Torus d → ℝ, Measurable fun F : NegSobolev d m => NegSobolev.eval F f := by
    intro f
    unfold NegSobolev.eval
    refine Measurable.tsum fun k => ?_
    refine Measurable.mul_const ?_ _
    have hc : Continuous fun F : NegSobolev d m => NegSobolev.fourierCoeff F k := by
      have hL : LipschitzWith (⟨Lattice.jp k.1 ^ m, (Real.rpow_pos_of_pos (Torus.jp_pos k.1) m).le⟩ : NNReal)
          (fun F : NegSobolev d m => NegSobolev.fourierCoeff F k) := by
        refine LipschitzWith.of_dist_le_mul fun F G => ?_
        have h1 : NegSobolev.fourierCoeff F k - NegSobolev.fourierCoeff G k =
            Lattice.jp k.1 ^ m * (NegSobolev.coord (F - G) k) := by
          unfold NegSobolev.fourierCoeff NegSobolev.coord
          rw [← mul_sub]; rfl
        rw [Real.dist_eq, dist_eq_norm, h1, abs_mul,
          abs_of_pos (Real.rpow_pos_of_pos (Torus.jp_pos k.1) m)]
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_pos_of_pos (Torus.jp_pos k.1) m).le
        exact lp.norm_apply_le_norm (by norm_num) (((F - G : NegSobolev d m)) : lp (fun _ : NonzeroLattice d => ℝ) 2) k
      exact hL.continuous
    exact hc.measurable
  have hZ0 : AEMeasurable Z₀ P' := by
    have : Z 0 =ᵐ[P'] Z₀ := hsol.init
    exact (hsol.meas 0).aemeasurable.congr this
  have hXae : AEMeasurable (fun ω => NegSobolev.eval (Z r ω) ψ - NegSobolev.eval (Z₀ ω) (propagator D ρ 0 r ψ)) P' :=
    ((hevm ψ).comp (hsol.meas r)).aemeasurable.sub ((hevm _).comp_aemeasurable hZ0)
  have hGae : AEMeasurable G P' :=
    (PiLp.continuous_toLp 2 (fun _ : Fin 1 => ℝ)).measurable.comp_aemeasurable
      (AEMeasurable.of_eval fun _ => hXae)
  have : IsGaussian (Measure.map G P') := by
    show IsGaussian (law P' G)
    rw [hlaw]; infer_instance
  let L : StrongDual ℝ (EuclideanSpace ℝ (Fin 1)) := EuclideanSpace.proj 0
  have hL : ∀ v, L v = v 0 := fun v => rfl
  have hXL : (fun ω => NegSobolev.eval (Z r ω) ψ - NegSobolev.eval (Z₀ ω) (propagator D ρ 0 r ψ))
      = fun ω => L (G ω) := by
    funext ω; simp [hL, hG]
  refine ⟨?_, ?_, ?_⟩
  · rw [hX]
    exact hind.comp hmeasc measurable_id
  · rw [hXL]
    have h1 : MemLp L 2 (Measure.map G P') := IsGaussian.memLp_dual _ L 2 (by simp)
    exact (memLp_map_measure_iff L.continuous.aestronglyMeasurable hGae).1 h1
  · rw [hXL]
    have h2 : ∫ ω, L (G ω) ∂P' = ∫ v, L v ∂(Measure.map G P') :=
      (integral_map hGae L.continuous.aestronglyMeasurable).symm
    have h4 : ∫ v, L v ∂(Measure.map G P') = L (∫ v, id v ∂(Measure.map G P')) :=
      ContinuousLinearMap.integral_comp_comm L IsGaussian.integrable_id
    rw [h2, h4]
    have h3 : ∫ v, v ∂(Measure.map G P') = 0 := by
      have : Measure.map G P' = multivariateGaussian 0 S := hlaw
      rw [this]; exact integral_id_multivariateGaussian
    simpa using congrArg L h3

end HRS.MH.EdgeSharp
