import HRS.MH.EdgeSharpA
import HRS.MH.EdgeSharpB
import HRS.MH.EdgeSharpDefs
import HRS.MH.EdgeSharpEF
import HRS.MH.EdgeSharpE2K2
import HRS.MH.EdgeSharpH1
import HRS.MH.EdgeworthSharp

/-!
# EdgeSharp packet H3: final assembly (statement-verbatim copy of `HRS/MH/EdgeSharpSpec.lean`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.EdgeSharp

open HRS HRS.Main

/-- [H3] The frozen theorem `HRS.Main.edgeworth_sharpness_homogeneous`. -/
theorem edgeworth_sharpness_homogeneous_final : type_of% @HRS.Main.edgeworth_sharpness_homogeneous := by
  intro d S m T hE hT hV hρ0 k hk b hb K ε hK ν hν Ω' _ P' _ Z₀ Z hZ Ω _ P _ X₀ W X hflow hfilt hinit
  have hφ := phi0_isSmooth (d := d) k b
  obtain ⟨ℓ, hℓ⟩ := exists_pathEval m T hT.le (phi0 k b) hφ
  obtain ⟨L, hL⟩ := exists_evalCLM (d := d) m (phi0 k b) hφ
  refine ⟨_, sinPhi_mem_cbUnitBall ℓ, ?_⟩
  have hsharp := HRS.MH.EdgeworthSharpP.edgeworth_sharpness_proof (d := d) S S.β m T hE hT K ε hK 0 le_rfl ν hν P' Z₀ Z hZ
    _ (sinPhi_mem_cbUnitBall ℓ) Ω P X₀ W X hflow hfilt hinit
  set κ := ((K 0 : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)
      ((ContinuousMultilinearMap.mkPiAlgebraFin ℝ 3 ℝ).compContinuousLinearMap (fun _ : Fin 3 => ℓ)) with hκ
  have hκne : κ ≠ 0 := by
    have hf := hK.formula 0 le_rfl (fun _ => 0) (fun _ => phi0 k b) (fun _ => ⟨le_rfl, by linarith⟩) (fun _ => hφ) (fun _ => ℓ)
      (fun i w => by rw [hℓ, sub_zero, pathEval_zero hT.le]) ν hν P' Z₀ Z hZ
      (fun _ r => crossDensity d S.s S.β k b r) (fun _ r => crossDensity_isSmooth _ _ _ _ _)
      (fun i r hr ψ hψ => cross_cov_density S m T hV hρ0 k hk b ν hν P' Z₀ Z hZ r hr ψ hψ)
    rw [cubicKappa_zero_times] at hf
    rw [hκ, hf]
    exact cubic_first_term_ne_zero S hV hρ0 k hk b hb
  set c : ℝ := 1 / (1 + ∑ j ∈ Finset.range 6, ‖ℓ‖ ^ j) with hc
  have hcpos : 0 < c := by positivity
  have hK3 : ∀ z, ((K 0 : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)
      (iteratedFDeriv ℝ 3 (fun z => c * Real.sin (ℓ z)) z) = (-c * κ) * Real.cos (ℓ z) := by
    intro z
    rw [iteratedFDeriv_three_sin_comp, map_smul, hκ]
    simp only [smul_eq_mul]; ring
  have hae : ∀ᵐ ω ∂P', ℓ (windowPath m T 0 Z ω) = L (Z₀ ω) := by
    filter_upwards [hZ.sol.init, hZ.sol.cont] with ω h0 hc'
    rw [zero_add] at hc'
    rw [hℓ, windowPath_at_zero hT.le Z ω hc', h0, hL]
  have hint : ∫ ω, ((K 0 : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)
      (iteratedFDeriv ℝ 3 (fun z => c * Real.sin (ℓ z)) (windowPath m T 0 Z ω)) ∂P' =
        (-c * κ) * ∫ ω, Real.cos (L (Z₀ ω)) ∂P' := by
    simp_rw [hK3]
    rw [integral_const_mul]
    congr 1
    exact integral_congr_ae (hae.mono fun ω h => by simp only [h])
  have hpos := integral_cos_clm_pos ν hν.1 L P' Z₀ hZ.meas hZ.law_init
  have hne : (1 / 6 : ℝ) * ∫ ω, ((K 0 : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)
      (iteratedFDeriv ℝ 3 (fun z => c * Real.sin (ℓ z)) (windowPath m T 0 Z ω)) ∂P' ≠ 0 := by
    rw [hint]
    have : -c * κ ≠ 0 := mul_ne_zero (neg_ne_zero.2 hcpos.ne') hκne
    exact mul_ne_zero (by norm_num) (mul_ne_zero this hpos.ne')
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.2 (abs_pos.2 hne)) hsharp

end HRS.MH.EdgeSharp
