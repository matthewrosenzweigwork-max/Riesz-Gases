import HRS.MC.S7S7zAux1

/-!
# Packet `s7_S7z_product_case`, helper 2: the covariance of `delta_x - mu` in `E_r`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.Sec7.S7z

open HRS HRS.Sec7 HRS.StaticLimitAux

variable {d : ℕ} {r : ℝ}

theorem s7z_inner_avec (hm : (d : ℝ) < 2 * r) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (z : Torus d) :
    ⟪avec r hφ, Ye r μ z⟫ = φ z - pair μ φ := by
  rw [inner_Ye_eq μ hm, evalFun_avec]
  have hc := continuous_of_smooth hφ
  have h1 : ∫ y, (φ y - Torus.mean φ) ∂μ = pair μ φ - Torus.mean φ := by
    rw [integral_sub (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (integrable_const _)]
    simp [pair]
  have h2 : ∫ y, evalFun r (avec r hφ) y ∂μ = ∫ y, (φ y - Torus.mean φ) ∂μ := by
    simp_rw [evalFun_avec]
  rw [h2, h1]; ring

theorem s7z_memLp_Ye (hm : (d : ℝ) < 2 * r) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    MemLp (Ye r μ) 2 μ :=
  MemLp.of_bound (continuous_Ye hm μ).aestronglyMeasurable
    (Real.sqrt (8 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * r))))
    (Filter.Eventually.of_forall fun x => norm_ofMeasureDiff_le hm (Measure.dirac x) μ)

theorem s7z_cov_eq (hm : (d : ℝ) < 2 * r) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (g : Torus d → ℝ) (G : Measure (NegSobolev d r)) (hGc : IsCenteredGaussian G)
    (hcov : ∀ φ ψ : Torus d → ℝ, Torus.IsSmooth φ → Torus.IsSmooth ψ →
      ∫ F, NegSobolev.eval F φ * NegSobolev.eval F ψ ∂G =
        ∫ x, φ x * responseRep g μ 0 ψ x ∂μ) :
    covarianceBilin G = covarianceBilin (μ.map (Ye r μ)) := by
  have hXae : AEMeasurable (Ye r μ) μ := (continuous_Ye hm μ).aemeasurable
  have hmemlaw : MemLp id 2 (μ.map (Ye r μ)) :=
    (memLp_map_measure_iff aestronglyMeasurable_id hXae).mpr (s7z_memLp_Ye hm μ)
  have hlaw0 : (μ.map (Ye r μ))[id] = 0 := by
    show ∫ z, id z ∂(μ.map (Ye r μ)) = 0
    rw [integral_map hXae aestronglyMeasurable_id]
    exact integral_Ye_eq_zero hm μ
  refine covarianceBilin_eq_of_smooth _ G hGc fun φ ψ hφ hψ => ?_
  rw [covarianceBilin_apply hmemlaw, hlaw0, hcov φ ψ hφ hψ]
  simp only [sub_zero]
  rw [integral_map hXae (by fun_prop)]
  have hφc := continuous_of_smooth hφ
  have hψc := continuous_of_smooth hψ
  have hpt : ∀ x, ⟪avec r hφ, Ye r μ x⟫ * ⟪avec r hψ, Ye r μ x⟫ =
      (φ x - pair μ φ) * (ψ x - pair μ ψ) := fun x => by
    rw [s7z_inner_avec hm μ hφ, s7z_inner_avec hm μ hψ]
  simp_rw [hpt]
  have hi : ∀ f : Torus d → ℝ, Continuous f → Integrable f μ := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hrr : ∀ x, responseRep g μ 0 ψ x = ψ x - pair μ ψ := fun x => by
    simp [responseRep, projMean]
  simp_rw [hrr]
  have h0 : ∫ x, (ψ x - pair μ ψ) ∂μ = 0 := by
    rw [integral_sub (hi _ hψc) (integrable_const _)]
    simp [pair]
  have : ∀ x, (φ x - pair μ φ) * (ψ x - pair μ ψ) =
      φ x * (ψ x - pair μ ψ) - pair μ φ * (ψ x - pair μ ψ) := fun x => by ring
  simp_rw [this]
  rw [integral_sub, integral_const_mul, h0, mul_zero, sub_zero]
  · exact (hφc.mul (hψc.sub continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact ((hψc.sub continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul _

end HRS.MC.Sec7.S7z
