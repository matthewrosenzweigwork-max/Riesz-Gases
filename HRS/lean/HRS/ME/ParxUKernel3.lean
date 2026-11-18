import HRS.ME.ParxU
import HRS.Equilibrium.Parametrix.PX5AuxG

/-!
# Packet P1b (part 3): uniform `px5_Bop_bound`

Uniform version (constant chosen before `β, V, ρ`, through the bundle `ParxU`) of
`HRS.Parx.px5_Bop_bound` (PX5AuxG:172). The original constant `β⁻¹ (d + Mr)` used two
ρ-dependent quantities: `β⁻¹` and the compactness sup `Mr` of `∑ⱼ |∂ⱼρ / ρ|`. Here
`β⁻¹ ≤ νp` (`ParxU.beta_bounds`) and `|∂ⱼρ / ρ| ≤ Aⱼ` (`ParxU.partial_div_cbNorm_bound` with `k = 0`),
so the constant is `|νp| (d + ∑ⱼ Aⱼ)`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.ParxU

open HRS.Parx

variable {d : ℕ} {s : ℝ} {N : ℕ} {νm νp c₀ Λ₀ : ℝ}

/-- **Uniform version of `px5_Bop_bound`.** The constant `|νp| (d + ∑ⱼ Aⱼ)` depends only on
`(d, N, νm, νp, c₀, Λ₀)` (with `Aⱼ` from `partial_div_cbNorm_bound`); it is chosen before `β, V, ρ`. -/
theorem px5_Bop_bound_unif (hN : 1 ≤ N) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ {K : ℝ} {ψ : Torus d → Torus d → ℝ}, Px5Bnds s K ψ →
      ∀ x y : Torus d, x ≠ y →
        |Bop d s V β ρ (fun z => ψ z y) x| ≤ Cb * K * wEnv s x y := by
  choose A hA0 hA using fun j : Fin d =>
    ParxU.partial_div_cbNorm_bound (d := d) (s := s) (N := N) (νm := νm) (νp := νp) (c₀ := c₀)
      (Λ₀ := Λ₀) j 0 (by omega)
  have hS0 : 0 ≤ ∑ j, A j := Finset.sum_nonneg fun j _ => hA0 j
  refine ⟨|νp| * (d + ∑ j, A j), mul_nonneg (abs_nonneg _) (add_nonneg (Nat.cast_nonneg d) hS0),
    fun β V ρ U {K ψ} hψ x y hxy => ?_⟩
  have hβ : 0 < β := U.F.hβ
  have hβi : β⁻¹ ≤ νp := (U.beta_bounds).2.1
  have hbi0 : 0 ≤ β⁻¹ := inv_nonneg.mpr hβ.le
  have hρ1 : Torus.IsCk 1 ρ := PDE.MFPair.isCk_of_smooth_ps U.H.rho_smooth.smooth 1
  -- pointwise bound of `∂ⱼρ / ρ` by the uniform constant `Aⱼ`
  have hbd : ∀ j : Fin d, |Torus.partialDeriv j ρ x / ρ x| ≤ A j := by
    intro j
    have hcont : Continuous fun z => Torus.partialDeriv j ρ z / ρ z :=
      (PDE.continuous_partialDeriv j ρ hρ1).div (PDE.MFAux.continuous_of_isCk hρ1)
        (fun z => (lt_of_lt_of_le U.F.hc₀ (U.rho_ge z)).ne')
    have h := HRS.PDE.norm_le_cbNorm_zero (fun z => Torus.partialDeriv j ρ z / ρ z) hcont x
    rw [Real.norm_eq_abs] at h
    exact h.trans (hA j β V ρ U)
  have hp : ((Torus.rep x, Torus.rep y) : Euc d × Euc d) ∈ offDiag d := by
    show Torus.mk (Torus.rep x) ≠ Torus.mk (Torus.rep y)
    rw [Torus.mk_rep, Torus.mk_rep]; exact hxy
  have hH := hψ.hess _ hp
  have hG := hψ.grad _ hp
  simp only [Torus.mk_rep] at hH hG
  have hr0 : 0 < rTrunc x y := lt_min zero_lt_one (px5_eucDist_pos hxy)
  have hr1 : rTrunc x y ≤ 1 := min_le_left _ _
  have hT1 : px5T s 1 (rTrunc x y) ≤ px5T s 2 (rTrunc x y) := by
    show 1 + rTrunc x y ^ (1 - s) ≤ 1 + rTrunc x y ^ (-s)
    have : rTrunc x y ^ (1 - s) ≤ rTrunc x y ^ (-s) :=
      Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (by linarith)
    linarith
  have hT2 : px5T s 2 (rTrunc x y) = wEnv s x y := rfl
  have hTpos : 0 < wEnv s x y := by linarith [px5_wEnv_ge_one s x y]
  have hK0 : 0 ≤ K := by
    have := (norm_nonneg _).trans hH
    rw [hT2] at this
    exact nonneg_of_mul_nonneg_left this hTpos
  have hKw : 0 ≤ K * wEnv s x y := mul_nonneg hK0 hTpos.le
  have hlap := px5_laplacian_slice_bound hψ.smooth2 hxy
  have hpd : ∀ j, |Torus.partialDeriv j (fun z => ψ z y) x| ≤ K * wEnv s x y := fun j =>
    (px5_partialDeriv_slice_bound hψ.smooth2 hxy j).trans (hG.trans
      (mul_le_mul_of_nonneg_left (hT1.trans_eq hT2) hK0))
  rw [px5_Bop_form U.H]
  rw [abs_mul, abs_of_pos (inv_pos.mpr hβ)]
  refine (mul_le_mul_of_nonneg_left (abs_add_le _ _) (inv_pos.mpr hβ).le).trans ?_
  have hs1 : |∑ j, (Torus.partialDeriv j ρ x / ρ x) * Torus.partialDeriv j (fun z => ψ z y) x| ≤
      (∑ j, A j) * (K * wEnv s x y) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |(Torus.partialDeriv j ρ x / ρ x) * Torus.partialDeriv j (fun z => ψ z y) x|
        ≤ ∑ j, A j * (K * wEnv s x y) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hbd j) (hpd j) (abs_nonneg _) (hA0 j)
      _ = (∑ j, A j) * (K * wEnv s x y) := by rw [Finset.sum_mul]
  have hs2 : |Torus.laplacian (fun z => ψ z y) x| ≤ d * (K * wEnv s x y) := by
    refine hlap.trans ?_
    exact mul_le_mul_of_nonneg_left (hH.trans (by rw [hT2])) (Nat.cast_nonneg _)
  have hmain : β⁻¹ * (|Torus.laplacian (fun z => ψ z y) x| +
        |∑ j, (Torus.partialDeriv j ρ x / ρ x) * Torus.partialDeriv j (fun z => ψ z y) x|)
      ≤ β⁻¹ * (d * (K * wEnv s x y) + (∑ j, A j) * (K * wEnv s x y)) :=
    mul_le_mul_of_nonneg_left (add_le_add hs2 hs1) hbi0
  have hd0 : 0 ≤ (d : ℝ) + ∑ j, A j := add_nonneg (Nat.cast_nonneg d) hS0
  have hνp : β⁻¹ ≤ |νp| := hβi.trans (le_abs_self _)
  have hfin : β⁻¹ * (d * (K * wEnv s x y) + (∑ j, A j) * (K * wEnv s x y)) ≤
      |νp| * (d + ∑ j, A j) * K * wEnv s x y := by
    have h2 : β⁻¹ * ((d : ℝ) + ∑ j, A j) ≤ |νp| * ((d : ℝ) + ∑ j, A j) :=
      mul_le_mul_of_nonneg_right hνp hd0
    have h3 := mul_le_mul_of_nonneg_right h2 hKw
    calc β⁻¹ * (d * (K * wEnv s x y) + (∑ j, A j) * (K * wEnv s x y))
        = (β⁻¹ * ((d : ℝ) + ∑ j, A j)) * (K * wEnv s x y) := by ring
      _ ≤ (|νp| * ((d : ℝ) + ∑ j, A j)) * (K * wEnv s x y) := h3
      _ = |νp| * (d + ∑ j, A j) * K * wEnv s x y := by ring
  exact hmain.trans hfin

end HRS.ME.ParxU

end
