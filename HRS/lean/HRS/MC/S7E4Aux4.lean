import HRS.MC.S7E3aAux4
import HRS.MC.S7E3aAux2
import HRS.MC.S7E4Aux3

/-!
# Packet `s7_E4_normalized_clt`, file 4: a uniform bound on the quadratic forms of `H_eps`

`|sum_{i,j<L} x_i x_j H^eps_ij| <= Lam sum_{i<L} x_i^2` for all `eps > 0`, `L`, `x`, with `Lam` independent of
`eps` and `L` (Schur test for the pair kernel `|h_eps(x,y)| <= G(x-y)` and Cauchy-Schwarz).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.Sec7.E4A4

open HRS HRS.Sec7 HRS.LocalDivAux HRS.MC.Sec7.E3Aux1 HRS.MC.Sec7.E3Aux4

variable {d : ℕ} {ρ : Torus d → ℝ}

/-- the quadratic form bound for a general `L^2` function, uniformly in `eps` -/
theorem form_bound (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hρ : SmoothPosDensity ρ)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ ε : ℝ, 0 < ε → ∀ F : Torus d → ℝ, MemLp F 2 (withDensityReal ρ) →
      |∫ z : Torus d × Torus d, hCut d s φ ε z.1 z.2 * (F z.1 * F z.2)
          ∂((withDensityReal ρ).prod (withDensityReal ρ))| ≤
        Λ * ∫ x, F x ^ 2 ∂(withDensityReal ρ) := by
  have hprob := isProb_withDensityReal hρ.density
  obtain ⟨B, hB0, hB⟩ := hT_bound hd hs0 hsd hφ
  obtain ⟨Λ, HG⟩ := e3_majorant hd hsd hρ hB0
  set G : Torus d → ℝ := fun z => B * Torus.eucDist z 0 ^ (-s) with hGdef
  have hGnn : ∀ z, 0 ≤ G z := fun z =>
    mul_nonneg hB0 (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  refine ⟨(PDE.MFLinear.Wc G Λ).toReal, ENNReal.toReal_nonneg, fun ε hε F hF => ?_⟩
  have hm := E1b.e1b_meas_cut hsd hφ ε
  have hbound : ∀ x y, |hCut d s φ ε x y| ≤ G (x - y) := by
    intro x y
    unfold hCut
    split_ifs with hc
    · have := hB x y
      rw [PairCorrAux.eucDist_sub_zero x y] at this
      exact this
    · simpa using hGnn (x - y)
  have hL2 := E1b.e1b_memLp_cut hd hs0 hsd hρ hφ hε
  have hW : MemLp (fun z : Torus d × Torus d => F z.1 * F z.2) 2
      ((withDensityReal ρ).prod (withDensityReal ρ)) := E0b.e0b_tensor_memLp hF hF
  have hint : Integrable (fun z : Torus d × Torus d => hCut d s φ ε z.1 z.2 * (F z.1 * F z.2))
      ((withDensityReal ρ).prod (withDensityReal ρ)) := hL2.integrable_mul hW
  set T : Torus d → ℝ := fun y => ∫ x, hCut d s φ ε x y * F x ∂(withDensityReal ρ) with hTdef
  have hFabs : MemLp (fun x => ‖F x‖) 2 (withDensityReal ρ) := hF.norm
  have hTm : AEStronglyMeasurable T (withDensityReal ρ) := by
    have hm' : Measurable (fun p : Torus d × Torus d => hCut d s φ ε p.2 p.1) := by
      have := hm.comp (measurable_swap (α := Torus d) (β := Torus d))
      simpa [Function.comp_def, Function.uncurry] using this
    have h1 : AEStronglyMeasurable (fun p : Torus d × Torus d => hCut d s φ ε p.2 p.1 * F p.2)
        ((withDensityReal ρ).prod (withDensityReal ρ)) :=
      hm'.aestronglyMeasurable.mul (hF.aestronglyMeasurable.comp_snd)
    exact h1.integral_prod_right'
  have hdom : ∀ᵐ y ∂(withDensityReal ρ), ‖T y‖ ≤ ‖PDE.MFLinear.Phi G ρ (fun x => ‖F x‖) y‖ := by
    filter_upwards [PDE.MFLinear.ae_integrable_slice HG (hFabs.integrable one_le_two)] with y hy
    have h1 : ‖T y‖ ≤ ∫ x, G (y - x) * ‖F x‖ ∂(withDensityReal ρ) := by
      refine norm_integral_le_of_norm_le hy (Filter.Eventually.of_forall fun x => ?_)
      rw [norm_mul, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have := hbound x y
      have hev : G (y - x) = G (x - y) := by
        rw [← HG.even (x - y), neg_sub]
      rw [hev]; exact this
    exact h1.trans (le_trans (le_refl _) (by
      rw [Real.norm_eq_abs]; exact le_abs_self _))
  have hTfn : eLpNorm T 2 (withDensityReal ρ) ≤
      PDE.MFLinear.Wc G Λ * eLpNorm F 2 (withDensityReal ρ) := by
    calc eLpNorm T 2 (withDensityReal ρ) ≤
          eLpNorm (PDE.MFLinear.Phi G ρ (fun x => ‖F x‖)) 2 (withDensityReal ρ) :=
          eLpNorm_mono_ae hTm hdom
      _ ≤ PDE.MFLinear.Wc G Λ * eLpNorm (fun x => ‖F x‖) 2 (withDensityReal ρ) :=
          (PDE.MFLinear.memLp_Phi HG hFabs).2
      _ = PDE.MFLinear.Wc G Λ * eLpNorm F 2 (withDensityReal ρ) := by
          rw [eLpNorm_norm _ hF.aestronglyMeasurable]
  have hTmem : MemLp T 2 (withDensityReal ρ) :=
    lt_of_le_of_lt hTfn (ENNReal.mul_lt_top HG.W_ne_top.lt_top hF)
  -- Fubini
  have hfub : ∫ z : Torus d × Torus d, hCut d s φ ε z.1 z.2 * (F z.1 * F z.2)
      ∂((withDensityReal ρ).prod (withDensityReal ρ)) = ∫ y, F y * T y ∂(withDensityReal ρ) := by
    rw [integral_prod_symm _ hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hTdef]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  rw [hfub]
  -- Cauchy-Schwarz
  have hcs := abs_real_inner_le_norm (hF.toLp F) (hTmem.toLp T)
  rw [E1Aux4.e1d_inner_toLp hF hTmem, Lp.norm_toLp, Lp.norm_toLp] at hcs
  have hTr : (eLpNorm T 2 (withDensityReal ρ)).toReal ≤
      (PDE.MFLinear.Wc G Λ).toReal * (eLpNorm F 2 (withDensityReal ρ)).toReal := by
    rw [← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top HG.W_ne_top hF.eLpNorm_ne_top) hTfn
  have hsq := E0b.e0b_sq_eq hF
  calc |∫ y, F y * T y ∂(withDensityReal ρ)| ≤
        (eLpNorm F 2 (withDensityReal ρ)).toReal * (eLpNorm T 2 (withDensityReal ρ)).toReal := hcs
    _ ≤ (eLpNorm F 2 (withDensityReal ρ)).toReal *
        ((PDE.MFLinear.Wc G Λ).toReal * (eLpNorm F 2 (withDensityReal ρ)).toReal) :=
        mul_le_mul_of_nonneg_left hTr ENNReal.toReal_nonneg
    _ = (PDE.MFLinear.Wc G Λ).toReal * (eLpNorm F 2 (withDensityReal ρ)).toReal ^ 2 := by ring
    _ = _ := by rw [hsq]

/-- the quadratic form bound for the coefficient matrices -/
theorem quad_bound (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hρ : SmoothPosDensity ρ)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) {e : ℕ → Torus d → ℝ}
    (he : IsONBL2Zero (withDensityReal ρ) e) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ ε : ℝ, 0 < ε → ∀ (L : ℕ) (x : ℕ → ℝ),
      |∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
          x i * x j * E0b.e0bH ρ e (hCut d s φ ε) i j| ≤ Λ * ∑ i ∈ Finset.range L, x i ^ 2 := by
  have hprob := isProb_withDensityReal hρ.density
  obtain ⟨Λ, hΛ, hall⟩ := form_bound hd hs0 hsd hρ hφ
  refine ⟨Λ, hΛ, fun ε hε L x => ?_⟩
  set F : Torus d → ℝ := fun y => ∑ i ∈ Finset.range L, x i * e i y with hFdef
  have hFmem : MemLp F 2 (withDensityReal ρ) :=
    memLp_finsetSum _ fun i _ => (he.memLp i).const_mul _
  have hL2 := E1b.e1b_memLp_cut hd hs0 hsd hρ hφ hε
  have hterm : ∀ i j, Integrable (fun z : Torus d × Torus d =>
      hCut d s φ ε z.1 z.2 * (e i z.1 * e j z.2)) ((withDensityReal ρ).prod (withDensityReal ρ)) :=
    fun i j => hL2.integrable_mul (E0b.e0b_tensor_memLp (he.memLp i) (he.memLp j))
  have hexp : ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
      x i * x j * E0b.e0bH ρ e (hCut d s φ ε) i j =
      ∫ z : Torus d × Torus d, hCut d s φ ε z.1 z.2 * (F z.1 * F z.2)
        ∂((withDensityReal ρ).prod (withDensityReal ρ)) := by
    have h1 : ∀ z : Torus d × Torus d, hCut d s φ ε z.1 z.2 * (F z.1 * F z.2) =
        ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
          (x i * x j) * (hCut d s φ ε z.1 z.2 * (e i z.1 * e j z.2)) := by
      intro z
      simp only [hFdef]
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp_rw [h1]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => (hterm i j).const_mul _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => (hterm i j).const_mul _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, E1.e1_H_prod hρ he hL2 i j]
  rw [hexp]
  refine (hall ε hε F hFmem).trans (le_of_eq ?_)
  rw [HRS.MC.Sec7.E3Aux2.e3_wnorm_sq he L x]

end HRS.MC.Sec7.E4A4

end
