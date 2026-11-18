import HRS.MC.S7E3aAux1
import HRS.MC.S7E1
import HRS.MC.S7E1b
import HRS.Equilibrium.LocalDivSub

/-!
# Packets `s7_E3a/b`, file 4: a uniform bound on the rows of `H_eps`

`sum_k (H^eps_{ik})^2 <= S^2` for all `eps > 0`, all `i`, with `S` independent of `eps` (the Schur test
for the pair kernel `h_eps`, `|h_eps(x,y)| <= G(x-y)` with the integrable radial majorant
`G(z) = B |z|^{-s}`, followed by Bessel's inequality).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.Sec7.E3Aux4

open HRS HRS.Sec7 HRS.LocalDivAux HRS.MC.Sec7.E3Aux1

variable {d : ℕ} {ρ : Torus d → ℝ}

/-- The radial majorant `G(z) = B |z|^{-s}` is a Schur kernel. -/
theorem e3_majorant (hd : 2 ≤ d) {s : ℝ} (hsd : s < d) (hρ : SmoothPosDensity ρ) {B : ℝ}
    (hB : 0 ≤ B) :
    ∃ Λ : ℝ, PDE.MFLinear.KS (fun z : Torus d => B * Torus.eucDist z 0 ^ (-s)) ρ Λ := by
  have hd1 : 1 ≤ d := by omega
  have hρc : Continuous ρ := StaticLimitAux.continuous_of_smooth hρ.smooth
  obtain ⟨Λ, hΛ⟩ := isCompact_univ.exists_bound_of_continuousOn hρc.continuousOn
  have hmeas : Measurable (fun z : Torus d => B * Torus.eucDist z 0 ^ (-s)) := by
    have h0 : Measurable (fun z : Torus d => Torus.eucDist z 0) := by
      have : (fun z : Torus d => Torus.eucDist z 0) = fun z => Torus.eucDist 0 z := by
        funext z; exact eucDist_symm z 0
      rw [this]
      exact measurable_eucDist_slice (0 : Torus d)
    exact (h0.pow_const _).const_mul _
  refine ⟨Λ, ?_, fun z => ?_, hρ.density, fun x => (le_abs_self _).trans (hΛ x (Set.mem_univ x))⟩
  · refine integrable_torus_of_cube hmeas 0 ?_
    have h1 : IntegrableOn (fun w : Euc d => B * ‖w‖ ^ (-s)) (cube d) :=
      (integrableOn_cube_rpow hd1 hsd).const_mul B
    refine h1.congr_fun (fun w hw => ?_) measurableSet_cube
    simp only
    rw [zero_add, eucDist_mk_zero hw]
  · show B * Torus.eucDist (-z) 0 ^ (-s) = B * Torus.eucDist z 0 ^ (-s)
    congr 2
    have h1 := PairCorrAux.eucDist_sub_zero (0 : Torus d) z
    rw [zero_sub] at h1
    rw [← h1, eucDist_symm]


theorem e3_H_row (hρ : SmoothPosDensity ρ) {e : ℕ → Torus d → ℝ}
    (he : IsONBL2Zero (withDensityReal ρ) e) {h : Torus d → Torus d → ℝ}
    (hL2 : MemLp (Function.uncurry h) 2 ((withDensityReal ρ).prod (withDensityReal ρ))) (i k : ℕ) :
    E0b.e0bH ρ e h i k = ∫ y, (∫ x, h x y * e i x ∂(withDensityReal ρ)) * e k y ∂(withDensityReal ρ) := by
  have := isProb_withDensityReal hρ.density
  rw [E1.e1_H_prod hρ he hL2]
  have hW : MemLp (fun z : Torus d × Torus d => e i z.1 * e k z.2) 2
      ((withDensityReal ρ).prod (withDensityReal ρ)) :=
    E0b.e0b_tensor_memLp (he.memLp i) (he.memLp k)
  have hint : Integrable (fun z : Torus d × Torus d => h z.1 z.2 * (e i z.1 * e k z.2))
      ((withDensityReal ρ).prod (withDensityReal ρ)) := hL2.integrable_mul hW
  rw [integral_prod_symm _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  ring

theorem e3_row_bound (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hρ : SmoothPosDensity ρ)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) {e : ℕ → Torus d → ℝ}
    (he : IsONBL2Zero (withDensityReal ρ) e) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ ε : ℝ, 0 < ε → ∀ i L : ℕ,
      ∑ k ∈ Finset.range L, (E0b.e0bH ρ e (hCut d s φ ε) i k) ^ 2 ≤ S ^ 2 := by
  have hprob := isProb_withDensityReal hρ.density
  obtain ⟨B, hB0, hB⟩ := hT_bound hd hs0 hsd hφ
  obtain ⟨Λ, HG⟩ := e3_majorant hd hsd hρ hB0
  set G : Torus d → ℝ := fun z => B * Torus.eucDist z 0 ^ (-s) with hGdef
  have hGnn : ∀ z, 0 ≤ G z := fun z =>
    mul_nonneg hB0 (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  refine ⟨(PDE.MFLinear.Wc G Λ).toReal, ENNReal.toReal_nonneg, fun ε hε i L => ?_⟩
  have hm := E1b.e1b_meas_cut hsd hφ ε
  have hsymm := E1b.e1b_symm_cut hsd hφ ε
  have hL2 := E1b.e1b_memLp_cut hd hs0 hsd hρ hφ hε
  have hbound : ∀ x y, |hCut d s φ ε x y| ≤ G (x - y) := by
    intro x y
    unfold hCut
    split_ifs with hc
    · have := hB x y
      rw [PairCorrAux.eucDist_sub_zero x y] at this
      exact this
    · simpa using hGnn (x - y)
  set f : Torus d → ℝ := fun y => ∫ x, hCut d s φ ε x y * e i x ∂(withDensityReal ρ) with hf
  have hfm : AEStronglyMeasurable f (withDensityReal ρ) := by
    have hm' : Measurable (fun p : Torus d × Torus d => hCut d s φ ε p.2 p.1) := by
      have := hm.comp (measurable_swap (α := Torus d) (β := Torus d))
      simpa [Function.comp_def, Function.uncurry] using this
    have h1 : AEStronglyMeasurable (fun p : Torus d × Torus d => hCut d s φ ε p.2 p.1 * e i p.2)
        ((withDensityReal ρ).prod (withDensityReal ρ)) :=
      hm'.aestronglyMeasurable.mul ((he.memLp i).aestronglyMeasurable.comp_snd)
    exact h1.integral_prod_right'
  have hei : MemLp (fun x => ‖e i x‖) 2 (withDensityReal ρ) := (he.memLp i).norm
  have hdom : ∀ᵐ y ∂(withDensityReal ρ), ‖f y‖ ≤ ‖PDE.MFLinear.Phi G ρ (fun x => ‖e i x‖) y‖ := by
    filter_upwards [PDE.MFLinear.ae_integrable_slice HG (hei.integrable one_le_two)] with y hy
    have h1 : ‖f y‖ ≤ ∫ x, G (y - x) * ‖e i x‖ ∂(withDensityReal ρ) := by
      refine norm_integral_le_of_norm_le hy (Filter.Eventually.of_forall fun x => ?_)
      rw [norm_mul, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have := hbound x y
      have hev : G (y - x) = G (x - y) := by
        rw [← HG.even (x - y), neg_sub]
      rw [hev]; exact this
    exact h1.trans (le_trans (le_refl _) (by
      rw [Real.norm_eq_abs]; exact le_abs_self _))
  have hfn : eLpNorm f 2 (withDensityReal ρ) ≤ PDE.MFLinear.Wc G Λ := by
    calc eLpNorm f 2 (withDensityReal ρ) ≤ eLpNorm (PDE.MFLinear.Phi G ρ (fun x => ‖e i x‖)) 2 (withDensityReal ρ) :=
          eLpNorm_mono_ae hfm hdom
      _ ≤ PDE.MFLinear.Wc G Λ * eLpNorm (fun x => ‖e i x‖) 2 (withDensityReal ρ) :=
          (PDE.MFLinear.memLp_Phi HG hei).2
      _ = PDE.MFLinear.Wc G Λ := by
          have h1 : eLpNorm (fun x => ‖e i x‖) 2 (withDensityReal ρ) = eLpNorm (e i) 2 (withDensityReal ρ) := eLpNorm_norm _ (he.memLp i).aestronglyMeasurable
          have h2 : (eLpNorm (e i) 2 (withDensityReal ρ)).toReal ^ 2 = 1 := by
            rw [E0b.e0b_sq_eq (he.memLp i)]
            have := he.orthonormal i i
            unfold l2Inner at this
            simpa [sq] using this
          have h3 : (eLpNorm (e i) 2 (withDensityReal ρ)).toReal = 1 := by
            have := ENNReal.toReal_nonneg (a := eLpNorm (e i) 2 (withDensityReal ρ))
            nlinarith
          have h4 : eLpNorm (e i) 2 (withDensityReal ρ) = 1 := by
            rw [← ENNReal.ofReal_toReal (he.memLp i).eLpNorm_ne_top, h3]; simp
          rw [h1, h4, mul_one]
  have hfmem : MemLp f 2 (withDensityReal ρ) := lt_of_le_of_lt hfn (lt_top_iff_ne_top.2 HG.W_ne_top)
  have hsq : ∫ y, f y ^ 2 ∂(withDensityReal ρ) ≤ (PDE.MFLinear.Wc G Λ).toReal ^ 2 := by
    rw [← E0b.e0b_sq_eq hfmem]
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg (ENNReal.toReal_mono HG.W_ne_top hfn) 2
  have hbes := e3_bessel he hfmem L
  refine le_trans (le_of_eq ?_) (hbes.trans hsq)
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [e3_H_row hρ he hL2 i k]

end HRS.MC.Sec7.E3Aux4

end
