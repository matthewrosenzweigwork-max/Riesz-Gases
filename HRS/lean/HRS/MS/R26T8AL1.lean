import HRS.MS.R26T8AL1a
import HRS.MS.R26T8AF00
import HRS.MP.RdGenSob

/-!
# S8.2 observed-time layer, generic lemma L1: weak derivative and Fourier identity for `SobSmooth` functions

For `u` with `r26t8a_SobSmooth u` and a coordinate `i`, the classical partial derivative `∂_i u` lies in `L²`
and `fourierL2 (∂_i u) = 2π i ξ_i · fourierL2 u` a.e.
Route: Q09A `chain_of_memSobolev` gives the weak derivative `G 1` (WD), `r26t8a_l1a_ibp` (integration by parts
with bounded `u`, `∇u` from `rg_sobolev_embedding`) identifies `G 1 = ∂_i u` a.e. via the compact-support
characterization `ae_eq_zero_of_integral_contDiff_smul_eq_zero`, and Q09A `WD.fourier` gives the Fourier identity.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.Whole.Q09A

variable {d : ℕ}

theorem r26t8a_l1{u : Euc d → ℝ} (hu : r26t8a_SobSmooth u) (i : Fin d) :
    MemLp (fun x => fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ))) 2 volume ∧
    fourierL2 (fun x => fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ))) =ᵐ[volume]
      fun ξ => (2 * Real.pi * Complex.I * (ξ i : ℂ)) * fourierL2 u ξ := by
  classical
  set e : Euc d := EuclideanSpace.single i (1 : ℝ) with he
  have hsm : HRS.PDE.ToolboxRd.MemSobolev ((1 : ℕ) : ℝ) u := hu.2 1
  obtain ⟨G, hG, -⟩ := HRS.Whole.Q09A.chain_of_memSobolev hsm i
  have hW : HRS.Whole.Q09A.WD i (fun x => ((u x : ℝ) : ℂ)) (G 1) := by
    have := hG.2 0 (by norm_num)
    rw [hG.1] at this
    exact this
  have hG1 : MemLp (G 1) 2 volume := hW.2.1
  -- bounds on `u` and `∇u`
  have hq : HRS.PDE.ToolboxRd.MemSobolev ((d + 2 : ℕ) : ℝ) u := hu.2 (d + 2)
  have hdq : ((d : ℝ)) / 2 < ((d + 2 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  obtain ⟨C0, hC0, hb0⟩ := HRS.MP.RdGen.rg_sobolev_embedding (d := d) 0 (q := ((d + 2 : ℕ) : ℝ))
    (by simpa using hdq)
  obtain ⟨C1, hC1, hb1⟩ := HRS.MP.RdGen.rg_sobolev_embedding (d := d) 1 (q := ((d + 2 : ℕ) : ℝ))
    (by push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
  set B0 : ℝ := C0 * HRS.Whole.sobolevNorm ((d + 2 : ℕ) : ℝ) u with hB0
  set B1 : ℝ := C1 * HRS.Whole.sobolevNorm ((d + 2 : ℕ) : ℝ) u with hB1
  have hbu : ∀ x, |u x| ≤ B0 := fun x => by
    have := hb0 u hu.1 hq x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    exact this
  have hbd : ∀ x, ‖fderiv ℝ u x‖ ≤ B1 := fun x => by
    have := hb1 u hu.1 hq x
    rw [norm_iteratedFDeriv_one] at this
    exact this
  -- continuity of the classical derivative in direction `e`
  have hcontd : Continuous (fun x => ((fderiv ℝ u x e : ℝ) : ℂ)) := by
    have : Continuous (fun x => fderiv ℝ u x e) :=
      (hu.1.continuous_fderiv (by simp)).clm_apply continuous_const
    exact Complex.continuous_ofReal.comp this
  -- the classical derivative is the weak derivative a.e.
  have hae : G 1 =ᵐ[volume] (fun x => ((fderiv ℝ u x e : ℝ) : ℂ)) := by
    have hloc : LocallyIntegrable (fun x => G 1 x - ((fderiv ℝ u x e : ℝ) : ℂ)) volume :=
      (hG1.locallyIntegrable (by norm_num)).sub hcontd.locallyIntegrable
    have key := ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume) hloc ?_
    · filter_upwards [key] with x hx
      exact sub_eq_zero.1 hx
    · intro g hg hgc
      have hgC : ContDiff ℝ ∞ (fun x => ((g x : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp hg
      have hgCc : HasCompactSupport (fun x => ((g x : ℝ) : ℂ)) :=
        HasCompactSupport.comp_left (g := (Complex.ofReal : ℝ → ℂ)) hgc Complex.ofReal_zero
      obtain ⟨ψ, hψ⟩ : ∃ ψ : SchwartzMap (Euc d) ℂ, ⇑ψ = fun x => ((g x : ℝ) : ℂ) :=
        ⟨hgCc.toSchwartzMap hgC, rfl⟩
      have h1 := hW.2.2 ψ
      have h2 := r26t8a_l1a_ibp u hu.1 B0 B1 hbu hbd ψ e
      have hI1 : Integrable (fun x => G 1 x * ψ x) volume :=
        HRS.Whole.Q09A.integrable_mul_schwartz hG1 ψ
      have hI2 : Integrable (fun x => ((fderiv ℝ u x e : ℝ) : ℂ) * ψ x) volume := by
        have hψi : Integrable (fun x => ψ x) volume := ψ.integrable
        exact hψi.bdd_mul hcontd.aestronglyMeasurable
          (Eventually.of_forall fun x => by
            rw [Complex.norm_real]
            exact (ContinuousLinearMap.le_opNorm (fderiv ℝ u x) e).trans
              (mul_le_mul_of_nonneg_right (hbd x) (norm_nonneg e)))
      have hsplit : ∫ x, g x • (G 1 x - ((fderiv ℝ u x e : ℝ) : ℂ)) =
          (∫ x, G 1 x * ψ x) - ∫ x, ((fderiv ℝ u x e : ℝ) : ℂ) * ψ x := by
        rw [← integral_sub hI1 hI2]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [hψ, Complex.real_smul, mul_sub]
        ring
      rw [hsplit, h1, h2]
      simp only [hψ]
      ring
  -- the Fourier identity
  have hDc : MemLp (fun x => ((fderiv ℝ u x e : ℝ) : ℂ)) 2 volume := hG1.ae_eq hae
  have hDreal : MemLp (fun x => fderiv ℝ u x e) 2 volume := by
    have := hDc.re
    simpa using this
  refine ⟨hDreal, ?_⟩
  have hfu : fourierL2 u = fcL (hsm.1.ofReal (K := ℂ)) := fourierL2_eq hsm.1
  have hfD : fourierL2 (fun x => fderiv ℝ u x e) = fcL (hDreal.ofReal (K := ℂ)) :=
    fourierL2_eq hDreal
  have hL : MemLp.toLp (fun x => ((fderiv ℝ u x e : ℝ) : ℂ)) hDc = MemLp.toLp (G 1) hG1 :=
    MemLp.toLp_congr hDc hG1 hae.symm
  have hLeq : fcL (hDreal.ofReal (K := ℂ)) = fcL hG1 := by
    have h0 : fcL (hDreal.ofReal (K := ℂ)) = fcL hDc := rfl
    rw [h0]
    unfold fcL
    rw [hL]
  have hWD := HRS.Whole.Q09A.WD.fourier hW
  filter_upwards [hWD] with ξ hξ
  rw [hfD, hLeq, hfu, hξ]

end HRS.MS.R26T8A

end
