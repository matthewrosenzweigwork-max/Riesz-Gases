import HRS.MS.ProClosureS111ScreenedFTC
import HRS.MS.ProClosureS111WindowOrbit
import HRS.MS.R26T6CI14
import Mathlib.Analysis.Calculus.MeanValue

/-!
The physical initial random path and its actual projective cubic tensor.
All constants precede the thermal density, the preparation parameter in
its closed interval, and the time shift. The scalar screened FTC is
produced from the physical data, not assumed. This module identifies every
oscillator coordinate; the extension to all admissible tests is separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R26T6C HRS.MS.S111K2

variable {d : ℕ}
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

theorem orbit_lipschitz_of_gradient {C : WholeCoeff d} {k : ℕ}
    {z A c : ℝ} {phi : Euc d → ℝ} (hz : 0 ≤ z) (hA : 0 ≤ A)
    (hex : ∃ f, IsClassicalAdjointW C z phi f)
    (hgrad : R2OrbitGrad C k z phi A c) :
    LipschitzWith (Real.toNNReal (A * Real.exp (-c * z))) (propagatorW C 0 z phi) := by
  have hcls := HRS.MS.Fcau.propagatorW_isClassical hex
  have hcd := hcls.c2 0 ⟨le_rfl, hz⟩
  have hcb := (hgrad _ hcls 0 ⟨le_rfl, hz⟩).2
  have hAc : 0 ≤ A * Real.exp (-c * z) := mul_nonneg hA (Real.exp_pos _).le
  refine lipschitzWith_of_nnnorm_fderiv_le (hcd.differentiable (by norm_num)) (fun x => ?_)
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hAc]
  have hx := HRS.MS.R2WinErr.s104_cbNormVecE_le
    (mul_nonneg hA (Real.exp_pos _).le) hcb 0 (Nat.zero_le _) x
  simpa only [norm_iteratedFDeriv_zero, sub_zero, gradient,
    LinearIsometryEquiv.norm_map] using hx

theorem normalize_square_summable (b : MultiIndex d → ℝ)
    (hb : Summable (fun alpha => b alpha ^ 2)) :
    let D := Real.sqrt (∑' alpha, b alpha ^ 2) + 1
    0 < D ∧ Summable (fun alpha => (b alpha / D) ^ 2) ∧
      (∑' alpha, (b alpha / D) ^ 2) ≤ 1 := by
  let S := ∑' alpha, b alpha ^ 2
  let D := Real.sqrt S + 1
  have hS : 0 ≤ S := tsum_nonneg fun alpha => sq_nonneg _
  have hD : 0 < D := add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) zero_lt_one
  have hsum : Summable (fun alpha => (b alpha / D) ^ 2) := by
    simpa [div_eq_mul_inv, mul_pow, inv_pow] using hb.mul_right ((D ^ 2)⁻¹)
  have hDsq : S ≤ D ^ 2 := by
    have hsqrt := Real.sq_sqrt hS
    dsimp only [D]
    nlinarith [Real.sqrt_nonneg S]
  refine ⟨hD, hsum, ?_⟩
  calc
    (∑' alpha, (b alpha / D) ^ 2) = S / D ^ 2 := by
      calc
        _ = ∑' alpha, b alpha ^ 2 * (D ^ 2)⁻¹ := by
          apply tsum_congr
          intro alpha
          simp [div_eq_mul_inv, mul_pow, inv_pow]
        _ = S / D ^ 2 := by
          simp [S, div_eq_mul_inv, tsum_mul_right]
    _ ≤ 1 := (div_le_iff₀ (sq_pos_of_pos hD)).2 (by simpa using hDsq)

/-- Actual thermal initial paths and cubic tensors, with the decay rate and
constant selected before the density, preparation, and shift. -/
theorem physical_initial_cubic_lift (hd : 2 ≤ d)
    (s a beta Gamma T : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) (hGamma : 0 ≤ Gamma) (hT : 0 < T) :
    ∃ c0 B : ℝ, 0 < c0 ∧ 0 ≤ B ∧
      ∀ rho : Euc d → ℝ, IsThermalEquilibrium d s a beta rho →
      ∀ gamma ∈ Icc (0 : ℝ) Gamma, ∀ u : ℝ, 0 ≤ u →
      let mu := HRS.Whole.withDensityReal rho
      let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
      ∃ L : Euc d → OscPath d (wholeSpaceIndex d) T,
        MemLp L 3 mu ∧
        (∀ tau : Icc (0 : ℝ) T, ∀ alpha : MultiIndex d,
          (fun x => OscDual.coord (OscPath.at' (L x) tau) alpha) =ᵐ[mu]
            HRS.Whole.responseInverse (rieszKernel d s) mu gamma
              (propagatorW C 0 (u + tau) (oscTestFun (wholeSpaceIndex d) alpha))) ∧
        (∫ x, ‖L x‖ ^ 3 ∂mu) ≤ B * Real.exp (-3 * c0 * u) ∧
        ∃ I : projTensor (OscPath d (wholeSpaceIndex d) T) 3,
          (∀ M : (OscPath d (wholeSpaceIndex d) T) [×3]→L[ℝ] ℝ,
            (I : TensorDual (OscPath d (wholeSpaceIndex d) T) 3) M =
              ∫ x, M ![L x, L x, L x] ∂mu) ∧
          ‖I‖ ≤ B * Real.exp (-3 * c0 * u) := by
  have hsd : s < (d : ℝ) := by
    linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ (d : ℝ))]
  obtain ⟨c0, b, hc0, hb, hW⟩ := physical_window_orbit_input hd s a beta hs0 hsd ha hbeta
  obtain ⟨Bresp, hBresp, hmoment⟩ :=
    physical_screened_lipschitz_third_uniform hd s a beta Gamma hs0 hs ha hbeta hGamma
  obtain ⟨K, hK, hlift⟩ := r26t6c_initial_H1_L3_lift d (wholeSpaceIndex d) T hT
  let D := Real.sqrt (∑' alpha, b alpha ^ 2) + 1
  let bn := fun alpha => b alpha / D
  obtain ⟨hD, hbn, hbn1⟩ := normalize_square_summable b hb
  change 0 < D at hD
  change Summable (fun alpha => bn alpha ^ 2) at hbn
  change (∑' alpha, bn alpha ^ 2) ≤ 1 at hbn1
  let B := K * ((Bresp + 1) * D) ^ 3
  refine ⟨c0, B, hc0, by dsimp [B]; positivity, ?_⟩
  intro rho hrho gamma hgamma u hu
  let mu := HRS.Whole.withDensityReal rho
  let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
  let phi := fun alpha : MultiIndex d => oscTestFun (wholeSpaceIndex d) alpha
  letI : IsProbabilityMeasure mu := HRS.Whole.Q34.isProbabilityMeasure_nu hrho.2.1
  have hw := hW rho hrho
  obtain ⟨f, g, hgm, hsection, hFTC⟩ :=
    physical_screened_terminal_FTC hd s a beta gamma T u hs0 hs ha hbeta hgamma.1 hT hu rho hrho
  let e := Real.exp (-c0 * u)
  let A := (Bresp + 1) * D * e
  have he : 0 < e := Real.exp_pos _
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hbn0 : ∀ alpha, 0 ≤ bn alpha :=
    fun alpha => div_nonneg (hw.nonneg alpha) hD.le
  have hBc : Bresp ≤ (Bresp + 1) ^ 3 := by
    nlinarith [sq_nonneg Bresp, mul_nonneg hBresp (sq_nonneg Bresp)]
  have hAb (alpha : MultiIndex d) : A * bn alpha = (Bresp + 1) * (b alpha * e) := by
    dsimp only [A, bn]
    field_simp [hD.ne']
    <;> ring
  have hcube (alpha : MultiIndex d) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      Bresp * (b alpha * Real.exp (-c0 * (u + t))) ^ 3 ≤ (A * bn alpha) ^ 3 := by
    have het : Real.exp (-c0 * (u + t)) ≤ e := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hc0.le ht.1]
    calc
      _ ≤ Bresp * (b alpha * e) ^ 3 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (mul_nonneg (hw.nonneg alpha) (Real.exp_pos _).le)
            (mul_le_mul_of_nonneg_left het (hw.nonneg alpha)) 3) hBresp
      _ ≤ (Bresp + 1) ^ 3 * (b alpha * e) ^ 3 :=
        mul_le_mul_of_nonneg_right hBc (pow_nonneg (mul_nonneg (hw.nonneg alpha) he.le) _)
      _ = (A * bn alpha) ^ 3 := by rw [hAb, mul_pow]; ring
  have hrespBound (alpha : MultiIndex d) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      (∫ x, |HRS.Whole.responseInverse (rieszKernel d s) mu gamma
        (propagatorW C 0 (u + t) (phi alpha)) x| ^ 3 ∂mu) ≤ (A * bn alpha) ^ 3 ∧
      (∫ x, |HRS.Whole.responseInverse (rieszKernel d s) mu gamma
        (propagatorW C 0 (u + t) (generatorW C (u + t) (phi alpha))) x| ^ 3 ∂mu) ≤
          (A * bn alpha) ^ 3 := by
    have htime := add_nonneg hu ht.1
    have hcls := hw.classical alpha (u + t) htime
    have hgrad := hw.grad alpha (u + t) htime
    have hL : 0 ≤ b alpha * Real.exp (-c0 * (u + t)) :=
      mul_nonneg (hw.nonneg alpha) (Real.exp_pos _).le
    have h0 := (hmoment rho hrho gamma hgamma _ _
      (orbit_lipschitz_of_gradient htime (hw.nonneg alpha) hcls.1 hgrad.1)).2
    have h1 := (hmoment rho hrho gamma hgamma _ _
      (orbit_lipschitz_of_gradient htime (hw.nonneg alpha) hcls.2 hgrad.2)).2
    rw [Real.coe_toNNReal _ hL] at h0 h1
    exact ⟨h0.trans (hcube alpha t ht), h1.trans (hcube alpha t ht)⟩
  have hfBound : ∀ alpha, (∫ x, |f alpha 0 x| ^ 3 ∂mu) ≤ (A * bn alpha) ^ 3 := by
    intro alpha
    have hrep := (hsection alpha 0 ⟨le_rfl, hT.le⟩).2.1
    calc
      _ = ∫ x, |HRS.Whole.responseInverse (rieszKernel d s) mu gamma
          (propagatorW C 0 (u + 0) (phi alpha)) x| ^ 3 ∂mu :=
        integral_congr_ae (hrep.fun_comp fun z => |z| ^ 3)
      _ ≤ _ := (hrespBound alpha 0 ⟨le_rfl, hT.le⟩).1
  have hgBound : ∀ alpha t, t ∈ Icc (0 : ℝ) T →
      (∫ x, |g alpha t x| ^ 3 ∂mu) ≤ (A * bn alpha) ^ 3 := by
    intro alpha t ht
    calc
      _ = ∫ x, |HRS.Whole.responseInverse (rieszKernel d s) mu gamma
          (propagatorW C 0 (u + t) (generatorW C (u + t) (phi alpha))) x| ^ 3 ∂mu :=
        integral_congr_ae ((hsection alpha t ht).2.2.2.fun_comp fun z => |z| ^ 3)
      _ ≤ _ := (hrespBound alpha t ht).2
  obtain ⟨L, hL3, hcoord, hLbound, I, hI, hIbound⟩ :=
    hlift mu f g bn hbn0 hbn hbn1 A hA
      (fun alpha => (hsection alpha 0 ⟨le_rfl, hT.le⟩).1)
      (fun alpha => (hgm alpha).aestronglyMeasurable)
      (fun alpha t ht => (hsection alpha t ht).2.2.1) hfBound hgBound hFTC
  have hecube : e ^ 3 = Real.exp (-3 * c0 * u) := by
    dsimp only [e]
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num <;> ring
  have hAeq : K * A ^ 3 = B * Real.exp (-3 * c0 * u) := by
    dsimp only [A, B]
    rw [mul_pow, hecube]
    ring
  refine ⟨L, hL3, fun tau alpha => ?_, hAeq ▸ hLbound, I, hI, hAeq ▸ hIbound⟩
  filter_upwards [hcoord, (hsection alpha tau tau.property).2.1] with x hx hsec
  exact (hx tau alpha).trans hsec

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.physical_initial_cubic_lift
