import HRS.MS.SpecAux99

/-!
# S8M: the uniform `L⁴(μ)` bound `∫ ‖∇e‖⁴ dμ ≤ (2ω)² e^{C₁ + C₂ ω}` for the constructed eigenfunctions (S8.7, R3)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  Instantiation of `s8p_gradL4` (SpecAux85) with `W = -log ρ`, the standard
basis, `hh = ‖∇U‖`, `λ = ω β`, the log-Sobolev constant of the thermal measure, `D²W ≥ -κ` (`s8p_W_data`) and the uniform
`L⁴` bound of `∇U` (`s8p_X_L4`): `s8p_L4_unif`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovDec

variable {d : ℕ} {s : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

theorem s8p_sqrt_pow4 {om : ℝ} (hom : 0 < om) (a : ℝ) : (a / Real.sqrt om) ^ 4 = a ^ 4 / om ^ 2 := by
  rw [div_pow]
  congr 1
  have : Real.sqrt om ^ 4 = (Real.sqrt om ^ 2) ^ 2 := by ring
  rw [this, Real.sq_sqrt hom.le]

set_option maxHeartbeats 800000 in
theorem s8p_L4_unif (hd : 1 ≤ d) (hs : s = (d : ℝ) / 2) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    {M : ℝ} (hM : S8pRho d s ρ M) {β : ℝ} (hβ : 0 < β) {Cl : ℝ} (hCl0 : 0 ≤ Cl)
    (hLSI : s8p_LSI (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) Cl) {lam0 : ℝ} (hlam0 : 0 < lam0) :
    ∃ C1 C2 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧ ∀ (φ : 𝓢R) (om : ℝ), lam0 ≤ om → s8p_W2 ρ φ ≤ β →
      (∀ᵐ x ∂(volume : Measure (Euc d)), movS d s β ρ φ x = om * φ x) →
      Integrable (fun x => ‖fderiv ℝ (s8p_E d s β ρ φ) x‖ ^ 2) (HRS.Whole.withDensityReal ρ) →
      ∫ x, ‖fderiv ℝ (s8p_E d s β ρ φ) x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρ) = om →
      Integrable (fun x => ‖fderiv ℝ (s8p_E d s β ρ φ) x‖ ^ 4) (HRS.Whole.withDensityReal ρ) ∧
        ∫ x, ‖fderiv ℝ (s8p_E d s β ρ φ) x‖ ^ 4 ∂(HRS.Whole.withDensityReal ρ) ≤
          (2 * om) ^ 2 * Real.exp (C1 + C2 * om) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hs0 : 0 < s := by rw [hs]; positivity
  have hsd : s < d := by rw [hs]; linarith
  have h32 : 3 * s / 2 < d := by rw [hs]; linarith
  obtain ⟨A, hA0, hA⟩ := s8p_X_L4 hd hs0 hsd h32 hρ hE hM hβ
  obtain ⟨κ, hκ0, hW, hρd, hκ⟩ := s8p_W_data hρ hE
  set H4 : ℝ := A * (1 + 1 / lam0) ^ 2 with hH4
  have hH40 : 0 ≤ H4 := by positivity
  refine ⟨(2 * Cl / 3) * (2 * κ), (2 * Cl / 3) * (2 * β + β * Real.sqrt 2 * (3 * H4 / 2 + 9 / 4)),
    by positivity, by positivity, fun φ om hlam hW2 hS hint hom => ?_⟩
  have hom0 : 0 < om := lt_of_lt_of_le hlam0 hlam
  haveI : IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) := mov2e_isProb hρ
  obtain ⟨hUI, hUle⟩ := hA φ om hW2 hint hom
  have hsmU := s8p_U_smooth hd hs0.le hsd hρ hE φ
  have hsmE := s8p_E_smooth hd hs0.le hsd hρ hE β φ
  set hh : Euc d → ℝ := fun x => ‖fderiv ℝ (s8p_U d s ρ φ) x‖ with hhdef
  have hhm : Measurable hh := (hsmU.continuous_fderiv (by simp)).norm.measurable
  have hh4e : ∀ x, (hh x / Real.sqrt om) ^ 4 = (om ^ 2)⁻¹ * ‖fderiv ℝ (s8p_U d s ρ φ) x‖ ^ 4 := fun x => by
    rw [s8p_sqrt_pow4 hom0]; simp only [hhdef]; rw [div_eq_inv_mul]
  have hh4 : Integrable (fun x => (hh x / Real.sqrt om) ^ 4)
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) := by
    simp_rw [hh4e]
    exact hUI.const_mul _
  have hH4' : ∫ x, (hh x / Real.sqrt om) ^ 4 ∂(volume.withDensity (fun x => ENNReal.ofReal (ρ x))) ≤ H4 := by
    simp_rw [hh4e]
    rw [integral_const_mul]
    have h1 : (om ^ 2)⁻¹ * ∫ x, ‖fderiv ℝ (s8p_U d s ρ φ) x‖ ^ 4 ∂(HRS.Whole.withDensityReal ρ) ≤
        (om ^ 2)⁻¹ * (A * (1 + om) ^ 2) := mul_le_mul_of_nonneg_left hUle (by positivity)
    refine h1.trans ?_
    have h2 : 1 / om ≤ 1 / lam0 := one_div_le_one_div_of_le hlam0 hlam
    have h3 : (om ^ 2)⁻¹ * (1 + om) ^ 2 = (1 + 1 / om) ^ 2 := by field_simp; ring
    have h4 : (1 + 1 / om) ^ 2 ≤ (1 + 1 / lam0) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    calc (om ^ 2)⁻¹ * (A * (1 + om) ^ 2) = A * ((om ^ 2)⁻¹ * (1 + om) ^ 2) := by ring
      _ = A * (1 + 1 / om) ^ 2 := by rw [h3]
      _ ≤ A * (1 + 1 / lam0) ^ 2 := mul_le_mul_of_nonneg_left h4 hA0
  have hNfun : s8p_N (s8p_bb d) (s8p_E d s β ρ φ) = fun x => ‖fderiv ℝ (s8p_E d s β ρ φ) x‖ ^ 2 :=
    funext fun x => s8p_N_eq _ _ x
  have hNint : Integrable (s8p_N (s8p_bb d) (s8p_E d s β ρ φ))
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) := by
    rw [hNfun]; exact hint
  have hNone : ∫ x, s8p_N (s8p_bb d) (s8p_E d s β ρ φ) x
      ∂(volume.withDensity (fun x => ENNReal.ofReal (ρ x))) = om := by
    rw [hNfun]; exact hom
  have hLw := s8p_Lw_eig hd hs0.le hsd hρ hE β φ om hS
  have hLe : ∀ x, ∑ i, s8p_g (s8p_E d s β ρ φ) (s8p_bb d i) x *
      fderiv ℝ (s8p_Lw (s8p_bb d) (fun y => -Real.log (ρ y)) (s8p_E d s β ρ φ)) x (s8p_bb d i) ≤
      (om * β) * s8p_N (s8p_bb d) (s8p_E d s β ρ φ) x +
        (om * β) * Real.sqrt (s8p_N (s8p_bb d) (s8p_E d s β ρ φ) x) * hh x :=
    fun x => s8p_hLe_pt hd hs0.le hsd hρ hE hβ φ hom0.le hLw x
  have key := s8p_gradL4 (s8p_bb d) (ρ := ρ) (W := fun x => -Real.log (ρ x)) (e := s8p_E d s β ρ φ)
    (hh := hh) (C := Cl) (κ := κ) (lam := om * β) (H4 := H4)
    (hρ.data.smooth.of_le (by simp)) hρ.pos hρd (hW.of_le (by simp)) hκ0 hκ (hsmE.of_le (by simp))
    hom0 (by positivity) hLSI hCl0 hNint hNone (fun x => norm_nonneg _) hhm hh4 hH4' hLe
  obtain ⟨hI, hle⟩ := key
  have hN4 : (fun x => s8p_N (s8p_bb d) (s8p_E d s β ρ φ) x ^ 2) =
      fun x => ‖fderiv ℝ (s8p_E d s β ρ φ) x‖ ^ 4 := funext fun x => by
    rw [s8p_N_eq]; ring
  rw [hN4] at hI hle
  refine ⟨hI, hle.trans (le_of_eq ?_)⟩
  congr 2
  ring

end HRS.MS.Spec
