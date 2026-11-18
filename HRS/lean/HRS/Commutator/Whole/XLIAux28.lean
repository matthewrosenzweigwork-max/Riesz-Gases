import HRS.Commutator.Whole.XLIAux27

/-!
# X-LI part 28: pointwise regularity of dyadic kernels (Lipschitz-type difference bounds)
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI
open HRS.Commutator.Whole
variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma fourierInv_cs_diff {θ : 𝔼 → ℂ} (hθ : ContDiff ℝ ∞ θ) (hcs : HasCompactSupport θ) :
    Differentiable ℝ (𝓕⁻ θ) := by
  set S : SchwartzMap 𝔼 ℂ := hcs.toSchwartzMap hθ with hS
  have hSθ : (⇑S : 𝔼 → ℂ) = θ := rfl
  have h1 : (⇑(𝓕⁻ S : SchwartzMap 𝔼 ℂ) : 𝔼 → ℂ) = 𝓕⁻ θ := by
    rw [← hSθ]; exact SchwartzMap.fourierInv_coe S
  rw [← h1]
  exact (𝓕⁻ S : SchwartzMap 𝔼 ℂ).differentiable

lemma fderiv_fourierInv_cs {θ : 𝔼 → ℂ} (hθ : ContDiff ℝ ∞ θ) (hcs : HasCompactSupport θ) (m z : 𝔼) :
    fderiv ℝ (𝓕⁻ θ) z m =
      𝓕⁻ (fun ξ : 𝔼 => (2 * Real.pi * Complex.I * ((inner ℝ ξ m : ℝ) : ℂ)) * θ ξ) z := by
  set S : SchwartzMap 𝔼 ℂ := hcs.toSchwartzMap hθ with hS
  have hSθ : (⇑S : 𝔼 → ℂ) = θ := rfl
  have h1 : (⇑(𝓕⁻ S : SchwartzMap 𝔼 ℂ) : 𝔼 → ℂ) = 𝓕⁻ θ := by
    rw [← hSθ]; exact SchwartzMap.fourierInv_coe S
  have h2 := SchwartzMap.lineDerivOp_fourierInv_eq S m
  have h3 := congrArg (fun T : SchwartzMap 𝔼 ℂ => T z) h2
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv] at h3
  rw [h1] at h3
  rw [h3]
  have hg : (fun x : 𝔼 => (inner ℝ x m : ℝ)).HasTemperateGrowth :=
    ((innerSL ℝ).flip m).hasTemperateGrowth
  set T : SchwartzMap 𝔼 ℂ := (2 * (Real.pi : ℂ) * Complex.I) • (SchwartzMap.smulLeftCLM ℂ
    (fun x : 𝔼 => (inner ℝ x m : ℝ))) S with hT
  have hTf : (⇑T : 𝔼 → ℂ) = fun ξ => 2 * ↑Real.pi * Complex.I * ↑(inner ℝ ξ m) * θ ξ := by
    funext ξ
    rw [hT, smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul, Complex.real_smul, hSθ]
    ring
  rw [← hTf]
  exact congrFun (SchwartzMap.fourierInv_coe T) z


lemma fourierInv_const_mul (c : ℂ) (f : 𝔼 → ℂ) (z : 𝔼) :
    𝓕⁻ (fun ξ => c * f ξ) z = c * 𝓕⁻ f z := by
  simp only [Real.fourierInv_eq, Circle.smul_def]
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul]
  ring

/-- the gradient symbol in direction `m` -/
def gradS (Θ : ℤ → 𝔼 → ℂ) (m : 𝔼) (j : ℤ) (η : 𝔼) : ℂ :=
  (2 * Real.pi * Complex.I * ((inner ℝ η m : ℝ) : ℂ)) * Θ j η

lemma fderiv_dK {Θ : ℤ → 𝔼 → ℂ} (hΘ : ∀ j, ContDiff ℝ ∞ (Θ j))
    (hcs : ∀ j, HasCompactSupport (Θ j)) (j : ℤ) (m z : 𝔼) :
    fderiv ℝ (dK Θ j) z m = ((2 : ℝ) ^ j : ℝ) * dK (gradS Θ m) j z := by
  have h := fderiv_fourierInv_cs (symbol_contDiff (hΘ j) j) (symbol_cs (hcs j) j) m z
  unfold dK at h ⊢
  rw [h]
  have e : (fun ξ : 𝔼 => gradS Θ m j (((2 : ℝ) ^ j)⁻¹ • ξ)) =
      fun ξ => (((2 : ℝ) ^ j)⁻¹ : ℝ) * ((2 * Real.pi * Complex.I * ((inner ℝ ξ m : ℝ) : ℂ)) *
        Θ j (((2 : ℝ) ^ j)⁻¹ • ξ)) := by
    funext ξ
    simp only [gradS, real_inner_smul_left]
    push_cast
    ring
  rw [e, fourierInv_const_mul]
  have hne : ((2 : ℝ) ^ j : ℝ) ≠ 0 := zpow_ne_zero _ (by norm_num)
  push_cast
  field_simp


/-- the real majorant `2^{jd}(1+2^j|y|)^{-(d+1)}` -/
def phiR (j : ℤ) (y : 𝔼) : ℝ := ((2 : ℝ) ^ j) ^ d * ((1 + (2 : ℝ) ^ j * ‖y‖) ^ (d + 1))⁻¹

lemma phiR_nonneg (j : ℤ) (y : 𝔼) : 0 ≤ phiR j y := by
  unfold phiR
  have : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  positivity

lemma Phi_eq_phiR (j : ℤ) (y : 𝔼) : Phi j y = ENNReal.ofReal (phiR j y) := rfl

lemma dK_dec_real {R : ℝ} {Θ : ℤ → 𝔼 → ℂ} (h : SymFam R Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℤ) (y : 𝔼), ‖dK Θ j y‖ ≤ C * phiR j y := by
  obtain ⟨C, hC0, hC⟩ := decay_dec_unif (d := d) R
  obtain ⟨B, hB0, hB⟩ := h.bdd
  refine ⟨C * B, mul_nonneg hC0 hB0, fun j x => ?_⟩
  have hM := hC (Θ j) (h.smooth j) (h.supp j) B hB0 (hB j)
  have hs0 : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hn : ‖((2 : ℝ) ^ j) • x‖ = (2 : ℝ) ^ j * ‖x‖ := by
    rw [norm_smul, Real.norm_of_nonneg hs0.le]
  have h1 := hM (((2 : ℝ) ^ j) • x)
  rw [hn] at h1
  have hpos : 0 < (1 + (2 : ℝ) ^ j * ‖x‖) ^ (d + 1) := by positivity
  have h2 : ‖𝓕⁻ (Θ j) (((2 : ℝ) ^ j) • x)‖ ≤ C * B * ((1 + (2 : ℝ) ^ j * ‖x‖) ^ (d + 1))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]; exact h1
  show ‖symK (Θ j) j x‖ ≤ _
  rw [symK_eq, norm_smul, Real.norm_of_nonneg (by positivity)]
  unfold phiR
  calc ((2 : ℝ) ^ j) ^ d * ‖𝓕⁻ (Θ j) (((2 : ℝ) ^ j) • x)‖
      ≤ ((2 : ℝ) ^ j) ^ d * (C * B * ((1 + (2 : ℝ) ^ j * ‖x‖) ^ (d + 1))⁻¹) := by gcongr
    _ = _ := by ring

lemma phiR_comp_le {j : ℤ} {z u : 𝔼} (h : ‖z‖ ≤ 2 * ‖u‖) :
    phiR j u ≤ 2 ^ (d + 1) * phiR j z := by
  unfold phiR
  have hs0 : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  have h1 : 1 + (2 : ℝ) ^ j * ‖z‖ ≤ 2 * (1 + (2 : ℝ) ^ j * ‖u‖) := by nlinarith [norm_nonneg u]
  have hp1 : 0 < (1 + (2 : ℝ) ^ j * ‖z‖) ^ (d + 1) := by positivity
  have hp2 : 0 < (1 + (2 : ℝ) ^ j * ‖u‖) ^ (d + 1) := by positivity
  have h2 : (1 + (2 : ℝ) ^ j * ‖z‖) ^ (d + 1) ≤ 2 ^ (d + 1) * (1 + (2 : ℝ) ^ j * ‖u‖) ^ (d + 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 _
  have h3 : ((1 + (2 : ℝ) ^ j * ‖u‖) ^ (d + 1))⁻¹ ≤ 2 ^ (d + 1) * ((1 + (2 : ℝ) ^ j * ‖z‖) ^ (d + 1))⁻¹ := by
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hp2 hp1]
    linarith
  calc ((2 : ℝ) ^ j) ^ d * ((1 + (2 : ℝ) ^ j * ‖u‖) ^ (d + 1))⁻¹
      ≤ ((2 : ℝ) ^ j) ^ d * (2 ^ (d + 1) * ((1 + (2 : ℝ) ^ j * ‖z‖) ^ (d + 1))⁻¹) := by gcongr
    _ = _ := by ring


lemma norm_fderiv_dK_le {R' : ℝ} {Θ : ℤ → 𝔼 → ℂ} (hΘ : ∀ j, ContDiff ℝ ∞ (Θ j))
    (hcs : ∀ j, HasCompactSupport (Θ j))
    (hG : ∀ l : Fin d, SymFam R' (gradS Θ (EuclideanSpace.single l (1 : ℝ)))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℤ) (u w : 𝔼),
      ‖fderiv ℝ (dK Θ j) u w‖ ≤ C * (2 : ℝ) ^ j * ‖w‖ * phiR j u := by
  choose C hC0 hC using fun l : Fin d => dK_dec_real (hG l)
  refine ⟨∑ l, C l, Finset.sum_nonneg fun l _ => hC0 l, fun j u w => ?_⟩
  have hs0 : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hw : w = ∑ l : Fin d, w l • (EuclideanSpace.single l (1 : ℝ) : 𝔼) := by
    have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr w
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using this.symm
  have hterm : ∀ l : Fin d, ‖w l • fderiv ℝ (dK Θ j) u (EuclideanSpace.single l (1 : ℝ))‖ ≤
      C l * (2 : ℝ) ^ j * ‖w‖ * phiR j u := by
    intro l
    rw [fderiv_dK hΘ hcs j _ u, norm_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le,
      Real.norm_eq_abs]
    have h1 : |w l| ≤ ‖w‖ := by
      have := PiLp.norm_apply_le w l
      simpa using this
    have h2 := hC l j u
    calc |w l| * ((2 : ℝ) ^ j * ‖dK (gradS Θ (EuclideanSpace.single l (1 : ℝ))) j u‖)
        ≤ ‖w‖ * ((2 : ℝ) ^ j * (C l * phiR j u)) := by gcongr
      _ = _ := by ring
  calc ‖fderiv ℝ (dK Θ j) u w‖
      = ‖∑ l : Fin d, w l • fderiv ℝ (dK Θ j) u (EuclideanSpace.single l (1 : ℝ))‖ := by
        conv_lhs => rw [hw]
        simp only [map_sum, map_smul]
    _ ≤ ∑ l : Fin d, ‖w l • fderiv ℝ (dK Θ j) u (EuclideanSpace.single l (1 : ℝ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ l : Fin d, C l * (2 : ℝ) ^ j * ‖w‖ * phiR j u := Finset.sum_le_sum fun l _ => hterm l
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]


lemma dK_diff_le {R R' : ℝ} {Θ : ℤ → 𝔼 → ℂ} (hΘ : SymFam R Θ)
    (hG : ∀ l : Fin d, SymFam R' (gradS Θ (EuclideanSpace.single l (1 : ℝ)))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℤ) (z w : 𝔼), 2 * ‖w‖ ≤ ‖z‖ →
      ‖dK Θ j (z - w) - dK Θ j z‖ ≤ C * ((2 : ℝ) ^ j * ‖w‖) * phiR j z ∧
      ‖dK Θ j (z - w) - dK Θ j z‖ ≤ C * phiR j z := by
  obtain ⟨C0, hC00, hC0⟩ := dK_dec_real hΘ
  obtain ⟨Cg, hCg0, hCg⟩ := norm_fderiv_dK_le hΘ.smooth hΘ.cs hG
  refine ⟨Cg * 2 ^ (d + 1) + C0 * (2 ^ (d + 1) + 1), by positivity, fun j z w hzw => ?_⟩
  have hs0 : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hdiff : Differentiable ℝ (dK Θ j) :=
    fourierInv_cs_diff (symbol_contDiff (hΘ.smooth j) j) (symbol_cs (hΘ.cs j) j)
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
  -- size part
  have hsize : ‖dK Θ j (z - w) - dK Θ j z‖ ≤ C0 * (2 ^ (d + 1) + 1) * phiR j z := by
    have h1 := hC0 j (z - w)
    have h2 := hC0 j z
    have hz : ‖z‖ ≤ 2 * ‖z - w‖ := by
      have : ‖z‖ ≤ ‖z - w‖ + ‖w‖ := by
        have := norm_add_le (z - w) w
        simpa using this
      linarith
    have h3 := phiR_comp_le (j := j) hz
    calc ‖dK Θ j (z - w) - dK Θ j z‖ ≤ ‖dK Θ j (z - w)‖ + ‖dK Θ j z‖ := norm_sub_le _ _
      _ ≤ C0 * phiR j (z - w) + C0 * phiR j z := add_le_add h1 h2
      _ ≤ C0 * (2 ^ (d + 1) * phiR j z) + C0 * phiR j z := by gcongr
      _ = _ := by ring
  have hphi0 := phiR_nonneg j z
  refine ⟨?_, ?_⟩
  · -- mean value part
    have hmv : ‖dK Θ j (z - (1 : ℝ) • w) - dK Θ j (z - (0 : ℝ) • w)‖ ≤
        (Cg * (2 : ℝ) ^ j * ‖w‖ * (2 ^ (d + 1) * phiR j z)) * (1 - 0) := by
      refine norm_image_sub_le_of_norm_deriv_le_segment' (f := fun t : ℝ => dK Θ j (z - t • w))
        (f' := fun t => -(fderiv ℝ (dK Θ j) (z - t • w) w)) (a := 0) (b := 1) ?_ ?_ 1 (by simp)
      · intro t ht
        have hl : HasDerivAt (fun t : ℝ => z - t • w) (-w) t := by
          simpa using ((hasDerivAt_id t).smul_const w).const_sub z
        have h2 : HasDerivAt (dK Θ j ∘ fun t : ℝ => z - t • w)
            ((fderiv ℝ (dK Θ j) (z - t • w)) (-w)) t :=
          (hdiff (z - t • w)).hasFDerivAt.comp_hasDerivAt t hl
        rw [map_neg] at h2
        exact h2.hasDerivWithinAt
      · intro t ht
        rw [norm_neg]
        refine (hCg j _ w).trans ?_
        have hz : ‖z‖ ≤ 2 * ‖z - t • w‖ := by
          have h1 : ‖z‖ ≤ ‖z - t • w‖ + ‖t • w‖ := by
            have := norm_add_le (z - t • w) (t • w)
            simpa using this
          have h2 : ‖t • w‖ ≤ ‖w‖ := by
            rw [norm_smul, Real.norm_of_nonneg ht.1]
            exact mul_le_of_le_one_left hw0 ht.2.le
          linarith
        have h3 := phiR_comp_le (j := j) hz
        have hCw : 0 ≤ Cg * (2 : ℝ) ^ j * ‖w‖ := by positivity
        calc Cg * (2 : ℝ) ^ j * ‖w‖ * phiR j (z - t • w)
            ≤ Cg * (2 : ℝ) ^ j * ‖w‖ * (2 ^ (d + 1) * phiR j z) := by gcongr
          _ = _ := by ring
    simp only [one_smul, zero_smul, sub_zero, sub_zero, mul_one, sub_zero] at hmv
    refine hmv.trans ?_
    have hC0' : 0 ≤ C0 * (2 ^ (d + 1) + 1) := by positivity
    calc Cg * (2 : ℝ) ^ j * ‖w‖ * (2 ^ (d + 1) * phiR j z)
        = (Cg * 2 ^ (d + 1)) * ((2 : ℝ) ^ j * ‖w‖) * phiR j z := by ring
      _ ≤ (Cg * 2 ^ (d + 1) + C0 * (2 ^ (d + 1) + 1)) * ((2 : ℝ) ^ j * ‖w‖) * phiR j z := by
          gcongr
          linarith
  · refine hsize.trans ?_
    gcongr
    have : 0 ≤ Cg * 2 ^ (d + 1) := by positivity
    linarith

end HRS.Commutator.Whole.XLI
