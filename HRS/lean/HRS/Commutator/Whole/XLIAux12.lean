import HRS.Commutator.Whole.XLIAux11

/-!
# X-LI part 12: operator calculus for the Bessel multiplier on Schwartz functions
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- the Bessel multiplier `(1 + 4π²|ξ|²)^{s/2}` -/
def bsymX (s : ℝ) (ξ : 𝔼) : ℂ := (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)

lemma bsymX_temperate (s : ℝ) : (bsymX s : 𝔼 → ℂ).HasTemperateGrowth := by
  have h1 := Function.hasTemperateGrowth_one_add_norm_sq_rpow 𝔼 (s / 2)
  have h2 : (fun ξ : 𝔼 => (2 * Real.pi) • ξ).HasTemperateGrowth :=
    ((2 * Real.pi) • ContinuousLinearMap.id ℝ 𝔼).hasTemperateGrowth
  have h3 := h1.comp h2
  have h4 := Complex.hasTemperateGrowth_ofReal.comp h3
  convert h4 using 1
  funext ξ
  simp only [bsymX, Function.comp, norm_smul, Real.norm_eq_abs, abs_mul, abs_two,
    abs_of_pos Real.pi_pos]
  congr 2
  ring

lemma bsymX_mul (s t : ℝ) (ξ : 𝔼) : bsymX s ξ * bsymX t ξ = bsymX (s + t) ξ := by
  unfold bsymX
  rw [← Complex.ofReal_mul, ← Real.rpow_add (by positivity)]
  congr 2
  ring

lemma bsymX_zero (ξ : 𝔼) : bsymX 0 ξ = 1 := by
  simp [bsymX]

lemma mulS_congr {τ τ' : 𝔼 → ℂ} (h : τ = τ') (hτ : τ.HasTemperateGrowth)
    (hτ' : τ'.HasTemperateGrowth) (φ : SchwartzMap 𝔼 ℂ) :
    mulS τ hτ φ = mulS τ' hτ' φ := by
  subst h; rfl

lemma mulS_mulS (τ₁ τ₂ : 𝔼 → ℂ) (h₁ : τ₁.HasTemperateGrowth) (h₂ : τ₂.HasTemperateGrowth)
    (h₁₂ : (fun ξ => τ₁ ξ * τ₂ ξ).HasTemperateGrowth) (φ : SchwartzMap 𝔼 ℂ) :
    mulS τ₁ h₁ (mulS τ₂ h₂ φ) = mulS (fun ξ => τ₁ ξ * τ₂ ξ) h₁₂ φ := by
  ext x
  rw [mulS_apply, mulS_apply]
  have : (fun ξ => τ₁ ξ * 𝓕 (⇑(mulS τ₂ h₂ φ)) ξ) = fun ξ => τ₁ ξ * τ₂ ξ * 𝓕 (⇑φ) ξ := by
    funext ξ
    rw [fourier_mulS, mul_assoc]
  rw [this]

lemma mulS_add (τ₁ τ₂ : 𝔼 → ℂ) (h₁ : τ₁.HasTemperateGrowth) (h₂ : τ₂.HasTemperateGrowth)
    (h₁₂ : (fun ξ => τ₁ ξ + τ₂ ξ).HasTemperateGrowth) (φ : SchwartzMap 𝔼 ℂ) :
    mulS (fun ξ => τ₁ ξ + τ₂ ξ) h₁₂ φ = mulS τ₁ h₁ φ + mulS τ₂ h₂ φ := by
  unfold mulS
  have : SchwartzMap.smulLeftCLM ℂ (fun ξ => τ₁ ξ + τ₂ ξ) (𝓕 φ) =
      SchwartzMap.smulLeftCLM ℂ τ₁ (𝓕 φ) + SchwartzMap.smulLeftCLM ℂ τ₂ (𝓕 φ) := by
    have := SchwartzMap.smulLeftCLM_add (F := ℂ) h₁ h₂
    exact congrArg (fun T => T (𝓕 φ)) this
  rw [this]
  exact FourierInvAdd.fourierInv_add _ _

lemma mulS_const_mul (c : ℂ) (τ : 𝔼 → ℂ) (hτ : τ.HasTemperateGrowth)
    (hc : (fun ξ => c * τ ξ).HasTemperateGrowth) (φ : SchwartzMap 𝔼 ℂ) (x : 𝔼) :
    mulS (fun ξ => c * τ ξ) hc φ x = c * mulS τ hτ φ x := by
  rw [mulS_apply, mulS_apply, Real.fourierInv_eq', Real.fourierInv_eq']
  simp only [smul_eq_mul]
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  ring

/-- the dyadic piece of the Bessel multiplier, `(1+4π²|ξ|²)^{s/2} ρ(2^{-j} ξ)` -/
def symR (s : ℝ) (j : ℤ) (ξ : 𝔼) : ℂ := bsymX s ξ * rho (((2 : ℝ) ^ j)⁻¹ • ξ)

lemma symR_temperate (s : ℝ) (j : ℤ) : (symR s j : 𝔼 → ℂ).HasTemperateGrowth :=
  (bsymX_temperate s).mul (temperate_symbol rho_contDiff rho_cs j)

lemma Ths_symbol (s : ℝ) {j : ℤ} (hj : -2 ≤ j) (ξ : 𝔼) :
    Ths s j (((2 : ℝ) ^ j)⁻¹ • ξ) = ((((2 : ℝ) ^ j)⁻¹ ^ s : ℝ) : ℂ) * symR s j ξ := by
  have hs0 : 0 < ((2 : ℝ) ^ j)⁻¹ := inv_pos.2 (zpow_pos (by norm_num) j)
  have hn : ‖((2 : ℝ) ^ j)⁻¹ • ξ‖ = ((2 : ℝ) ^ j)⁻¹ * ‖ξ‖ := by
    rw [norm_smul, Real.norm_of_nonneg hs0.le]
  have hA : (((2 : ℝ) ^ j)⁻¹ ^ 2 + 4 * Real.pi ^ 2 * (((2 : ℝ) ^ j)⁻¹ * ‖ξ‖) ^ 2) ^ (s / 2) =
      (((2 : ℝ) ^ j)⁻¹) ^ s * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (s / 2) := by
    have : (((2 : ℝ) ^ j)⁻¹) ^ 2 + 4 * Real.pi ^ 2 * (((2 : ℝ) ^ j)⁻¹ * ‖ξ‖) ^ 2 =
        (((2 : ℝ) ^ j)⁻¹) ^ 2 * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) := by ring
    rw [this, Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs0.le]
    congr 1
    push_cast
    ring
  unfold Ths thB symR bsymX
  rw [epsj_eq hj, hn, hA]
  push_cast
  ring

/-- the Bessel LP kernels on Schwartz functions are Fourier multipliers -/
lemma cv_dK_Ths_apply (s : ℝ) {j : ℤ} (hj : -2 ≤ j) (φ : SchwartzMap 𝔼 ℂ) (x : 𝔼) :
    cv (dK (Ths s : ℤ → 𝔼 → ℂ) j) ⇑φ x =
      ((((2 : ℝ) ^ j)⁻¹ ^ s : ℝ) : ℂ) * mulS (symR s j) (symR_temperate s j) φ x := by
  have h := cv_symK_eq_mulS ((symFam_Ths (d := d) s).smooth j) ((symFam_Ths (d := d) s).cs j) φ j
  have h2 := congrFun h x
  show cv (symK (Ths s j) j) ⇑φ x = _
  rw [h2]
  have hc : (fun ξ : 𝔼 => ((((2 : ℝ) ^ j)⁻¹ ^ s : ℝ) : ℂ) * symR s j ξ).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const _).mul (symR_temperate s j)
  rw [← mulS_const_mul _ _ (symR_temperate s j) hc]
  refine congrFun (congrArg (⇑) (mulS_congr ?_ _ _ φ)) x
  funext ξ
  exact Ths_symbol s hj ξ

/-- the dyadic piece `Δ_j f` of a Schwartz function in terms of its Bessel derivative -/
lemma delta_eq_bessel (α : ℝ) {j : ℤ} (hj : -2 ≤ j) (f : SchwartzMap 𝔼 ℂ) (x : 𝔼) :
    cv (symK rho j) ⇑f x = (((2 : ℝ) ^ j) ^ (-α) : ℝ) *
      cv (dK (Ths (-α) : ℤ → 𝔼 → ℂ) j)
        ⇑(mulS (bsymX α) (bsymX_temperate α) f) x := by
  rw [cv_dK_Ths_apply (-α) hj]
  rw [mulS_mulS _ _ (symR_temperate (-α) j) (bsymX_temperate α)
    ((symR_temperate (-α) j).mul (bsymX_temperate α))]
  have hsym : (fun ξ : 𝔼 => symR (-α) j ξ * bsymX α ξ) = fun ξ : 𝔼 => rho (((2 : ℝ) ^ j)⁻¹ • ξ) := by
    funext ξ
    unfold symR
    rw [mul_right_comm, bsymX_mul]
    simp [bsymX_zero]
  have e1 : mulS (fun ξ => symR (-α) j ξ * bsymX α ξ)
      ((symR_temperate (-α) j).mul (bsymX_temperate α)) f x =
      mulS (fun ξ => rho (((2 : ℝ) ^ j)⁻¹ • ξ)) (temperate_symbol rho_contDiff rho_cs j) f x :=
    congrFun (congrArg (⇑) (mulS_congr hsym ((symR_temperate (-α) j).mul (bsymX_temperate α))
      (temperate_symbol rho_contDiff rho_cs j) f)) x
  have e2 := congrFun (cv_symK_eq_mulS rho_contDiff rho_cs f j) x
  rw [e1, ← e2]
  have hpos : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hab : ((2 : ℝ) ^ j) ^ (-α) * (((2 : ℝ) ^ j)⁻¹) ^ (-α) = 1 := by
    rw [Real.inv_rpow hpos.le]
    exact mul_inv_cancel₀ (Real.rpow_pos_of_pos hpos _).ne'
  rw [← mul_assoc, ← Complex.ofReal_mul, hab]
  simp

/-- the dyadic piece `Δ_k` of the Bessel derivative of a Schwartz function -/
lemma delta_bessel_eq (α : ℝ) {k : ℤ} (hk : -2 ≤ k) (u : SchwartzMap 𝔼 ℂ) (x : 𝔼) :
    cv (symK rho k) ⇑(mulS (bsymX α) (bsymX_temperate α) u) x = (((2 : ℝ) ^ k) ^ α : ℝ) *
      cv (dK (Ths α : ℤ → 𝔼 → ℂ) k) ⇑u x := by
  rw [cv_dK_Ths_apply α hk]
  have e2 := congrFun (cv_symK_eq_mulS rho_contDiff rho_cs
    (mulS (bsymX α) (bsymX_temperate α) u) k) x
  rw [e2]
  rw [mulS_mulS _ _ (temperate_symbol rho_contDiff rho_cs k) (bsymX_temperate α)
    ((temperate_symbol rho_contDiff rho_cs k).mul (bsymX_temperate α))]
  have hsym : (fun ξ : 𝔼 => rho (((2 : ℝ) ^ k)⁻¹ • ξ) * bsymX α ξ) = symR α k := by
    funext ξ; unfold symR; ring
  have e1 : mulS (fun ξ => rho (((2 : ℝ) ^ k)⁻¹ • ξ) * bsymX α ξ)
      ((temperate_symbol rho_contDiff rho_cs k).mul (bsymX_temperate α)) u x =
      mulS (symR α k) (symR_temperate α k) u x :=
    congrFun (congrArg (⇑) (mulS_congr hsym ((temperate_symbol rho_contDiff rho_cs k).mul
      (bsymX_temperate α)) (symR_temperate α k) u)) x
  rw [e1]
  have hpos : 0 < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  have hab : ((2 : ℝ) ^ k) ^ α * (((2 : ℝ) ^ k)⁻¹) ^ α = 1 := by
    rw [Real.inv_rpow hpos.le]
    exact mul_inv_cancel₀ (Real.rpow_pos_of_pos hpos _).ne'
  rw [← mul_assoc, ← Complex.ofReal_mul, hab]
  simp

end HRS.Commutator.Whole.XLI
