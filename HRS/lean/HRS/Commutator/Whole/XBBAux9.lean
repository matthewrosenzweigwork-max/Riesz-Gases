import HRS.Commutator.Whole.XBBAux8

/-!
# Packet XBB, part 9: band symbols for the identification step (T2)

`θ = cutC(2^{-j}·) - cutC(2^{-j₀}·)` and the smooth compactly supported symbols `m θ`, `(2π|ξ|)^{-η} m θ`,
`2πiξ_a (2π|ξ|)^{-α} θ` of the Riesz transform, of `Λ^{-η}R_a` and of `∂_aΛ^{-α}` on that band.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section
namespace HRS.Commutator.Whole.XBB
open HRS.Commutator.Whole HRS.Commutator.Whole.XLI HRS.Commutator.Whole.XNRS
variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- the band symbol `cutC(2^{-j}ξ) - cutC(2^{-j₀}ξ)` -/
def xbbTheta (j j₀ : ℤ) (ξ : 𝔼) : ℂ :=
  cutC (((2 : ℝ) ^ j)⁻¹ • ξ) - cutC (((2 : ℝ) ^ j₀)⁻¹ • ξ)

lemma xbbTheta_contDiff (j j₀ : ℤ) : ContDiff ℝ ∞ (xbbTheta j j₀ : 𝔼 → ℂ) :=
  (symbol_contDiff cutC_contDiff j).sub (symbol_contDiff cutC_contDiff j₀)

lemma xbbTheta_cs (j j₀ : ℤ) : HasCompactSupport (xbbTheta j j₀ : 𝔼 → ℂ) :=
  (symbol_cs cutC_cs j).sub (symbol_cs cutC_cs j₀)

lemma xbbTheta_zero_low {j j₀ : ℤ} (h : j₀ ≤ j) {ξ : 𝔼} (hξ : ‖ξ‖ ≤ (2 : ℝ) ^ j₀) :
    xbbTheta j j₀ ξ = 0 := by
  unfold xbbTheta
  have h1 : cutC (((2 : ℝ) ^ j)⁻¹ • ξ) = 1 := by
    refine cutC_eq_one_of_le ?_
    have hs : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hs.le, inv_mul_le_iff₀ hs, mul_one]
    exact hξ.trans (zpow_le_zpow_right₀ (by norm_num) h)
  have h2 : cutC (((2 : ℝ) ^ j₀)⁻¹ • ξ) = 1 := by
    refine cutC_eq_one_of_le ?_
    have hs : 0 < (2 : ℝ) ^ j₀ := zpow_pos (by norm_num) j₀
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hs.le, inv_mul_le_iff₀ hs, mul_one]
    exact hξ
  rw [h1, h2]; simp

lemma xbbTheta_zero_high {j j₀ : ℤ} (h : j₀ ≤ j) {ξ : 𝔼} (hξ : (2 : ℝ) ^ (j + 1) ≤ ‖ξ‖) :
    xbbTheta j j₀ ξ = 0 := by
  unfold xbbTheta
  have hj : (2 : ℝ) ^ (j + 1) = 2 * (2 : ℝ) ^ j := by rw [zpow_add₀ (by norm_num), zpow_one]; ring
  have hj0 : (2 : ℝ) ^ (j₀ + 1) ≤ (2 : ℝ) ^ (j + 1) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hj0' : (2 : ℝ) ^ (j₀ + 1) = 2 * (2 : ℝ) ^ j₀ := by
    rw [zpow_add₀ (by norm_num), zpow_one]; ring
  have h1 : cutC (((2 : ℝ) ^ j)⁻¹ • ξ) = 0 := by
    refine cutC_eq_zero_of_ge ?_
    have hs : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hs.le, inv_mul_eq_div, le_div_iff₀ hs]
    linarith
  have h2 : cutC (((2 : ℝ) ^ j₀)⁻¹ • ξ) = 0 := by
    refine cutC_eq_zero_of_ge ?_
    have hs : 0 < (2 : ℝ) ^ j₀ := zpow_pos (by norm_num) j₀
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hs.le, inv_mul_eq_div, le_div_iff₀ hs]
    linarith
  rw [h1, h2]; simp

/-- smoothness and compact support of `g · θ` when `θ` vanishes near `0` and `g` is smooth away from `0` -/
lemma xbb_smooth_cs_of_zero_near {θ : 𝔼 → ℂ} (hθ : ContDiff ℝ ∞ θ) (hcs : HasCompactSupport θ)
    {r : ℝ} (hr : 0 < r) (hz : ∀ ξ : 𝔼, ‖ξ‖ < r → θ ξ = 0) {g : 𝔼 → ℂ}
    (hg : ∀ ξ : 𝔼, ξ ≠ 0 → ContDiffAt ℝ ∞ g ξ) :
    ContDiff ℝ ∞ (fun ξ => g ξ * θ ξ) ∧ HasCompactSupport (fun ξ => g ξ * θ ξ) := by
  refine ⟨?_, hcs.mul_left⟩
  refine cmxMY_contDiff_of_away_real (r := r) hr (fun ξ hξ => (hg ξ hξ).mul hθ.contDiffAt) (fun ξ hξ => ?_)
  simp [hz ξ hξ]

/-- the power symbol `(2π|ξ|)^s` -/
def xbbPow (s : ℝ) (ξ : 𝔼) : ℂ := (((2 * Real.pi * ‖ξ‖) ^ s : ℝ) : ℂ)

lemma xbbPow_contDiffAt (s : ℝ) {ξ : 𝔼} (hξ : ξ ≠ 0) : ContDiffAt ℝ ∞ (xbbPow s : 𝔼 → ℂ) ξ := by
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have h1 : ContDiffAt ℝ ∞ (fun η : 𝔼 => (2 * Real.pi * ‖η‖) ^ s) ξ :=
    ContDiffAt.rpow_const_of_ne (contDiffAt_const.mul (contDiffAt_norm ℝ hξ)) (by positivity)
  exact (Complex.ofRealCLM.contDiff.contDiffAt).comp ξ h1

lemma xbbRm_contDiffAt (a : Fin d) {ξ : 𝔼} (hξ : ξ ≠ 0) : ContDiffAt ℝ ∞ (xbbRm a : 𝔼 → ℂ) ξ := by
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have h1 : ContDiffAt ℝ ∞ (fun η : 𝔼 => (η a : ℝ)) ξ :=
    ((EuclideanSpace.proj a : 𝔼 →L[ℝ] ℝ).contDiff).contDiffAt
  have h2 : ContDiffAt ℝ ∞ (fun η : 𝔼 => ‖η‖) ξ := contDiffAt_norm ℝ hξ
  unfold xbbRm
  exact contDiffAt_const.mul ((Complex.ofRealCLM.contDiff.contDiffAt).comp ξ (h1.div h2 hn.ne'))

lemma xbbCoord_contDiff (a : Fin d) : ContDiff ℝ ∞ (fun ξ : 𝔼 => (2 * Real.pi * Complex.I * ((ξ a : ℝ) : ℂ))) :=
  contDiff_const.mul (Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj a : 𝔼 →L[ℝ] ℝ).contDiff))


/-- the symbols of the band operators, all multiplied by `θ = xbbTheta j j₀` -/
def xbbSR (a : Fin d) (j j₀ : ℤ) (ξ : 𝔼) : ℂ := xbbRm a ξ * xbbTheta j j₀ ξ
def xbbSG (a : Fin d) (η : ℝ) (j j₀ : ℤ) (ξ : 𝔼) : ℂ := xbbPow (-η) ξ * (xbbRm a ξ * xbbTheta j j₀ ξ)
def xbbSS (a : Fin d) (α : ℝ) (j j₀ : ℤ) (ξ : 𝔼) : ℂ :=
  (2 * Real.pi * Complex.I * ((ξ a : ℝ) : ℂ)) * (xbbPow (-α) ξ * xbbTheta j j₀ ξ)

section sym
variable {j j₀ : ℤ}

lemma xbbSR_prop (a : Fin d) (h : j₀ ≤ j) :
    ContDiff ℝ ∞ (xbbSR a j j₀ : 𝔼 → ℂ) ∧ HasCompactSupport (xbbSR a j j₀ : 𝔼 → ℂ) := by
  have hr : 0 < (2 : ℝ) ^ j₀ := zpow_pos (by norm_num) j₀
  exact xbb_smooth_cs_of_zero_near (xbbTheta_contDiff j j₀) (xbbTheta_cs j j₀) hr
    (fun ξ hξ => xbbTheta_zero_low h hξ.le) (g := xbbRm a) (fun ξ hξ => xbbRm_contDiffAt a hξ)

lemma xbbSG_prop (a : Fin d) (η : ℝ) (h : j₀ ≤ j) :
    ContDiff ℝ ∞ (xbbSG a η j j₀ : 𝔼 → ℂ) ∧ HasCompactSupport (xbbSG a η j j₀ : 𝔼 → ℂ) := by
  have hr : 0 < (2 : ℝ) ^ j₀ := zpow_pos (by norm_num) j₀
  have := xbb_smooth_cs_of_zero_near (xbbTheta_contDiff j j₀) (xbbTheta_cs j j₀) hr
    (fun ξ hξ => xbbTheta_zero_low h hξ.le)
    (g := fun ξ => xbbPow (-η) ξ * xbbRm a ξ)
    (fun ξ hξ => (xbbPow_contDiffAt (-η) hξ).mul (xbbRm_contDiffAt a hξ))
  have e : (xbbSG a η j j₀ : 𝔼 → ℂ) =
      fun ξ => (xbbPow (-η) ξ * xbbRm a ξ) * xbbTheta j j₀ ξ := by
    funext ξ; unfold xbbSG; ring
  rw [e]; exact this

lemma xbbSS_prop (a : Fin d) (α : ℝ) (h : j₀ ≤ j) :
    ContDiff ℝ ∞ (xbbSS a α j j₀ : 𝔼 → ℂ) ∧ HasCompactSupport (xbbSS a α j j₀ : 𝔼 → ℂ) := by
  have hr : 0 < (2 : ℝ) ^ j₀ := zpow_pos (by norm_num) j₀
  have := xbb_smooth_cs_of_zero_near (xbbTheta_contDiff j j₀) (xbbTheta_cs j j₀) hr
    (fun ξ hξ => xbbTheta_zero_low h hξ.le)
    (g := fun ξ => (2 * Real.pi * Complex.I * ((ξ a : ℝ) : ℂ)) * xbbPow (-α) ξ)
    (fun ξ hξ => (xbbCoord_contDiff a).contDiffAt.mul (xbbPow_contDiffAt (-α) hξ))
  have e : (xbbSS a α j j₀ : 𝔼 → ℂ) =
      fun ξ => ((2 * Real.pi * Complex.I * ((ξ a : ℝ) : ℂ)) * xbbPow (-α) ξ) * xbbTheta j j₀ ξ := by
    funext ξ; unfold xbbSS; ring
  rw [e]; exact this

end sym

lemma xbbSG_eq (a : Fin d) {α β η : ℝ} (hη : α = β + η + 1) (j j₀ : ℤ) (ξ : 𝔼) :
    xbbSG a η j j₀ ξ = xbbPow β ξ * xbbSS a α j j₀ ξ := by
  unfold xbbSG xbbSS xbbPow xbbRm
  by_cases hξ : ξ = 0
  · subst hξ; simp
  · have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    have hw : 0 < 2 * Real.pi * ‖ξ‖ := by positivity
    set w : ℝ := 2 * Real.pi * ‖ξ‖ with hwdef
    have e1 : w ^ (-α) = w ^ (-η) * (w ^ β)⁻¹ * w⁻¹ := by
      rw [← Real.rpow_neg hw.le β, ← Real.rpow_neg_one w, ← Real.rpow_add hw, ← Real.rpow_add hw]
      congr 1; rw [hη]; ring
    have e2 : (2 * Real.pi : ℝ) = w / ‖ξ‖ := by rw [hwdef]; field_simp
    have hwβ : (w ^ β : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hw β).ne'
    have hwne : w ≠ 0 := hw.ne'
    have hnne : ‖ξ‖ ≠ 0 := hn.ne'
    have key : (((w ^ (-η) : ℝ)) : ℂ) * (Complex.I * (((ξ a / ‖ξ‖ : ℝ)) : ℂ)) =
        (((w ^ β : ℝ)) : ℂ) * ((2 * (Real.pi : ℂ) * Complex.I * ((ξ a : ℝ) : ℂ)) * (((w ^ (-α) : ℝ)) : ℂ)) := by
      rw [e1]
      push_cast
      have hπ : (2 * (Real.pi : ℂ)) = (w : ℂ) / (‖ξ‖ : ℂ) := by
        have := congrArg (fun r : ℝ => (r : ℂ)) e2
        simpa using this
      rw [hπ]
      have hwC : (w : ℂ) ≠ 0 := by exact_mod_cast hwne
      have hnC : (‖ξ‖ : ℂ) ≠ 0 := by exact_mod_cast hnne
      have hwβC : ((w ^ β : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hwβ
      field_simp
    linear_combination (xbbTheta j j₀ ξ) * key

end HRS.Commutator.Whole.XBB
