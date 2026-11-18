import HRS.Commutator.Whole.Defs
import HRS.Commutator.Whole.ExternalAuxMult4
import HRS.Commutator.Whole.ExternalAuxHLS5
import Mathlib.Analysis.Distribution.FourierMultiplier

/-!
# Packet X-NRS, part 1: Fourier-localised Schwartz class and the multipliers `Λ^γ`

For a smooth cutoff `ρ` with compact support vanishing near `0` (`XGoodCut`) and `γ : ℝ`, the symbol
`(2π|ξ|)^γ ρ(ξ)` is smooth with compact support, hence of temperate growth, and
`xlam γ ρ = fourierMultiplierCLM` is a continuous linear map on Schwartz functions.  A Schwartz
function `h` with `ρ 𝓕h = 𝓕h` (`XInD ρ h`) satisfies `𝓕(Λ^γ h) = (2π|ξ|)^γ 𝓕h`.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

/-- A smooth cutoff with compact support vanishing near `0`. -/
structure XGoodCut (ρ : Euc d → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ ρ
  cpt : HasCompactSupport ρ
  zero_near : ∃ ε : ℝ, 0 < ε ∧ ∀ ξ : Euc d, ‖ξ‖ < ε → ρ ξ = 0

/-- The symbol `(2π|ξ|)^γ ρ(ξ)`. -/
def xsym (γ : ℝ) (ρ : Euc d → ℝ) (ξ : Euc d) : ℝ := (2 * Real.pi * ‖ξ‖) ^ γ * ρ ξ

lemma xsym_contDiff {ρ : Euc d → ℝ} (hρ : XGoodCut ρ) (γ : ℝ) : ContDiff ℝ ∞ (xsym γ ρ) := by
  obtain ⟨ε, hε, hz⟩ := hρ.zero_near
  refine cmxMY_contDiff_of_away_real (r := ε) hε (fun η hη => ?_) (fun η hη => ?_)
  · have hn : 0 < ‖η‖ := norm_pos_iff.2 hη
    have h1 : ContDiffAt ℝ ∞ (fun η : Euc d => (2 * Real.pi * ‖η‖) ^ γ) η :=
      ContDiffAt.rpow_const_of_ne (contDiffAt_const.mul (contDiffAt_norm ℝ hη)) (by positivity)
    exact h1.mul hρ.smooth.contDiffAt
  · simp [xsym, hz η hη]

lemma xsym_hasCompactSupport {ρ : Euc d → ℝ} (hρ : XGoodCut ρ) (γ : ℝ) :
    HasCompactSupport (xsym γ ρ) :=
  hρ.cpt.mul_left

lemma xsym_temperate {ρ : Euc d → ℝ} (hρ : XGoodCut ρ) (γ : ℝ) :
    (xsym γ ρ).HasTemperateGrowth :=
  (xsym_hasCompactSupport hρ γ).hasTemperateGrowth (xsym_contDiff hρ γ)

/-- `Λ^γ` on Schwartz functions (relative to the cutoff `ρ`). -/
def xlam (γ : ℝ) (ρ : Euc d → ℝ) : 𝓢(Euc d, ℂ) →L[ℝ] 𝓢(Euc d, ℂ) :=
  SchwartzMap.fourierMultiplierCLM ℂ (xsym γ ρ)

lemma fourier_xlam {ρ : Euc d → ℝ} (hρ : XGoodCut ρ) (γ : ℝ) (f : 𝓢(Euc d, ℂ)) (ξ : Euc d) :
    𝓕 (xlam γ ρ f) ξ = ((xsym γ ρ ξ : ℝ) : ℂ) * 𝓕 f ξ := by
  unfold xlam
  rw [SchwartzMap.fourierMultiplierCLM_apply]
  set g : 𝓢(Euc d, ℂ) := SchwartzMap.smulLeftCLM ℂ (xsym γ ρ) (𝓕 f) with hg
  have h : 𝓕 (𝓕⁻ g) = g := FourierTransform.fourier_fourierInv_eq g
  rw [h, hg, SchwartzMap.smulLeftCLM_apply_apply (xsym_temperate hρ γ)]
  rfl


/-- `h` is Fourier-localised where `ρ = 1`: `ρ 𝓕h = 𝓕h`. -/
def XInD (ρ : Euc d → ℝ) (h : 𝓢(Euc d, ℂ)) : Prop := ∀ ξ : Euc d, ((ρ ξ : ℝ) : ℂ) * 𝓕 h ξ = 𝓕 h ξ

lemma fourier_xlam_of_inD {ρ : Euc d → ℝ} (hρ : XGoodCut ρ) {h : 𝓢(Euc d, ℂ)} (hh : XInD ρ h)
    (γ : ℝ) (ξ : Euc d) : 𝓕 (xlam γ ρ h) ξ = (((2 * Real.pi * ‖ξ‖) ^ γ : ℝ) : ℂ) * 𝓕 h ξ := by
  rw [fourier_xlam hρ, xsym]
  push_cast
  rw [mul_assoc, hh ξ]

lemma xInD_xlam {ρ : Euc d → ℝ} (hρ : XGoodCut ρ) {h : 𝓢(Euc d, ℂ)} (hh : XInD ρ h) (γ : ℝ) :
    XInD ρ (xlam γ ρ h) := by
  intro ξ
  rw [fourier_xlam_of_inD hρ hh]
  rw [mul_left_comm, hh ξ]

/-- Fourier injectivity on Schwartz functions. -/
lemma xschwartz_ext_fourier {f g : 𝓢(Euc d, ℂ)} (h : ∀ ξ, 𝓕 f ξ = 𝓕 g ξ) : f = g := by
  have h1 : 𝓕 f = 𝓕 g := SchwartzMap.ext h
  calc f = 𝓕⁻ (𝓕 f) := (FourierTransform.fourierInv_fourier_eq f).symm
    _ = 𝓕⁻ (𝓕 g) := by rw [h1]
    _ = g := FourierTransform.fourierInv_fourier_eq g

lemma xInD_fourier_zero_near {ρ : Euc d → ℝ} (hρ : XGoodCut ρ) {h : 𝓢(Euc d, ℂ)} (hh : XInD ρ h) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ξ : Euc d, ‖ξ‖ < ε → 𝓕 h ξ = 0 := by
  obtain ⟨ε, hε, hz⟩ := hρ.zero_near
  refine ⟨ε, hε, fun ξ hξ => ?_⟩
  have := hh ξ
  rw [hz ξ hξ] at this
  simpa using this.symm

lemma xlam_comp {ρ : Euc d → ℝ} (hρ : XGoodCut ρ) {h : 𝓢(Euc d, ℂ)} (hh : XInD ρ h) (γ γ' : ℝ) :
    xlam γ ρ (xlam γ' ρ h) = xlam (γ + γ') ρ h := by
  refine xschwartz_ext_fourier fun ξ => ?_
  rw [fourier_xlam_of_inD hρ (xInD_xlam hρ hh γ'), fourier_xlam_of_inD hρ hh,
    fourier_xlam_of_inD hρ hh]
  by_cases hξ : ξ = 0
  · subst hξ
    obtain ⟨ε, hε, hz⟩ := xInD_fourier_zero_near hρ hh
    rw [hz 0 (by simpa using hε)]
    simp
  · have hn : 0 < 2 * Real.pi * ‖ξ‖ := by
      have := norm_pos_iff.2 hξ
      positivity
    rw [Real.rpow_add hn]
    push_cast
    ring


/-! ### Derivatives -/

/-- The `c`-th unit vector. -/
def xe (c : Fin d) : Euc d := EuclideanSpace.single c 1

/-- `∂_c` on Schwartz functions. -/
def xdr (c : Fin d) (f : 𝓢(Euc d, ℂ)) : 𝓢(Euc d, ℂ) := ∂_{xe c} f

lemma xdr_apply (c : Fin d) (f : 𝓢(Euc d, ℂ)) (x : Euc d) :
    xdr c f x = lineDeriv ℝ f x (xe c) := SchwartzMap.lineDerivOp_apply _ _ _

lemma fourier_xdr (c : Fin d) (f : 𝓢(Euc d, ℂ)) (ξ : Euc d) :
    𝓕 (xdr c f) ξ = (2 * Real.pi * Complex.I * (ξ c : ℝ)) * 𝓕 f ξ := by
  unfold xdr
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  have : (fun x : Euc d => inner ℝ x (xe c)).HasTemperateGrowth :=
    ((innerSL ℝ).flip (xe c)).hasTemperateGrowth
  simp only [SchwartzMap.smul_apply, smul_eq_mul, SchwartzMap.smulLeftCLM_apply_apply this]
  have h2 : inner ℝ ξ (xe c) = ξ c := by
    simp [xe, EuclideanSpace.inner_single_right]
  rw [h2]
  simp [Algebra.smul_def, mul_assoc]

lemma xInD_xdr {ρ : Euc d → ℝ} {h : 𝓢(Euc d, ℂ)} (hh : XInD ρ h) (c : Fin d) :
    XInD ρ (xdr c h) := by
  intro ξ
  rw [fourier_xdr, mul_left_comm, hh ξ]


/-! ### The pairing `∫ (Λ^σ f) g` in Fourier variables and the homogeneous seminorm -/

/-- `∫ (2π|ξ|)^σ 𝓕f(ξ) 𝓕g(-ξ) dξ`. -/
def xpair (σ : ℝ) (f g : 𝓢(Euc d, ℂ)) : ℂ :=
  ∫ ξ, (((2 * Real.pi * ‖ξ‖) ^ σ : ℝ) : ℂ) * 𝓕 f ξ * 𝓕 g (-ξ)

lemma integral_xlam_mul {ρ : Euc d → ℝ} (hρ : XGoodCut ρ) {f : 𝓢(Euc d, ℂ)} (hf : XInD ρ f)
    (σ : ℝ) (g : 𝓢(Euc d, ℂ)) : ∫ x, xlam σ ρ f x * g x = xpair σ f g := by
  set u : 𝓢(Euc d, ℂ) := xlam σ ρ f with hu
  have h1 : ∫ x, 𝓕⁻ (𝓕 u) x * g x = ∫ x, 𝓕 u x * 𝓕⁻ g x :=
    SchwartzMap.integral_fourierInv_mul_eq (𝓕 u) g
  rw [FourierTransform.fourierInv_fourier_eq] at h1
  rw [h1]
  unfold xpair
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [hu, fourier_xlam_of_inD hρ hf]
  have : (𝓕⁻ g : 𝓢(Euc d, ℂ)) ξ = 𝓕 g (-ξ) := by
    rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe, Real.fourierInv_eq_fourier_neg]
  rw [this]

/-- `‖g‖²_{Ḣ^β} = ∫ (2π|ξ|)^{2β} |𝓕g|²`. -/
def xhom (β : ℝ) (g : 𝓢(Euc d, ℂ)) : ℝ := ∫ ξ, (2 * Real.pi * ‖ξ‖) ^ (2 * β) * ‖𝓕 g ξ‖ ^ 2

lemma integrable_xhom {β : ℝ} (hβ : 0 ≤ β) (g : 𝓢(Euc d, ℂ)) :
    Integrable (fun ξ : Euc d => (2 * Real.pi * ‖ξ‖) ^ (2 * β) * ‖𝓕 g ξ‖ ^ 2) := by
  set G : 𝓢(Euc d, ℂ) := 𝓕 g
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ ξ, ‖G ξ‖ ≤ M := by
    refine ⟨∑ k ∈ Finset.range 1, SchwartzMap.seminorm ℝ 0 0 G, fun ξ => ?_⟩
    simpa using SchwartzMap.le_seminorm ℝ 0 0 G ξ
  have h := ((HRS.Commutator.Whole.cmxHLS_integrable_rpow_schwartz (by positivity : 0 ≤ 2 * β) G).const_mul
    ((2 * Real.pi) ^ (2 * β) * M))
  refine h.mono' ?_ (Eventually.of_forall fun ξ => ?_)
  · exact (((Real.continuous_rpow_const (by positivity)).comp
      (by fun_prop : Continuous fun ξ : Euc d => 2 * Real.pi * ‖ξ‖)).mul
      (G.continuous.norm.pow 2)).aestronglyMeasurable
  · have h0 : 0 ≤ (2 * Real.pi * ‖ξ‖) ^ (2 * β) := by positivity
    rw [Real.norm_of_nonneg (mul_nonneg h0 (sq_nonneg _))]
    have h2 : ‖G ξ‖ ^ 2 ≤ M * ‖G ξ‖ := by
      rw [sq]; exact mul_le_mul_of_nonneg_right (hM ξ) (norm_nonneg _)
    calc (2 * Real.pi * ‖ξ‖) ^ (2 * β) * ‖G ξ‖ ^ 2
        ≤ (2 * Real.pi * ‖ξ‖) ^ (2 * β) * (M * ‖G ξ‖) := mul_le_mul_of_nonneg_left h2 h0
      _ = ((2 * Real.pi) ^ (2 * β) * M) * (‖ξ‖ ^ (2 * β) * ‖G ξ‖) := by
          rw [Real.mul_rpow (by positivity) (norm_nonneg _)]; ring


lemma xcs {p q : Euc d → ℝ} (hp0 : ∀ ξ, 0 ≤ p ξ) (hq0 : ∀ ξ, 0 ≤ q ξ)
    (hpm : AEStronglyMeasurable p volume) (hqm : AEStronglyMeasurable q volume)
    (hp : Integrable (fun ξ => p ξ ^ 2)) (hq : Integrable (fun ξ => q ξ ^ 2)) :
    Integrable (fun ξ => p ξ * q ξ) ∧
      ∫ ξ, p ξ * q ξ ≤ Real.sqrt (∫ ξ, p ξ ^ 2) * Real.sqrt (∫ ξ, q ξ ^ 2) := by
  have hp2 : MemLp p (ENNReal.ofReal 2) volume := by
    rw [show ENNReal.ofReal 2 = 2 by simp]
    exact (memLp_two_iff_integrable_sq hpm).2 hp
  have hq2 : MemLp q (ENNReal.ofReal 2) volume := by
    rw [show ENNReal.ofReal 2 = 2 by simp]
    exact (memLp_two_iff_integrable_sq hqm).2 hq
  refine ⟨?_, ?_⟩
  · have := (memLp_two_iff_integrable_sq hpm).2 hp
    have := (memLp_two_iff_integrable_sq hqm).2 hq
    exact MemLp.integrable_mul (p := 2) (q := 2) (by assumption) (by assumption)
  · have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) Real.HolderConjugate.two_two
      (Eventually.of_forall hp0) (Eventually.of_forall hq0) hp2 hq2
    simp only [Real.rpow_two, one_div] at h
    simpa [Real.sqrt_eq_rpow] using h

lemma norm_xpair_le {β : ℝ} (hβ : 0 ≤ β) (f g : 𝓢(Euc d, ℂ)) :
    ‖xpair (2 * β) f g‖ ≤ Real.sqrt (xhom β f) * Real.sqrt (xhom β g) := by
  have hint := integrable_xhom hβ f
  have hint' : Integrable (fun ξ : Euc d => (2 * Real.pi * ‖ξ‖) ^ (2 * β) * ‖𝓕 g (-ξ)‖ ^ 2) := by
    have := (integrable_xhom hβ g).comp_neg (μ := volume)
    simpa using this
  set p : Euc d → ℝ := fun ξ => (2 * Real.pi * ‖ξ‖) ^ β * ‖𝓕 f ξ‖ with hp
  set q : Euc d → ℝ := fun ξ => (2 * Real.pi * ‖ξ‖) ^ β * ‖𝓕 g (-ξ)‖ with hq
  have hsq : ∀ (e : ℝ) (ξ : Euc d), ((2 * Real.pi * ‖ξ‖) ^ e) ^ 2 = (2 * Real.pi * ‖ξ‖) ^ (2 * e) := by
    intro e ξ
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1; push_cast; ring
  have hp2 : ∀ ξ, p ξ ^ 2 = (2 * Real.pi * ‖ξ‖) ^ (2 * β) * ‖𝓕 f ξ‖ ^ 2 := by
    intro ξ; simp only [hp]; rw [mul_pow, hsq]
  have hq2 : ∀ ξ, q ξ ^ 2 = (2 * Real.pi * ‖ξ‖) ^ (2 * β) * ‖𝓕 g (-ξ)‖ ^ 2 := by
    intro ξ; simp only [hq]; rw [mul_pow, hsq]
  have hpm : AEStronglyMeasurable p volume :=
    (((Real.continuous_rpow_const hβ).comp (by fun_prop : Continuous fun ξ : Euc d => 2 * Real.pi * ‖ξ‖)).mul
      (𝓕 f : 𝓢(Euc d, ℂ)).continuous.norm).aestronglyMeasurable
  have hqm : AEStronglyMeasurable q volume :=
    (((Real.continuous_rpow_const hβ).comp (by fun_prop : Continuous fun ξ : Euc d => 2 * Real.pi * ‖ξ‖)).mul
      ((𝓕 g : 𝓢(Euc d, ℂ)).continuous.comp continuous_neg).norm).aestronglyMeasurable
  have hcs := xcs (p := p) (q := q) (fun ξ => by positivity) (fun ξ => by positivity) hpm hqm
    (by simpa only [hp2] using hint) (by simpa only [hq2] using hint')
  have hnorm : ‖xpair (2 * β) f g‖ ≤ ∫ ξ, p ξ * q ξ := by
    unfold xpair
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [hp, hq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    have : (2 * Real.pi * ‖ξ‖) ^ (2 * β) = (2 * Real.pi * ‖ξ‖) ^ β * (2 * Real.pi * ‖ξ‖) ^ β := by
      rw [← hsq β ξ, sq]
    rw [this]; ring
  have hq' : (∫ ξ, q ξ ^ 2) = xhom β g := by
    unfold xhom
    rw [← integral_neg_eq_self (fun ξ : Euc d => (2 * Real.pi * ‖ξ‖) ^ (2 * β) * ‖𝓕 g ξ‖ ^ 2) volume]
    exact integral_congr_ae (Eventually.of_forall fun ξ => by simp only [hq2, norm_neg])
  have hp' : (∫ ξ, p ξ ^ 2) = xhom β f := by
    unfold xhom
    exact integral_congr_ae (Eventually.of_forall hp2)
  rw [hp', hq'] at hcs
  exact hnorm.trans hcs.2

end HRS.Commutator.Whole.XNRS
