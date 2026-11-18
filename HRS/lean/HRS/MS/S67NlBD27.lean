import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovAdjAux7
import HRS.MS.S67NlBD24
import HRS.MS.S67NlBD26

/-!
# S6.7 nonlinear breakdown, packet 27: centered time derivative

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd27_`. TeX S:4766-4770, nonlinear part of
`S:W:lem:r2mov-global-adjoint`. No owned definitions.
Route: differentiate the fixed thermal mean `r ↦ ∫ f_r ρ₀` under the integral sign (dominated by the
linear growth of the time derivative against `ρ₀`), differentiate `√ρ₀ (f_r - mean)` pointwise, and
substitute the generator-difference identity of packet 26 to recognise the projected source
`R = Q K`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

/-- abstract dominated differentiation of the fixed thermal mean -/
lemma s67bd27_dom {ρ₀ : Euc d → ℝ} (hρsm : ContDiff ℝ ∞ ρ₀) (hρpos : ∀ x, 0 < ρ₀ x)
    (hρ0I : Integrable ρ₀ volume)
    (hmaj : Integrable (fun y => (((1 + ‖y‖) * Real.sqrt (ρ₀ y)) * Real.sqrt (ρ₀ y))) volume)
    {T : ℝ} {f G : ℝ → Euc d → ℝ} {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) T)
    (hfc : ∀ u ∈ Ioo (0 : ℝ) T, Continuous (f u))
    (hGc : ∀ u ∈ Ioo (0 : ℝ) T, Continuous (G u))
    {B0 Bt : ℝ} (hB0 : ∀ u ∈ Ioo (0 : ℝ) T, ∀ y, |f u y| ≤ B0)
    (hBt : ∀ u ∈ Ioo (0 : ℝ) T, ∀ y, |G u y| ≤ Bt * (1 + ‖y‖))
    (hder : ∀ y, ∀ u ∈ Ioo (0 : ℝ) T, HasDerivAt (fun r' => f r' y) (-(G u y)) u) :
    Integrable (fun y => -(G r y) * ρ₀ y) volume ∧
    HasDerivAt (fun u => ∫ y, f u y * ρ₀ y) (∫ y, -(G r y) * ρ₀ y) r := by
  have hs : Ioo (0 : ℝ) T ∈ 𝓝 r := isOpen_Ioo.mem_nhds hr
  have hbI : Integrable (fun y => |Bt| *
      (((1 + ‖y‖) * Real.sqrt (ρ₀ y)) * Real.sqrt (ρ₀ y))) volume := hmaj.const_mul |Bt|
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun u y => f u y * ρ₀ y) (F' := fun u y => -(G u y) * ρ₀ y) (x₀ := r)
    (bound := fun y => |Bt| * (((1 + ‖y‖) * Real.sqrt (ρ₀ y)) * Real.sqrt (ρ₀ y)))
    hs
    (Filter.eventually_of_mem hs fun u hu =>
      ((hfc u hu).mul hρsm.continuous).aestronglyMeasurable)
    (hρ0I.bdd_mul (c := B0) (hfc r hr).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact hB0 r hr y))
    ((((hGc r hr).neg).mul hρsm.continuous).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y u hu => by
      have hρy := hρpos y
      have h1 := hBt u hu y
      have h2 : |G u y| ≤ |Bt| * (1 + ‖y‖) :=
        h1.trans (mul_le_mul_of_nonneg_right (le_abs_self Bt) (by positivity))
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos hρy]
      have hsr : Real.sqrt (ρ₀ y) * Real.sqrt (ρ₀ y) = ρ₀ y := Real.mul_self_sqrt hρy.le
      calc |G u y| * ρ₀ y ≤ (|Bt| * (1 + ‖y‖)) * ρ₀ y := mul_le_mul_of_nonneg_right h2 hρy.le
        _ = |Bt| * (((1 + ‖y‖) * Real.sqrt (ρ₀ y)) * Real.sqrt (ρ₀ y)) := by
            rw [mul_assoc (1 + ‖y‖), hsr]; ring)
    hbI
    (Filter.Eventually.of_forall fun y u hu => ((hder y u hu).mul_const (ρ₀ y)))

/-- derivative of the fixed thermal mean under the integral sign -/
lemma s67bd27_mean_deriv (H : Mov2dTh d s β q ρ₀) {ρ : ℝ → Euc d → ℝ} {T : ℝ}
    {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff ρ) T φ f)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) T) :
    Integrable (fun y =>
      -(generatorW ((quadraticGradientDyn d s q β).coeff ρ) r (f r) y) * ρ₀ y) volume ∧
    HasDerivAt (fun u => ∫ y, f u y * ρ₀ y)
      (∫ y, -(generatorW ((quadraticGradientDyn d s q β).coeff ρ) r (f r) y) * ρ₀ y) r := by
  obtain ⟨ψs, hψs⟩ := mov2d_sqrt_schwartz H
  obtain ⟨hρsm, hρpos⟩ := mov2d_rho_data H
  have hsq2 : MemLp (fun x => Real.sqrt (ρ₀ x)) 2 (volume : Measure (Euc d)) := by
    have := (memOsc_schwartz 0 ψs).1
    rwa [hψs] at this
  have hρ0I : Integrable ρ₀ volume := by
    by_contra hni
    have h1 := H.hρ.2.1.integral_one
    rw [integral_undef hni] at h1
    exact zero_ne_one h1
  have hIcc : ∀ u ∈ Ioo (0 : ℝ) T, u ∈ Icc (0 : ℝ) T := fun u hu => Ioo_subset_Icc_self hu
  obtain ⟨B0, hB0⟩ := hf.bdd 0 (by norm_num)
  obtain ⟨Bt, hBt⟩ := hf.bdd_time_deriv
  have hGc : ∀ u ∈ Icc (0 : ℝ) T, Continuous
      (fun y => generatorW ((quadraticGradientDyn d s q β).coeff ρ) u (f u) y) := by
    intro u hu
    have hmap : Continuous (fun y : Euc d => ((⟨u, hu⟩ : Set.Icc (0 : ℝ) T), y)) :=
      continuous_const.prodMk continuous_id
    have hc := hf.cont_time_deriv.comp hmap
    have heq : (fun p : Set.Icc (0 : ℝ) T × Euc d =>
        generatorW ((quadraticGradientDyn d s q β).coeff ρ) p.1 (f p.1) p.2) ∘
        (fun y : Euc d => ((⟨u, hu⟩ : Set.Icc (0 : ℝ) T), y)) =
        fun y => generatorW ((quadraticGradientDyn d s q β).coeff ρ) u (f u) y := rfl
    rwa [heq] at hc
  exact s67bd27_dom (ρ₀ := ρ₀) (T := T) (f := f) (r := r) hρsm hρpos hρ0I
    ((s67_memLp_G H).integrable_mul hsq2) hr
    (G := fun u y => generatorW ((quadraticGradientDyn d s q β).coeff ρ) u (f u) y)
    (fun u hu => (hf.c2 u (hIcc u hu)).continuous) (fun u hu => hGc u (hIcc u hu))
    (B0 := B0) (Bt := Bt)
    (fun u hu y => by
      have := hB0 u (hIcc u hu) y
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this)
    (fun u hu y => hBt u (hIcc u hu) y)
    (fun y u hu => hf.time_deriv y u hu)

theorem s67bd_centered_time_derivative (H : Mov2dTh d s β q ρ₀)
    (m : ℕ) (hm : (d : ℝ) / 2 + 7 < m) (R0 c0 : ℝ)
    (f0 : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ)
    (hρ : MovInSmallClass d s q β ρ₀ m R0 c0 f0 ρ)
    (T : ℝ) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ) (hT : 0 ≤ T)
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff ρ) T φ f) :
    ∀ r ∈ Ioo (0 : ℝ) T, ∀ x : Euc d,
      HasDerivAt (fun u => s67psi ρ₀ (f u) x)
        (-(Real.sqrt (ρ₀ x) *
          (generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ₀)) r (f r) x -
           ∫ y, generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ₀)) r (f r) y * ρ₀ y)) -
          s67bd_R d s ρ₀ (movV ρ₀ ρ r) (s67psi ρ₀ (f r)) x) r := by
  intro r hr x
  obtain ⟨hρsm, hρpos⟩ := mov2d_rho_data H
  obtain ⟨hI1, hI0, hid⟩ := s67bd_generator_difference H m hm R0 c0 f0 ρ hρ T φ f hT hf r
    (Ioo_subset_Icc_self hr)
  obtain ⟨-, hmean⟩ := s67bd27_mean_deriv H hf hr
  set G : Euc d → ℝ := fun y => generatorW ((quadraticGradientDyn d s q β).coeff ρ) r (f r) y
    with hG
  set L : Euc d → ℝ := fun y =>
    generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ₀)) r (f r) y with hL
  have hd1 : HasDerivAt (fun u => f u x - ∫ y, f u y * ρ₀ y)
      (-(G x) - ∫ y, -(G y) * ρ₀ y) r := (hf.time_deriv x r hr).sub hmean
  have hd2 := hd1.const_mul (Real.sqrt (ρ₀ x))
  refine hd2.congr_deriv ?_
  -- the projected source
  have hKpt : ∀ y, s67bd_K d s ρ₀ (movV ρ₀ ρ r) (s67psi ρ₀ (f r)) y =
      Real.sqrt (ρ₀ y) * (G y - L y) := fun y => (hid y).symm
  have hint : (∫ y, Real.sqrt (ρ₀ y) *
      s67bd_K d s ρ₀ (movV ρ₀ ρ r) (s67psi ρ₀ (f r)) y) = (∫ y, G y * ρ₀ y) - ∫ y, L y * ρ₀ y := by
    have : ∀ y, Real.sqrt (ρ₀ y) * s67bd_K d s ρ₀ (movV ρ₀ ρ r) (s67psi ρ₀ (f r)) y =
        G y * ρ₀ y - L y * ρ₀ y := by
      intro y
      rw [hKpt y]
      have hsr : Real.sqrt (ρ₀ y) * Real.sqrt (ρ₀ y) = ρ₀ y := Real.mul_self_sqrt (hρpos y).le
      calc Real.sqrt (ρ₀ y) * (Real.sqrt (ρ₀ y) * (G y - L y))
          = (Real.sqrt (ρ₀ y) * Real.sqrt (ρ₀ y)) * (G y - L y) := by ring
        _ = G y * ρ₀ y - L y * ρ₀ y := by rw [hsr]; ring
    simp_rw [this]
    exact integral_sub hI1 hI0
  have hR : s67bd_R d s ρ₀ (movV ρ₀ ρ r) (s67psi ρ₀ (f r)) x =
      Real.sqrt (ρ₀ x) * (G x - L x) -
        Real.sqrt (ρ₀ x) * ((∫ y, G y * ρ₀ y) - ∫ y, L y * ρ₀ y) := by
    unfold s67bd_R s67bd_Q
    rw [hint, hKpt x]
  have hneg : (∫ y, -(G y) * ρ₀ y) = -∫ y, G y * ρ₀ y := by
    simp_rw [neg_mul]
    exact integral_neg _
  rw [hR, hneg]
  ring

end HRS.MS.BreakdownS67
