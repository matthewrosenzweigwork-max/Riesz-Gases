import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovAdjNlAux2
import HRS.MS.S67NlBD06
import HRS.MS.S67NlBD24
import HRS.MS.S67NlBD26
import HRS.MS.S67NlBD27
import HRS.MS.S67NlBD30

/-!
# S6.7nl.31: the core pairing derivative with the minus source sign
Source pin `b66ab61cf3f03a9c6f5a899ef5de61f2b34c5e44`.
Route: for `u ∈ [τ, T-r)` the centered element `Ψ(r+u)` equals `f_{r+u} √ρ₀ - m √ρ₀` a.e., and the orbit
`T(u) z ∈ L²_0` is orthogonal to `√ρ₀`, so `⟨Ψ(r+u), T(u) z⟩ = ⟨f_{r+u} √ρ₀, T(u) z⟩`.  The right derivative
of the latter at `τ` is `-∫ (𝓛^ρ - 𝓛^{ρ₀}) f √ρ₀ φ'` (`s67a_gdv`), and `√ρ₀ (𝓛^ρ - 𝓛^{ρ₀}) f = K`
(packet 26) while `R = K - √ρ₀ ∫ √ρ₀ K` pairs with the orbit exactly like `K`.
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

lemma s67bd31_inner_ae {F G : Lp ℝ 2 (volume : Measure (Euc d))} {f g : Euc d → ℝ}
    (hF : ∀ᵐ x ∂(volume : Measure (Euc d)), F x = f x)
    (hG : ∀ᵐ x ∂(volume : Measure (Euc d)), G x = g x) :
    inner ℝ F G = ∫ x, f x * g x := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hF, hG] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

lemma s67bd31_orth (hgL : MemLp (fun x => Real.sqrt (ρ₀ x)) 2 (volume : Measure (Euc d)))
    (w : MovL2Zero ρ₀) : ∫ x, Real.sqrt (ρ₀ x) * movFun w x = 0 := by
  have h := (mov2d_mem_zero_iff (ρ := ρ₀)).1 w.2
  have e : movSqrtLp ρ₀ = hgL.toLp (fun x => Real.sqrt (ρ₀ x)) := by
    unfold movSqrtLp; rw [dif_pos hgL]
  rw [e, s67_inner_toLp_left] at h
  exact h

set_option maxHeartbeats 1600000 in
theorem s67bd_core_pairing_derivative (H : Mov2dTh d s β q ρ₀)
    (g : SchwartzMap (Euc d) ℝ)
    (hg : (⇑g : Euc d → ℝ) = fun x => Real.sqrt (ρ₀ x))
    (m : ℕ) (hm : (d : ℝ) / 2 + 7 < m) (R0 c0 : ℝ)
    (f0 : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ)
    (hρ : MovInSmallClass d s q β ρ₀ m R0 c0 f0 ρ)
    (T : ℝ) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ) (hT : 0 ≤ T)
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff ρ) T φ f)
    (Ψ R : ℝ → MovL2Zero ρ₀)
    (hrep : ∀ r ∈ Icc (0 : ℝ) T,
      (∀ᵐ x ∂(volume : Measure (Euc d)), movFun (Ψ r) x = s67psi ρ₀ (f r) x) ∧
      (∀ᵐ x ∂(volume : Measure (Euc d)), movFun (R r) x =
        s67bd_R d s ρ₀ (movV ρ₀ ρ r) (s67psi ρ₀ (f r)) x))
    (z : MovL2Zero ρ₀) (hz : ∃ z0 : SchwartzMap (Euc d) ℝ,
      ∀ᵐ x ∂(volume : Measure (Euc d)), movFun z x = z0 x)
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) T) (τ : ℝ) (hτ : τ ∈ Ioo (0 : ℝ) (T - r)) :
    HasDerivWithinAt (fun u => inner ℝ (Ψ (r + u)) (mov2d_T H g hg u z))
      (-(inner ℝ (R (r + τ)) (mov2d_T H g hg τ z))) (Ici τ) τ := by
  obtain ⟨z0, hz0⟩ := hz
  have hgL : MemLp (fun x => Real.sqrt (ρ₀ x)) 2 (volume : Measure (Euc d)) := by
    rw [← hg]; exact g.memLp 2
  have hr1 : 0 < r + τ := by linarith [hr.1, hτ.1]
  have hr2 : r + τ < T := by linarith [hτ.2]
  have hrτ : r + τ ∈ Icc (0 : ℝ) T := ⟨hr1.le, hr2.le⟩
  have hgd := HRS.MS.MovAdjNl.s67a_gdv H g hg hf hT hr hz0 hgL hτ
  -- pointwise identification of the two pairings
  have hE : ∀ u : ℝ, τ ≤ u → u < T - r →
      inner ℝ (Ψ (r + u)) (mov2d_T H g hg u z) =
      inner ℝ ((s67a_memLp hf hT r hgL u).toLp (s67a f ρ₀ r T u))
        ((mov2d_T H g hg u z : MovL2Zero ρ₀) : Lp ℝ 2 (volume : Measure (Euc d))) := by
    intro u hu1 hu2
    have hru : r + u ∈ Icc (0 : ℝ) T := ⟨by linarith [hr.1, hτ.1], by linarith⟩
    have hcl : s67clamp r T u = r + u := s67clamp_eq (by linarith [hr.1, hτ.1]) (by linarith)
    set Y := mov2d_T H g hg u z with hY
    show inner ℝ ((Ψ (r + u) : MovL2Zero ρ₀) : Lp ℝ 2 (volume : Measure (Euc d)))
      ((Y : MovL2Zero ρ₀) : Lp ℝ 2 (volume : Measure (Euc d))) = _
    rw [s67bd31_inner_ae (hrep (r + u) hru).1 (g := movFun Y) (Filter.Eventually.of_forall fun x => rfl),
      s67_inner_toLp_left]
    have hA : Integrable (fun x => s67a f ρ₀ r T u x * movFun Y x) volume :=
      (s67a_memLp hf hT r hgL u).integrable_mul (Lp.memLp _)
    have hB : Integrable (fun x => Real.sqrt (ρ₀ x) * movFun Y x) volume :=
      hgL.integrable_mul (Lp.memLp _)
    have hfun : (fun x => s67psi ρ₀ (f (r + u)) x * movFun Y x) =
        fun x => s67a f ρ₀ r T u x * movFun Y x -
          (∫ y, f (r + u) y * ρ₀ y) * (Real.sqrt (ρ₀ x) * movFun Y x) := by
      funext x
      unfold s67psi s67a
      rw [hcl]; ring
    rw [hfun, integral_sub hA (hB.const_mul _), integral_const_mul, s67bd31_orth hgL Y, mul_zero,
      sub_zero]
  -- the derivative value
  obtain ⟨φ', hφ', w, hw, hwd⟩ := s67_T_deriv H g hg hz0 hτ.1.le
  have hfinal : -(∫ x, HRS.MS.MovAdjNl.s67aR d s q β ρ₀ ρ (r + τ) (f (r + τ)) x *
        (Real.sqrt (ρ₀ x) * movFun (mov2d_T H g hg τ z) x)) =
      -(inner ℝ (R (r + τ)) (mov2d_T H g hg τ z)) := by
    obtain ⟨hI1, hI0, hid⟩ := s67bd_generator_difference H m hm R0 c0 f0 ρ hρ T φ f hT hf (r + τ) hrτ
    set Y := mov2d_T H g hg τ z with hY
    have hu : MemCb 2 (f (r + τ)) := hf.isC12TestRd.memCb hrτ
    obtain ⟨Bf, hBf0, hBgen, -⟩ := s67_time_lip hf
    obtain ⟨B0, hB00, hB0⟩ := HRS.MS.MovAdjNl.s67a_L0_growth H hu (r + τ)
    have J1 : Integrable (fun x => generatorW ((quadraticGradientDyn d s q β).coeff ρ) (r + τ)
        (f (r + τ)) x * (Real.sqrt (ρ₀ x) * φ' x)) :=
      HRS.MS.MovAdjNl.s67a_int_lin H (s67_gen_cont hf hrτ).aestronglyMeasurable (hBgen _ hrτ) φ'
    have J2 : Integrable (fun x => generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ₀))
        (r + τ) (f (r + τ)) x * (Real.sqrt (ρ₀ x) * φ' x)) :=
      HRS.MS.MovAdjNl.s67a_int_lin H (HRS.MS.MovAdjNl.s67a_L0_meas H hu (r + τ)) hB0 φ'
    have hAI : Integrable (fun x => HRS.MS.MovAdjNl.s67aR d s q β ρ₀ ρ (r + τ) (f (r + τ)) x *
        (Real.sqrt (ρ₀ x) * movFun Y x)) volume := by
      refine (J1.sub J2).congr ?_
      filter_upwards [hφ'] with x hx
      simp only [Pi.sub_apply]
      rw [hx]
      unfold HRS.MS.MovAdjNl.s67aR
      ring
    have hB : Integrable (fun x => Real.sqrt (ρ₀ x) * movFun Y x) volume :=
      hgL.integrable_mul (Lp.memLp _)
    have hin : inner ℝ (R (r + τ)) Y = ∫ x, s67bd_R d s ρ₀ (movV ρ₀ ρ (r + τ))
        (s67psi ρ₀ (f (r + τ))) x * movFun Y x :=
      s67bd31_inner_ae (F := ((R (r + τ) : MovL2Zero ρ₀) : Lp ℝ 2 (volume : Measure (Euc d))))
        (G := ((Y : MovL2Zero ρ₀) : Lp ℝ 2 (volume : Measure (Euc d)))) (hrep (r + τ) hrτ).2
        (g := movFun Y) (Filter.Eventually.of_forall fun x => rfl)
    rw [hin, neg_inj]
    have hfun : (fun x => s67bd_R d s ρ₀ (movV ρ₀ ρ (r + τ)) (s67psi ρ₀ (f (r + τ))) x *
          movFun Y x) =
        fun x => HRS.MS.MovAdjNl.s67aR d s q β ρ₀ ρ (r + τ) (f (r + τ)) x * (Real.sqrt (ρ₀ x) * movFun Y x) -
          (∫ y, Real.sqrt (ρ₀ y) * s67bd_K d s ρ₀ (movV ρ₀ ρ (r + τ)) (s67psi ρ₀ (f (r + τ))) y) *
            (Real.sqrt (ρ₀ x) * movFun Y x) := by
      funext x
      unfold s67bd_R s67bd_Q
      rw [← hid x]
      unfold HRS.MS.MovAdjNl.s67aR
      ring
    rw [hfun, integral_sub hAI (hB.const_mul _), integral_const_mul, s67bd31_orth hgL Y, mul_zero,
      sub_zero]
  refine (hgd.congr_of_eventuallyEq ?_ (hE τ le_rfl hτ.2)).congr_deriv hfinal
  filter_upwards [Ico_mem_nhdsGE (show τ < T - r from hτ.2)] with u hu
  exact hE u hu.1 hu.2

end HRS.MS.BreakdownS67
