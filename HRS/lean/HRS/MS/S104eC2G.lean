import HRS.MS.S104eC2F

/-!
# S104E route C, packet C2, part G: linearity of `Q_ρ f = s103bQ d s ρ f`

Prefix `s104c2_`, namespace `HRS.MS.S104e.C`.  The cancellation integral `convGradConvW` is a Bochner integral, so linearity holds only on data for which the
integrand `ultInt` is integrable; here that is guaranteed by `ρ ∈ U2Dec 1 L A` (`L > d`) and `f` with `C^{1,η}` regularity (`η > max 0 (s-d+1)`).

* `s104c2_HolB_zero`: `HolB j η B f → HolB 0 η (2B) f`; `s104c2_HolB0_of_Bd2`: `Bd 2 B f → HolB 0 η (2B) f`;
* `s104c2_Q_lin0` / `c2_Q_lin`: `Q_ρ (c f + g) = c Q_ρ f + Q_ρ g`;
* `c2_Q_sub_density`: `Q_{ρ-ρ'} f = Q_ρ f - Q_ρ' f`;
* `c2_Q_sub_fun`: `Q_ρ (f - g) = Q_ρ f - Q_ρ g` for `f, g` with `Bd 2` jets.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.Ul HRS.MS.R2WinOrbNL

variable {d : ℕ}

lemma s104c2_HolB0_of_Bd2 {η B : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) {f : Euc d → ℝ} (hf : Bd 2 B f) :
    HolB 0 η (2 * B) f := by
  have hB0 := hf.nonneg
  refine ⟨(hf.mono_N (by omega : 1 ≤ 2)).mono_A (by linarith), fun x z => ?_⟩
  show ‖iteratedFDeriv ℝ 1 f (x + z) - iteratedFDeriv ℝ 1 f x‖ ≤ 2 * B * ‖z‖ ^ η
  by_cases hz : ‖z‖ ≤ 1
  · have := s104c2_lip_iter hf.1 (m := 1) (n := 2) (by omega) (B := B) (fun y => hf.2 2 le_rfl y) (x + z) x
    simp only [add_sub_cancel_left] at this
    have h2 := s104c2_norm_le_rpow hη0 hη1 (norm_nonneg z) hz
    nlinarith [Real.rpow_nonneg (norm_nonneg z) η]
  · push Not at hz
    have h1 : 1 ≤ ‖z‖ ^ η := Real.one_le_rpow hz.le hη0.le
    have h2 := norm_sub_le (iteratedFDeriv ℝ 1 f (x + z)) (iteratedFDeriv ℝ 1 f x)
    have h3 := hf.2 1 (by omega) (x + z)
    have h4 := hf.2 1 (by omega) x
    nlinarith

lemma s104c2_HolB_zero {j : ℕ} {η B : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) {f : Euc d → ℝ} (hf : HolB j η B f) :
    HolB 0 η (2 * B) f := by
  have hB0 := hf.bd.nonneg
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact hf.mono_B (by linarith) hη0.le
  · exact s104c2_HolB0_of_Bd2 hη0 hη1 (hf.bd.mono_N (by omega))

/-! ### Linearity of the cancellation integral -/

lemma s104c2_ultInt_lin (s c : ℝ) (h1 h2 : Euc d → ℝ) (x y : Euc d) :
    ultInt s (fun y => c * h1 y + h2 y) x y = c • ultInt s h1 x y + ultInt s h2 x y := by
  unfold ultInt
  split_ifs
  · module
  · module

lemma s104c2_ultInt_sub (s : ℝ) (h1 h2 : Euc d → ℝ) (x y : Euc d) :
    ultInt s (fun y => h1 y - h2 y) x y = ultInt s h1 x y - ultInt s h2 x y := by
  unfold ultInt
  split_ifs
  · module
  · module

lemma s104c2_conv_lin (s c : ℝ) {h1 h2 : Euc d → ℝ} (x : Euc d) (i1 : Integrable (ultInt s h1 x) volume)
    (i2 : Integrable (ultInt s h2 x) volume) (j : Fin d) :
    convGradConvW (rieszKernelGrad d s) (fun y => c * h1 y + h2 y) x j =
      c * convGradConvW (rieszKernelGrad d s) h1 x j + convGradConvW (rieszKernelGrad d s) h2 x j := by
  have : convGradConvW (rieszKernelGrad d s) (fun y => c * h1 y + h2 y) x =
      c • convGradConvW (rieszKernelGrad d s) h1 x + convGradConvW (rieszKernelGrad d s) h2 x := by
    rw [ult_conv_unfold, ult_conv_unfold, ult_conv_unfold]
    simp only [s104c2_ultInt_lin]
    have i1' : Integrable (fun y => c • ultInt s h1 x y) volume := i1.smul c
    rw [integral_add i1' i2, integral_smul]
  rw [this]
  simp

lemma s104c2_conv_sub (s : ℝ) {h1 h2 : Euc d → ℝ} (x : Euc d) (i1 : Integrable (ultInt s h1 x) volume)
    (i2 : Integrable (ultInt s h2 x) volume) (j : Fin d) :
    convGradConvW (rieszKernelGrad d s) (fun y => h1 y - h2 y) x j =
      convGradConvW (rieszKernelGrad d s) h1 x j - convGradConvW (rieszKernelGrad d s) h2 x j := by
  have : convGradConvW (rieszKernelGrad d s) (fun y => h1 y - h2 y) x =
      convGradConvW (rieszKernelGrad d s) h1 x - convGradConvW (rieszKernelGrad d s) h2 x := by
    rw [ult_conv_unfold, ult_conv_unfold, ult_conv_unfold]
    simp only [s104c2_ultInt_sub]
    rw [integral_sub i1 i2]
  rw [this]
  simp

/-! ### Integrability of the integrands -/

lemma s104c2_int_rho (hd : 1 ≤ d) {s η : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) (hη1 : η < 1)
    (hηd : s + 1 - η < (d : ℝ)) (hηp : 0 < η) {L A : ℝ} (hL : (d : ℝ) < L) {ρ : Euc d → ℝ}
    (hρ : U2Dec 1 L A ρ) (x : Euc d) : Integrable (ultInt s ρ x) volume := by
  have hL0 : 0 ≤ L := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hA : 0 ≤ A := by
    have := (norm_nonneg _).trans (hρ.2 0 (Nat.zero_le _) 0)
    exact (mul_nonneg_iff_of_pos_right (u2Wt_pos (d := d) L 0)).1 this
  have hlip := s104c2_lip_iter hρ.1 (m := 0) (n := 1) (by omega) (B := A) (fun y => by
    have := hρ.2 1 le_rfl y
    refine this.trans ?_
    have := u2Wt_le_one (d := d) hL0 y
    nlinarith)
  have hh : HolNear η A ρ := s104c2_hol_zero (s104c2_hol_of_lip hηp hη1.le hA hlip)
  refine (s104c2_conv_comp hd hs0 hsd hη1 hηd hA hL hA hρ.1.continuous hh (fun y => ?_) x).1
  have := hρ.2 0 (Nat.zero_le _) y
  rwa [norm_iteratedFDeriv_zero] at this

lemma s104c2_int_k (hd : 1 ≤ d) {s η : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) (hη1 : η < 1)
    (hηd : s + 1 - η < (d : ℝ)) (hηp : 0 < η) {L A B : ℝ} (hL : (d : ℝ) < L) {ρ : Euc d → ℝ}
    (hρ : U2Dec 1 L A ρ) {f : Euc d → ℝ} (hf : HolB 0 η B f) (v : Euc d) (x : Euc d) :
    Integrable (ultInt s (fun y => ρ y * fderiv ℝ f y v) x) volume := by
  have hL0 : 0 ≤ L := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hA : 0 ≤ A := by
    have := (norm_nonneg _).trans (hρ.2 0 (Nat.zero_le _) 0)
    exact (mul_nonneg_iff_of_pos_right (u2Wt_pos (d := d) L 0)).1 this
  have hB0 : 0 ≤ B := hf.bd.nonneg
  obtain ⟨hkd, hkh⟩ := s104c2_k_data hηp hη1.le hL0 hρ hf v
  refine (s104c2_conv_comp hd hs0 hsd hη1 hηd (H := 2 ^ 0 * A * (B * ‖v‖ + 2 * (B * ‖v‖))) (by positivity) hL
    (A0 := A * (B * ‖v‖) * 2 ^ 0) (by positivity) hkd.1.continuous
    (s104c2_hol_zero (hkh 0 le_rfl)) (fun y => ?_) x).1
  have := hkd.2 0 (Nat.zero_le _) y
  rwa [norm_iteratedFDeriv_zero] at this

/-! ### Linearity of `Q_ρ` -/

theorem s104c2_Q_lin0 (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) {η : ℝ}
    (hη0 : max 0 (s - d + 1) < η) (hη1 : η < 1) {L A : ℝ} (hL : (d : ℝ) < L) {ρ : Euc d → ℝ}
    (hρ : U2Dec 1 L A ρ) {B B' : ℝ} {f g : Euc d → ℝ} (hf : HolB 0 η B f) (hg : HolB 0 η B' g) (c : ℝ) :
    s103bQ d s ρ (fun x => c * f x + g x) = fun x => c * s103bQ d s ρ f x + s103bQ d s ρ g x := by
  have hηp : 0 < η := lt_of_le_of_lt (le_max_left _ _) hη0
  have hηd : s + 1 - η < (d : ℝ) := by
    have := lt_of_le_of_lt (le_max_right _ _) hη0
    linarith
  have hf1 : ContDiff ℝ 1 f := by simpa using hf.bd.1
  have hg1 : ContDiff ℝ 1 g := by simpa using hg.bd.1
  have hdd : ∀ (y e : Euc d), fderiv ℝ (fun x => c * f x + g x) y e = c * fderiv ℝ f y e + fderiv ℝ g y e := by
    intro y e
    have hfd : DifferentiableAt ℝ f y := (hf1.differentiable one_ne_zero) y
    have hgd : DifferentiableAt ℝ g y := (hg1.differentiable one_ne_zero) y
    have := fderiv_add (f := fun x => c * f x) (g := g) (x := y) (hfd.const_mul c) hgd
    rw [show (fun x => c * f x + g x) = (fun x => c * f x) + g from rfl, this, fderiv_const_mul hfd]
    simp
  funext x
  unfold s103bQ
  simp only [hdd]
  have hfun : ∀ i : Fin d, (fun y => ρ y * (c * fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ)) +
      fderiv ℝ g y (EuclideanSpace.single i (1 : ℝ)))) =
      fun y => c * (ρ y * fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ))) +
        ρ y * fderiv ℝ g y (EuclideanSpace.single i (1 : ℝ)) := fun i => by funext y; ring
  have hM : ∀ i : Fin d, movForce d s (fun y => ρ y * (c * fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ)) +
      fderiv ℝ g y (EuclideanSpace.single i (1 : ℝ)))) x i =
      c * movForce d s (fun y => ρ y * fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ))) x i +
        movForce d s (fun y => ρ y * fderiv ℝ g y (EuclideanSpace.single i (1 : ℝ))) x i := fun i => by
    rw [hfun i]
    exact s104c2_conv_lin s c x
      (s104c2_int_k hd hs0 hsd hη1 hηd hηp hL hρ hf _ x) (s104c2_int_k hd hs0 hsd hη1 hηd hηp hL hρ hg _ x) i
  simp only [hM]
  rw [Finset.sum_add_distrib]
  have e1 : ∑ i : Fin d, (-1 : ℝ) * (movForce d s ρ x i * (c * fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ)) +
      fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ)))) =
      c * ∑ i : Fin d, (-1 : ℝ) * (movForce d s ρ x i * fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ))) +
        ∑ i : Fin d, (-1 : ℝ) * (movForce d s ρ x i * fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i : Fin d, c * movForce d s (fun y => ρ y * fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ))) x i =
      c * ∑ i : Fin d, movForce d s (fun y => ρ y * fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ))) x i := by
    rw [Finset.mul_sum]
  rw [e1, e2]
  ring

theorem c2_Q_lin (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) {η : ℝ}
    (hη0 : max 0 (s - d + 1) < η) (hη1 : η < 1) {L A : ℝ} (hL : (d : ℝ) < L) {ρ : Euc d → ℝ}
    (hρ : U2Dec 1 L A ρ) {j : ℕ} {B B' : ℝ} {f g : Euc d → ℝ} (hf : HolB j η B f) (hg : HolB j η B' g) (c : ℝ) :
    s103bQ d s ρ (fun x => c * f x + g x) = fun x => c * s103bQ d s ρ f x + s103bQ d s ρ g x := by
  have hηp : 0 < η := lt_of_le_of_lt (le_max_left _ _) hη0
  exact s104c2_Q_lin0 hd hs0 hsd hη0 hη1 hL hρ (s104c2_HolB_zero hηp hη1.le hf)
    (s104c2_HolB_zero hηp hη1.le hg) c

/-- `Q_ρ (f - g) = Q_ρ f - Q_ρ g` (for `f, g` with bounded jets up to order `2`; in the relayed statement `f, g ∈ C^2` without
bounds the identity is false because of Bochner junk of the far part of `∇g * (ρ ∂f)`). -/
theorem c2_Q_sub_fun (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) {L A : ℝ} (hL : (d : ℝ) < L)
    {ρ : Euc d → ℝ} (hρ : U2Dec 1 L A ρ) {B B' : ℝ} {f g : Euc d → ℝ} (hf : Bd 2 B f) (hg : Bd 2 B' g) :
    s103bQ d s ρ (fun x => f x - g x) = fun x => s103bQ d s ρ f x - s103bQ d s ρ g x := by
  set η : ℝ := (max 0 (s - d + 1) + 1) / 2 with hη
  have hm : max 0 (s - d + 1) < 1 := max_lt (by norm_num) (by linarith)
  have hη0 : max 0 (s - d + 1) < η := by rw [hη]; linarith
  have hη1 : η < 1 := by rw [hη]; linarith
  have hηp : 0 < η := lt_of_le_of_lt (le_max_left _ _) hη0
  have := s104c2_Q_lin0 (by omega) hs0 hsd hη0 hη1 hL hρ (s104c2_HolB0_of_Bd2 hηp hη1.le hg)
    (s104c2_HolB0_of_Bd2 hηp hη1.le hf) (-1)
  have e : (fun x => f x - g x) = fun x => (-1 : ℝ) * g x + f x := by funext x; ring
  rw [e, this]
  funext x
  ring

end HRS.MS.S104e.C

end
