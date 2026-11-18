import HRS.MC.CepH2Aux31

/-!
# CEPH2, S2b (part 1): a Gronwall inequality with continuous forcing and the pathwise moment bound
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ}

theorem h2_gronwall_forced {φ f : ℝ → ℝ} {T κ a : ℝ} (hT : 0 ≤ T) (hκ : 0 ≤ κ)
    (hφ : ContinuousOn φ (Icc 0 T)) (hf : ContinuousOn f (Icc 0 T)) (hf0 : ∀ s ∈ Icc (0 : ℝ) T, 0 ≤ f s)
    (h : ∀ t ∈ Icc (0 : ℝ) T, φ t ≤ a + ∫ r in (0 : ℝ)..t, (κ * φ r + f r)) :
    ∀ t ∈ Icc (0 : ℝ) T, φ t ≤ Real.exp (κ * t) * (a + ∫ r in (0 : ℝ)..t, f r) := by
  set cl : ℝ → ℝ := fun r => max 0 (min r T) with hcl
  have hclc : Continuous cl := continuous_const.max (continuous_id.min continuous_const)
  have hclm : ∀ r, cl r ∈ Icc (0 : ℝ) T := fun r => ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  have hcle : ∀ r ∈ Icc (0 : ℝ) T, cl r = r := fun r hr => by
    simp only [hcl]; rw [min_eq_left hr.2]; exact max_eq_right hr.1
  set φt : ℝ → ℝ := fun r => φ (cl r) with hφt
  set ft : ℝ → ℝ := fun r => f (cl r) with hft
  have hφtc : Continuous φt := hφ.comp_continuous hclc hclm
  have hftc : Continuous ft := hf.comp_continuous hclc hclm
  have hint : ∀ t ∈ Icc (0 : ℝ) T, ∀ (u : ℝ → ℝ) (ut : ℝ → ℝ), (∀ r ∈ Icc (0 : ℝ) T, ut r = u r) →
      ∫ r in (0 : ℝ)..t, ut r = ∫ r in (0 : ℝ)..t, u r := by
    intro t ht u ut hu
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le ht.1] at hr
    exact hu r ⟨hr.1, hr.2.trans ht.2⟩
  have hφe : ∀ r ∈ Icc (0 : ℝ) T, φt r = φ r := fun r hr => by simp only [hφt]; rw [hcle r hr]
  have hfe : ∀ r ∈ Icc (0 : ℝ) T, ft r = f r := fun r hr => by simp only [hft]; rw [hcle r hr]
  set G : ℝ → ℝ := fun t => a + ∫ r in (0 : ℝ)..t, (κ * φt r + ft r) with hG
  have hcont : Continuous fun r => κ * φt r + ft r := (continuous_const.mul hφtc).add hftc
  have hGd : ∀ x, HasDerivAt G (κ * φt x + ft x) x := fun x =>
    (hcont.integral_hasStrictDerivAt 0 x).hasDerivAt.const_add a
  have hGφ : ∀ t ∈ Icc (0 : ℝ) T, φ t ≤ G t := by
    intro t ht
    have h1 := h t ht
    have e : ∫ r in (0 : ℝ)..t, (κ * φt r + ft r) = ∫ r in (0 : ℝ)..t, (κ * φ r + f r) :=
      hint t ht (fun r => κ * φ r + f r) (fun r => κ * φt r + ft r) fun r hr => by
        simp only [hφe r hr, hfe r hr]
    simp only [hG]; rw [e]; exact h1
  set I : ℝ → ℝ := fun x => ∫ s in (0 : ℝ)..x, Real.exp (-κ * s) * ft s with hI
  have hIc : Continuous fun s => Real.exp (-κ * s) * ft s :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hftc
  have hId : ∀ x, HasDerivAt I (Real.exp (-κ * x) * ft x) x := fun x =>
    (hIc.integral_hasStrictDerivAt 0 x).hasDerivAt
  set H : ℝ → ℝ := fun x => Real.exp (-κ * x) * G x - I x with hH
  have hHd : ∀ x, HasDerivAt H (Real.exp (-κ * x) * (κ * (φt x - G x))) x := fun x => by
    have h1 : HasDerivAt (fun x => Real.exp (-κ * x)) (Real.exp (-κ * x) * (-κ)) x := by
      have := ((hasDerivAt_id x).const_mul (-κ)).exp
      simpa [mul_comm] using this
    have h2 := (h1.mul (hGd x)).sub (hId x)
    convert h2 using 1
    ring
  have hanti : AntitoneOn H (Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) (fun x _ => (hHd x).continuousAt.continuousWithinAt)
      (fun x _ => (hHd x).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [(hHd x).deriv]
    have hx' : x ∈ Icc (0 : ℝ) T := interior_subset hx
    have := hGφ x hx'
    rw [hφe x hx'] at *
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (mul_nonpos_of_nonneg_of_nonpos hκ (by linarith))
  intro t ht
  have h0 : H 0 = a := by simp [hH, hG, hI]
  have h1 : H t ≤ H 0 := hanti ⟨le_rfl, hT⟩ ht ht.1
  rw [h0] at h1
  have hI_le : I t ≤ ∫ r in (0 : ℝ)..t, f r := by
    have e : ∫ r in (0 : ℝ)..t, f r = ∫ r in (0 : ℝ)..t, ft r :=
      (hint t ht f ft fun r hr => hfe r hr).symm
    rw [e]
    refine intervalIntegral.integral_mono_on ht.1 ?_ ?_ fun s hs => ?_
    · exact (hIc.intervalIntegrable 0 t)
    · exact hftc.intervalIntegrable 0 t
    · have : Real.exp (-κ * s) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hs.1])
      have h3 : 0 ≤ ft s := by
        rw [hfe s ⟨hs.1, hs.2.trans ht.2⟩]; exact hf0 s ⟨hs.1, hs.2.trans ht.2⟩
      nlinarith
  have h2 : Real.exp (-κ * t) * G t ≤ a + ∫ r in (0 : ℝ)..t, f r := by
    simp only [hH] at h1; linarith
  have h3 : G t ≤ Real.exp (κ * t) * (a + ∫ r in (0 : ℝ)..t, f r) := by
    have := mul_le_mul_of_nonneg_left h2 (Real.exp_pos (κ * t)).le
    rw [← mul_assoc, ← Real.exp_add, show κ * t + -κ * t = 0 by ring, Real.exp_zero, one_mul] at this
    exact this
  exact (hGφ t ht).trans h3

theorem h2_pathwise_moment [NeZero N] {Z Nz : ℝ → Ch N} {B : Ch N → Ch N} (hZc : Continuous Z)
    (hNc : Continuous Nz) {σ' a₀ b : ℝ} (hσ : 0 ≤ σ') (ha₀ : 0 ≤ a₀) (hb : 0 ≤ b) (hB : Continuous B)
    (hBb : ∀ z, ‖B z‖ ≤ a₀ + b * ‖h2_perp z‖)
    (hZeq : ∀ t : ℝ, 0 ≤ t → Z t = Z 0 + (∫ s in Icc (0 : ℝ) t, B (Z s)) + σ' • Nz t) {T : ℝ} (hT : 0 ≤ T) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖h2_perp (Z t)‖ ≤ Real.exp (b * T) * (‖h2_perp (Z 0)‖ + a₀ * T +
      b * σ' * ∫ s in (0 : ℝ)..T, ‖h2_perp (Nz s)‖) + σ' * ‖h2_perp (Nz t)‖ := by
  set L := h2_permL N with hL
  set n : ℝ → ℝ := fun s => ‖h2_perp (Nz s)‖ with hn
  set φ : ℝ → ℝ := fun t => ‖h2_perp (Z t - σ' • Nz t)‖ with hφ
  have hnc : Continuous n := h2_continuous_perp.norm.comp hNc
  have hφc : Continuous φ := h2_continuous_perp.norm.comp (hZc.sub (hNc.const_smul σ'))
  have hn0 : ∀ s, 0 ≤ n s := fun s => norm_nonneg _
  have hsplit : ∀ t, ‖h2_perp (Z t)‖ ≤ φ t + σ' * n t := fun t => by
    have : h2_perp (Z t) = h2_perp (Z t - σ' • Nz t) + σ' • h2_perp (Nz t) := by
      show L (Z t) = L (Z t - σ' • Nz t) + σ' • L (Nz t)
      rw [map_sub, map_smul]; abel
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hσ]
  have hBZ : Continuous fun s => B (Z s) := hB.comp hZc
  have hineq : ∀ t ∈ Icc (0 : ℝ) T, φ t ≤ ‖h2_perp (Z 0)‖ +
      ∫ r in (0 : ℝ)..t, (b * φ r + (a₀ + b * σ' * n r)) := by
    intro t ht
    have h1 : Z t - σ' • Nz t = Z 0 + ∫ s in Icc (0 : ℝ) t, B (Z s) := by
      rw [hZeq t ht.1]; abel
    have h2 : h2_perp (Z t - σ' • Nz t) = h2_perp (Z 0) + ∫ s in Icc (0 : ℝ) t, h2_perp (B (Z s)) := by
      rw [h1]
      show L (Z 0 + ∫ s in Icc (0 : ℝ) t, B (Z s)) = L (Z 0) + ∫ s in Icc (0 : ℝ) t, L (B (Z s))
      rw [map_add, L.integral_comp_comm (hBZ.integrableOn_Icc)]
    have hLB : Continuous fun s => h2_perp (B (Z s)) := h2_continuous_perp.comp hBZ
    have h3 : φ t ≤ ‖h2_perp (Z 0)‖ + ∫ s in Icc (0 : ℝ) t, ‖h2_perp (B (Z s))‖ := by
      simp only [hφ]
      rw [h2]
      refine (norm_add_le _ _).trans (add_le_add le_rfl (norm_integral_le_integral_norm _))
    have h4 : ∫ s in Icc (0 : ℝ) t, ‖h2_perp (B (Z s))‖ ≤
        ∫ s in Icc (0 : ℝ) t, (b * φ s + (a₀ + b * σ' * n s)) := by
      refine setIntegral_mono_on (hLB.norm.integrableOn_Icc)
        ((((continuous_const.mul hφc).add (continuous_const.add (continuous_const.mul hnc)))).integrableOn_Icc)
        measurableSet_Icc fun s hs => ?_
      calc ‖h2_perp (B (Z s))‖ ≤ ‖B (Z s)‖ := h2_norm_perp_le _
        _ ≤ a₀ + b * ‖h2_perp (Z s)‖ := hBb _
        _ ≤ a₀ + b * (φ s + σ' * n s) := by
            have := hsplit s
            nlinarith [mul_le_mul_of_nonneg_left this hb]
        _ = b * φ s + (a₀ + b * σ' * n s) := by ring
    rw [intervalIntegral.integral_of_le ht.1, ← integral_Icc_eq_integral_Ioc]
    linarith
  have hf0 : ∀ s ∈ Icc (0 : ℝ) T, 0 ≤ a₀ + b * σ' * n s := fun s _ => by
    have := hn0 s; positivity
  have hg := h2_gronwall_forced (φ := φ) (f := fun s => a₀ + b * σ' * n s) hT hb hφc.continuousOn
    (continuous_const.add (continuous_const.mul hnc)).continuousOn hf0 hineq
  intro t ht
  refine (hsplit t).trans ?_
  have h5 := hg t ht
  have h6 : ∫ r in (0 : ℝ)..t, (a₀ + b * σ' * n r) = a₀ * t + b * σ' * ∫ r in (0 : ℝ)..t, n r := by
    have hc : Continuous fun r => b * σ' * n r := continuous_const.mul hnc
    rw [intervalIntegral.integral_add intervalIntegrable_const (hc.intervalIntegrable 0 t),
      intervalIntegral.integral_const_mul]
    simp [mul_comm]
  rw [h6] at h5
  have h7 : ∫ r in (0 : ℝ)..t, n r ≤ ∫ r in (0 : ℝ)..T, n r := by
    have h8 := intervalIntegral.integral_add_adjacent_intervals
      (hnc.intervalIntegrable (μ := volume) 0 t) (hnc.intervalIntegrable (μ := volume) t T)
    have h9 : 0 ≤ ∫ r in t..T, n r := intervalIntegral.integral_nonneg ht.2 (fun s _ => hn0 s)
    linarith
  have hI0 : 0 ≤ ∫ r in (0 : ℝ)..t, n r := intervalIntegral.integral_nonneg ht.1 (fun s _ => hn0 s)
  have hA : 0 ≤ ‖h2_perp (Z 0)‖ + (a₀ * t + b * σ' * ∫ r in (0 : ℝ)..t, n r) := by
    have := ht.1; positivity
  have hAle : ‖h2_perp (Z 0)‖ + (a₀ * t + b * σ' * ∫ r in (0 : ℝ)..t, n r) ≤
      ‖h2_perp (Z 0)‖ + a₀ * T + b * σ' * ∫ r in (0 : ℝ)..T, n r := by
    have h10 : a₀ * t ≤ a₀ * T := mul_le_mul_of_nonneg_left ht.2 ha₀
    have h11 : b * σ' * ∫ r in (0 : ℝ)..t, n r ≤ b * σ' * ∫ r in (0 : ℝ)..T, n r :=
      mul_le_mul_of_nonneg_left h7 (mul_nonneg hb hσ)
    linarith
  have hexp : Real.exp (b * t) ≤ Real.exp (b * T) := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hb)
  have h12 : Real.exp (b * t) * (‖h2_perp (Z 0)‖ + (a₀ * t + b * σ' * ∫ r in (0 : ℝ)..t, n r)) ≤
      Real.exp (b * T) * (‖h2_perp (Z 0)‖ + a₀ * T + b * σ' * ∫ r in (0 : ℝ)..T, n r) :=
    mul_le_mul hexp hAle hA (Real.exp_pos _).le
  have h13 : φ t ≤ Real.exp (b * T) * (‖h2_perp (Z 0)‖ + a₀ * T + b * σ' * ∫ r in (0 : ℝ)..T, n r) :=
    h5.trans h12
  show _ ≤ _ + σ' * n t
  linarith

end HRS.MC.CepH2
