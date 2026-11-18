import HRS.PDE.TorusFPExistAux8

/-!
# D1 existence, helper 9: restriction of solutions and the semigroup identity
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS

variable {n : ℕ}

theorem D1BackwardSolution.restrict {κ : ℝ} {b : Torus n → Euc n} {t s : ℝ} (hst : s ≤ t)
    {φ : Torus n → ℝ} {f : ℝ → Torus n → ℝ} (h : D1BackwardSolution κ b t φ f) :
    D1BackwardSolution κ b s (f s) f where
  c2 r hr := h.c2 r ⟨hr.1, hr.2.trans hst⟩
  cont_c2 j hj := by
    have h1 := (h.cont_c2 j hj).comp ((continuous_inclusion (Set.Icc_subset_Icc_right hst)).prodMap continuous_id)
    refine h1.congr fun p => ?_
    rfl
  terminal := rfl
  time_deriv x r hr := h.time_deriv x r ⟨hr.1, hr.2.trans_le hst⟩
  cont_time_deriv := by
    have h1 := h.cont_time_deriv.comp ((continuous_inclusion (Set.Icc_subset_Icc_right hst)).prodMap continuous_id)
    refine h1.congr fun p => ?_
    rfl

theorem d1_eq_of_forall_abs_le_inv {a b C : ℝ} (h : ∀ k : ℕ, |a - b| ≤ C / ((k : ℝ) + 1)) : a = b := by
  by_contra hne
  have hpos : 0 < |a - b| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨k, hk⟩ := exists_nat_gt (C / |a - b|)
  have h1 := h k
  have h2 : C / ((k : ℝ) + 1) < |a - b| := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hpos] at hk
    nlinarith [hpos]
  linarith

theorem d1_abs_integral_sub_le {ρ : Measure (Torus n)} [IsProbabilityMeasure ρ] {g₁ g₂ : Torus n → ℝ}
    (h₁ : Continuous g₁) (h₂ : Continuous g₂) {c : ℝ} (hc : ∀ x, |g₁ x - g₂ x| ≤ c) :
    |∫ x, g₁ x ∂ρ - ∫ x, g₂ x ∂ρ| ≤ c := by
  have i1 : Integrable g₁ ρ := h₁.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have i2 : Integrable g₂ ρ := h₂.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← integral_sub i1 i2]
  calc |∫ x, (g₁ x - g₂ x) ∂ρ| ≤ ∫ x, |g₁ x - g₂ x| ∂ρ := abs_integral_le_integral_abs
    _ ≤ ∫ _x, c ∂ρ := integral_mono_of_nonneg (ae_of_all _ fun x => abs_nonneg _)
          (integrable_const _) (ae_of_all _ hc)
    _ = c := by simp

section Semigroup

variable (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
  (μ₀ : Measure (Torus n)) [IsProbabilityMeasure μ₀]

/-- The semigroup identity `⟨U^{0,h}φ, μ_s⟩ = ⟨U^{0,s+h} φ, μ₀⟩`. -/
theorem d1_mu_semigroup {s h : ℝ} (hs : 0 ≤ s) (hh : 0 ≤ h) {φ : Torus n → ℝ}
    (hφ : Torus.IsSmooth φ) :
    ∫ x, d1_P hn hκ hU h φ x ∂(d1_mu hn hκ hU μ₀ s) =
      ∫ x, d1_P hn hκ hU (s + h) φ x ∂μ₀ := by
  rcases hs.eq_or_lt with rfl | hs0
  · rw [d1_mu_of_nonpos hn hκ hU μ₀ le_rfl, zero_add]
  have := d1_mu_prob hn hκ hU μ₀ s
  set T : ℝ := s + h + 1 with hT
  have hTpos : 0 < T := by rw [hT]; linarith
  have hf := d1_sol_spec hn hκ hU hTpos hφ
  set f := d1_sol hn hκ hU T φ with hfdef
  have hgc : Continuous (d1_P hn hκ hU h φ) := d1_P_continuous hn hκ hU hh hφ
  have hgx : ∀ x, d1_P hn hκ hU h φ x = f (T - h) x := fun x =>
    d1_P_eq hn hκ hU hTpos hφ hf ⟨hh, by rw [hT]; linarith⟩ x
  have hsh : ∀ x, d1_P hn hκ hU (s + h) φ x = f (T - (s + h)) x := fun x =>
    d1_P_eq hn hκ hU hTpos hφ hf ⟨by linarith, by rw [hT]; linarith⟩ x
  have hf₂ := hf.shift (show 0 < s + h by linarith) (show s + h ≤ T by rw [hT]; linarith)
  have hf₃ := hf₂.restrict (show s ≤ s + h by linarith)
  have key : ∀ k : ℕ, |∫ x, d1_P hn hκ hU h φ x ∂(d1_mu hn hκ hU μ₀ s) -
      ∫ x, d1_P hn hκ hU (s + h) φ x ∂μ₀| ≤ 2 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨ψ, hψ, hψg⟩ := d1_exists_smooth_seq hgc k
    have hψc : Continuous ψ := StaticLimitAux.continuous_of_smooth hψ
    have hsol := d1_sol_spec hn hκ hU hs0 hψ
    have hdat : ∀ x, |ψ x - (fun r => f (r + (T - (s + h)))) s x| ≤ 1 / ((k : ℝ) + 1) := by
      intro x
      have e : (fun r => f (r + (T - (s + h)))) s x = d1_P hn hκ hU h φ x := by
        rw [hgx]
        show f (s + (T - (s + h))) x = f (T - h) x
        rw [show s + (T - (s + h)) = T - h by ring]
      rw [e, abs_sub_comm]
      exact hψg x
    have hb := d1_backward_abs_le hκ hs0 hsol hf₃ hdat 0 ⟨le_rfl, hs0.le⟩
    have hbound : ∀ x, |d1_P hn hκ hU s ψ x - d1_P hn hκ hU (s + h) φ x| ≤ 1 / ((k : ℝ) + 1) := by
      intro x
      have h1 : d1_P hn hκ hU s ψ x = d1_sol hn hκ hU s ψ 0 x := by
        unfold d1_P; rw [if_pos hs0]
      have h2 : d1_P hn hκ hU (s + h) φ x = (fun r => f (r + (T - (s + h)))) 0 x := by
        rw [hsh]; simp
      rw [h1, h2]
      exact hb x
    have t1 : |∫ x, d1_P hn hκ hU h φ x ∂(d1_mu hn hκ hU μ₀ s) -
        ∫ x, ψ x ∂(d1_mu hn hκ hU μ₀ s)| ≤ 1 / ((k : ℝ) + 1) :=
      d1_abs_integral_sub_le hgc hψc hψg
    have t2 : |∫ x, d1_P hn hκ hU s ψ x ∂μ₀ - ∫ x, d1_P hn hκ hU (s + h) φ x ∂μ₀| ≤
        1 / ((k : ℝ) + 1) :=
      d1_abs_integral_sub_le (d1_P_continuous hn hκ hU hs0.le hψ)
        (d1_P_continuous hn hκ hU (by linarith) hφ) hbound
    rw [d1_mu_integral hn hκ hU μ₀ hs0.le hψ] at t1
    have : 2 / ((k : ℝ) + 1) = 1 / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1) := by ring
    rw [this]
    calc _ = |(∫ x, d1_P hn hκ hU h φ x ∂(d1_mu hn hκ hU μ₀ s) - ∫ x, d1_P hn hκ hU s ψ x ∂μ₀) +
          (∫ x, d1_P hn hκ hU s ψ x ∂μ₀ - ∫ x, d1_P hn hκ hU (s + h) φ x ∂μ₀)| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add t1 t2)
  exact d1_eq_of_forall_abs_le_inv key

end Semigroup

end HRS
