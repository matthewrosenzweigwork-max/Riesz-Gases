import HRS.PDE.MovSXAux3
import HRS.Equilibrium.QuadraticVariance
import HRS.Sections.Q40bAux3
import HRS.Kernel.D1
import HRS.PDE.MeanFieldKernelD1

/-!
# MOVSX Aux4: the commutator envelope `|h_v| ≤ A L (g + c_*)` for every `d ≥ 1`

`q40b_hdom` (`HRS/Sections/Q40bAux3.lean`) is stated for `2 ≤ d`; its only `d ≥ 2` inputs are the lower envelope
`Quad.periodicRiesz_lower_env` (`g(z) ≥ e(z) - C`) and `periodicRiesz_ge`.  The `d = 1` local singularity
(`periodicRiesz_local_singularity_d1`, `periodicLog_local_singularity_d1`) and `periodicRiesz_ge_of_one_le` give
the same for `d = 1`; the proofs are copies.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Quad

variable {d : ℕ} {s : ℝ}

open HRS HRS.External HRS.External.RefMarg HRS.External.HeatSplit

/-- **Lower envelope** `g(z) ≥ e(z) - C` for `z ≠ 0`, `d ≥ 1` (copy of `periodicRiesz_lower_env`). -/
theorem movsx_periodicRiesz_lower_env (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, ∀ z : Torus d, z ≠ 0 → envT s z - C ≤ periodicRiesz d s z := by
  have hd0 : 0 < d := by omega
  obtain ⟨r, δ, hδ, hr, hsing⟩ : ∃ (r : Torus d → ℝ) (δ : ℝ), 0 < δ ∧ Torus.IsSmooth r ∧
      ∀ x : Euc d, ‖x‖ < δ → x ≠ 0 →
        periodicRiesz d s (Torus.mk x) = (if s = 0 then -Real.log ‖x‖ else ‖x‖ ^ (-s)) + r (Torus.mk x) := by
    by_cases hd2 : 2 ≤ d
    · by_cases hs : s = 0
      · subst hs
        obtain ⟨r, δ, h1, h2, h3⟩ := periodicLog_local_singularity (d := d) hd2
        exact ⟨r, δ, h1, h2, fun x hx hx0 => by simpa using h3 x hx hx0⟩
      · obtain ⟨r, δ, h1, h2, h3⟩ := periodicRiesz_local_singularity hd2 (lt_of_le_of_ne hs0 (Ne.symm hs)) hsd
        exact ⟨r, δ, h1, h2, fun x hx hx0 => by simpa [hs] using h3 x hx hx0⟩
    · have hd1 : d = 1 := by omega
      subst hd1
      by_cases hs : s = 0
      · subst hs
        obtain ⟨r, δ, h1, h2, h3⟩ := periodicLog_local_singularity_d1
        exact ⟨r, δ, h1, h2, fun x hx hx0 => by simpa using h3 x hx hx0⟩
      · obtain ⟨r, δ, h1, h2, h3⟩ := periodicRiesz_local_singularity_d1
          (lt_of_le_of_ne hs0 (Ne.symm hs)) (by simpa using hsd)
        exact ⟨r, δ, h1, h2, fun x hx hx0 => by simpa [hs] using h3 x hx hx0⟩
  have hrc : Continuous r := PoleCavityAux.continuous_of_lift'
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift r) from hr).continuous
  obtain ⟨Mr, hMr⟩ := isCompact_univ.exists_bound_of_continuousOn (f := r) hrc.continuousOn
  obtain ⟨Bg, hBg⟩ := periodicRiesz_ge_of_one_le (d := d) (s := s) hd hs0 hsd
  have hE : (Real.sqrt d / 2) ≥ 0 := by positivity
  -- constants
  set C0 : ℝ := 1 + 2 * max (Real.log δ) 0 + ‖Mr‖ with hC0
  set C1 : ℝ := 1 + δ ^ (-s) + |Real.log δ| + |Real.log (Real.sqrt d / 2)| + Bg with hC1
  refine ⟨max C0 C1 + ‖Mr‖ + |Bg|, fun z hz => ?_⟩
  obtain ⟨y, hyB, rfl⟩ := exists_box_rep z
  have hyb : ∀ i, |y i| ≤ 1 / 2 := fun i => KernelAux.Box_abs_le hyB i
  set ye : Euc d := WithLp.toLp 2 y with hye
  have hmk : Torus.mk ye = KernelAux.boxPt y := by
    funext i
    simp [Torus.mk, KernelAux.boxPt, hye]
  have hed : Torus.eucDist (KernelAux.boxPt y) 0 = ‖ye‖ := eucDist_boxPt_eq hyb
  have hrb : |r (KernelAux.boxPt y)| ≤ ‖Mr‖ := by
    have := hMr (KernelAux.boxPt y) trivial
    simpa [Real.norm_eq_abs] using this.trans (le_abs_self _ |>.trans (by simp))
  have hyne : ye ≠ 0 := by
    intro h0
    apply hz
    funext i
    have := congrFun (congrArg (fun v : Euc d => (v : Fin d → ℝ)) h0) i
    simp [KernelAux.boxPt, hye] at this ⊢
    simp [this]
  have hpos : 0 < ‖ye‖ := norm_pos_iff.2 hyne
  have hMr0 : 0 ≤ ‖Mr‖ := norm_nonneg _
  have hmax0 : 0 ≤ max (Real.log δ) 0 := le_max_right _ _
  by_cases hA : ‖ye‖ < δ
  · have hsg := hsing ye hA hyne
    rw [hmk] at hsg
    rw [hsg]
    unfold envT singEnvelope
    rw [hed]
    have hlb := (abs_le.mp hrb).1
    by_cases hs : s = 0
    · simp only [hs, if_true]
      have hlogle : Real.log ‖ye‖ ≤ Real.log δ := Real.log_le_log hpos hA.le
      have habs : |Real.log ‖ye‖| ≤ -Real.log ‖ye‖ + 2 * max (Real.log δ) 0 := by
        rcases le_total (Real.log ‖ye‖) 0 with h | h
        · rw [abs_of_nonpos h]; linarith
        · rw [abs_of_nonneg h]
          have := le_max_left (Real.log δ) 0
          linarith
      have : 0 ≤ ‖Mr‖ + |Bg| + (max C0 C1 - C0) := by
        have := le_max_left C0 C1; positivity
      nlinarith [le_max_left C0 C1, abs_nonneg Bg]
    · simp only [hs, if_false]
      have : 1 ≤ C0 := by nlinarith
      nlinarith [le_max_left C0 C1, abs_nonneg Bg]
  · push Not at hA
    have hg := hBg (KernelAux.boxPt y)
    unfold envT singEnvelope
    rw [hed]
    have hEle : ‖ye‖ ≤ Real.sqrt d / 2 := by
      rw [← hed]; exact eucDist_le_half_sqrt _
    by_cases hs : s = 0
    · simp only [hs, if_true]
      have hl1 : Real.log δ ≤ Real.log ‖ye‖ := Real.log_le_log hδ hA
      have hl2 : Real.log ‖ye‖ ≤ Real.log (Real.sqrt d / 2) := Real.log_le_log hpos hEle
      have := abs_le_max_abs_abs hl1 hl2
      have h3 : max |Real.log δ| |Real.log (Real.sqrt d / 2)| ≤ |Real.log δ| + |Real.log (Real.sqrt d / 2)| :=
        max_le (by linarith [abs_nonneg (Real.log (Real.sqrt d / 2))])
          (by linarith [abs_nonneg (Real.log δ)])
      have : 0 ≤ ‖Mr‖ + |Bg| := by positivity
      have hC1' : C1 = 1 + 1 + |Real.log δ| + |Real.log (Real.sqrt d / 2)| + Bg := by
        rw [hC1, hs]; simp
      have hm1 := le_max_right C0 C1
      rw [hs] at hg
      linarith [abs_nonneg Bg, le_abs_self Bg, abs_nonneg (Real.log δ), abs_nonneg (Real.log (Real.sqrt d / 2))]
    · simp only [hs, ite_false]
      have h3 : ‖ye‖ ^ (-s) ≤ δ ^ (-s) := Real.rpow_le_rpow_of_nonpos hδ hA (by linarith [lt_of_le_of_ne hs0 (Ne.symm hs)])
      have hm1 := le_max_right C0 C1
      linarith [abs_nonneg Bg, le_abs_self Bg, abs_nonneg (Real.log δ), abs_nonneg (Real.log (Real.sqrt d / 2))]


end HRS.Quad

namespace HRS

variable {d : ℕ} {s : ℝ}

theorem movsx_hdom (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ cstar A : ℝ, 0 ≤ A ∧ (∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + cstar) ∧
      0 ≤ periodicRiesz d s 0 + cstar ∧
      ∀ (L : ℝ) (v : Torus d → Euc d), 0 ≤ L → IsLipschitzVF L v → ∀ x y : Torus d,
        |commKernel (periodicRieszGrad d s) v x y| ≤ (A * L) * (periodicRiesz d s (x - y) + cstar) := by
  obtain ⟨C₀, hC₀, hC⟩ := Commutator.commKernel_bound (d := d) (s := s) hd hs0 hsd
  obtain ⟨Bg, hBg⟩ := periodicRiesz_ge_of_one_le (d := d) (s := s) hd hs0 hsd
  obtain ⟨Cenv, hCenv⟩ := Quad.movsx_periodicRiesz_lower_env (d := d) (s := s) hd hs0 hsd
  set cstar : ℝ := max (Bg + 1) (max Cenv |periodicRiesz d s 0|) with hcstar
  have hc1 : Bg + 1 ≤ cstar := le_max_left _ _
  have hc2 : Cenv ≤ cstar := (le_max_left _ _).trans (le_max_right _ _)
  have hc3 : |periodicRiesz d s 0| ≤ cstar := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨cstar, 2 * C₀, by positivity, fun z _ => by linarith [hBg z], ?_, ?_⟩
  · have := neg_abs_le (periodicRiesz d s 0); linarith
  · intro L v hL hv x y
    by_cases hxy : x = y
    · subst hxy
      simp only [commKernel, if_true, abs_zero]
      have h0 : 0 ≤ periodicRiesz d s (x - x) + cstar := by
        rw [sub_self]; have := neg_abs_le (periodicRiesz d s 0); linarith
      positivity
    · have h1 := hC L v hL hv x y hxy
      have hz : x - y ≠ 0 := sub_ne_zero.2 hxy
      have h2 := hCenv (x - y) hz
      have h3 : KernelGrad.tdist x y ^ (-s) + 1 ≤ 2 * Quad.envT s (x - y) := by
        have hone := Quad.one_le_envT (d := d) (s := s) (x - y)
        by_cases hs : s = 0
        · subst hs
          simp only [neg_zero, Real.rpow_zero]
          linarith
        · have hE : Quad.envT s (x - y) = Torus.eucDist (x - y) 0 ^ (-s) + 1 := by
            unfold Quad.envT singEnvelope
            simp only [hs, if_false]; ring
          rw [Q40b.q40b_tdist_eq_eucDist, hE]
          rw [hE] at hone
          linarith
      calc |commKernel (periodicRieszGrad d s) v x y|
          ≤ C₀ * L * (KernelGrad.tdist x y ^ (-s) + 1) := h1
        _ ≤ C₀ * L * (2 * Quad.envT s (x - y)) := by gcongr
        _ ≤ C₀ * L * (2 * (periodicRiesz d s (x - y) + cstar)) := by
          gcongr
          linarith
        _ = (2 * C₀ * L) * (periodicRiesz d s (x - y) + cstar) := by ring

end HRS

end
