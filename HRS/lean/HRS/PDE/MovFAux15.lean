import HRS.PDE.MovFAux14
import HRS.Appendix.B15CAux1
import HRS.Kernel.GradD1

/-!
# MOVF Aux15: the Gibbs weight against the force, `e^{-a g} |∇g| ∈ L¹(𝕋^d)` for `a > 0`

`movf_local_lower`: `g(mk y) ≥ sing ‖y‖ - R` near `0` with `sing u = u^{-s}` (`s > 0`) or `-log u` (`s = 0`).
`movf_E_bound`: `e^{-a g(z)} ‖∇g(z)‖ ≤ C₁ ‖z‖^{-t} + C₂` with `0 ≤ t < d`; `movf_E_integrable`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movf_local_lower (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ (δ R : ℝ), 0 < δ ∧ 0 ≤ R ∧ ∀ y : Euc d, y ≠ 0 → ‖y‖ < δ →
      (if s = 0 then -Real.log ‖y‖ else ‖y‖ ^ (-s)) - R ≤ periodicRiesz d s (Torus.mk y) := by
  have key : ∀ (sing : ℝ → ℝ) (r : Torus d → ℝ) (δ : ℝ), 0 < δ → Torus.IsSmooth r →
      (∀ x : Euc d, ‖x‖ < δ → x ≠ 0 → periodicRiesz d s (Torus.mk x) = sing ‖x‖ + r (Torus.mk x)) →
      ∃ (δ R : ℝ), 0 < δ ∧ 0 ≤ R ∧ ∀ y : Euc d, y ≠ 0 → ‖y‖ < δ → sing ‖y‖ - R ≤ periodicRiesz d s (Torus.mk y) := by
    intro sing r δ hδ hr hloc
    obtain ⟨R, hR⟩ := b15_bounded_of_continuous (b15c_isSmooth_continuous hr)
    refine ⟨δ, |R|, hδ, abs_nonneg _, fun y hy hlt => ?_⟩
    rw [hloc y hlt hy]
    have := neg_abs_le (r (Torus.mk y))
    have := hR (Torus.mk y)
    have := le_abs_self R
    linarith
  rcases eq_or_lt_of_le hs0 with h0 | hpos
  · subst h0
    rcases hd.eq_or_lt with h1 | h2
    · subst h1
      obtain ⟨r, δ, hδ, hr, hloc⟩ := periodicLog_local_singularity_d1
      obtain ⟨δ', R, h1, h2, h3⟩ := key (fun u => -Real.log u) r δ hδ hr hloc
      exact ⟨δ', R, h1, h2, fun y hy hlt => by simpa using h3 y hy hlt⟩
    · obtain ⟨r, δ, hδ, hr, hloc⟩ := periodicLog_local_singularity (d := d) (by omega)
      obtain ⟨δ', R, h1, h2, h3⟩ := key (fun u => -Real.log u) r δ hδ hr hloc
      exact ⟨δ', R, h1, h2, fun y hy hlt => by simpa using h3 y hy hlt⟩
  · rcases hd.eq_or_lt with h1 | h2
    · subst h1
      have hs1 : s < 1 := by simpa using hsd
      obtain ⟨r, δ, hδ, hr, hloc⟩ := periodicRiesz_local_singularity_d1 hpos hs1
      obtain ⟨δ', R, h1, h2, h3⟩ := key (fun u => u ^ (-s)) r δ hδ hr hloc
      exact ⟨δ', R, h1, h2, fun y hy hlt => by simpa [hpos.ne'] using h3 y hy hlt⟩
    · obtain ⟨r, δ, hδ, hr, hloc⟩ := periodicRiesz_local_singularity (d := d) (by omega) hpos hsd
      obtain ⟨δ', R, h1, h2, h3⟩ := key (fun u => u ^ (-s)) r δ hδ hr hloc
      exact ⟨δ', R, h1, h2, fun y hy hlt => by simpa [hpos.ne'] using h3 y hy hlt⟩

theorem movf_exp_neg_rpow {a s u : ℝ} (ha : 0 < a) (hu : 0 < u) (k : ℕ) :
    Real.exp (-(a * u ^ (-s))) ≤ (k.factorial : ℝ) / a ^ k * u ^ (s * k) := by
  have hx : 0 < a * u ^ (-s) := mul_pos ha (Real.rpow_pos_of_pos hu _)
  have h1 := Real.pow_div_factorial_le_exp (a * u ^ (-s)) hx.le k
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hxk : (a * u ^ (-s)) ^ k = a ^ k * u ^ (-(s * k)) := by
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]
    congr 1; ring
  rw [Real.exp_neg]
  have h2 : (Real.exp (a * u ^ (-s)))⁻¹ ≤ ((a * u ^ (-s)) ^ k / k.factorial)⁻¹ :=
    inv_anti₀ (by positivity) h1
  refine h2.trans (le_of_eq ?_)
  rw [hxk, Real.rpow_neg hu.le]
  field_simp

theorem movf_E_bound (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a : ℝ} (ha : 0 < a) :
    ∃ t C₁ C₂ : ℝ, 0 ≤ t ∧ t < d ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ z : Torus d, z ≠ 0 →
      Real.exp (-a * periodicRiesz d s z) * ‖periodicRieszGrad d s z‖ ≤ C₁ * ‖z‖ ^ (-t) + C₂ := by
  obtain ⟨CG, hG⟩ := KernelGradD1.goodKernel_periodicRieszGrad_of_one_le hd hs0 hsd
  obtain ⟨B0, hB0⟩ := periodicRiesz_ge_of_one_le (d := d) hd hs0 hsd
  obtain ⟨δ, R, hδ, hR0, hloc⟩ := movf_local_lower hd hs0 hsd
  have hCG0 := hG.hC0
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set δ₀ : ℝ := min δ (1 / 4) with hδ₀
  have hδ₀0 : 0 < δ₀ := lt_min hδ (by norm_num)
  have hδ₀1 : δ₀ ≤ 1 / 4 := min_le_right _ _
  -- the far region
  set Cfar : ℝ := Real.exp (a * |B0|) * (CG * (δ₀ ^ (-s - 1) + 1)) with hCfar
  have hCfar0 : 0 ≤ Cfar := by positivity
  have hfar : ∀ z : Torus d, z ≠ 0 → δ₀ ≤ Torus.tdist z 0 →
      Real.exp (-a * periodicRiesz d s z) * ‖periodicRieszGrad d s z‖ ≤ Cfar := by
    intro z hz hfarz
    have hu0 : 0 < Torus.tdist z 0 := KernelGrad.tdist_pos hz
    have h1 : Real.exp (-a * periodicRiesz d s z) ≤ Real.exp (a * |B0|) := by
      refine Real.exp_le_exp.2 ?_
      have h1 := hB0 z
      have h2 : a * B0 ≤ a * |B0| := mul_le_mul_of_nonneg_left (le_abs_self B0) ha.le
      nlinarith
    have h2 : ‖periodicRieszGrad d s z‖ ≤ CG * (δ₀ ^ (-s - 1) + 1) := by
      refine (hG.bound z hz).trans ?_
      have : KernelGrad.tdist z 0 ^ (-s - 1) ≤ δ₀ ^ (-s - 1) :=
        Real.rpow_le_rpow_of_nonpos hδ₀0 hfarz (by linarith)
      exact mul_le_mul_of_nonneg_left (by linarith) hCG0
    exact mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos _).le
  -- the near region
  have hnear : ∃ t E : ℝ, 0 ≤ t ∧ t < d ∧ 0 ≤ E ∧ ∀ z : Torus d, z ≠ 0 → Torus.tdist z 0 < δ₀ →
      Real.exp (-a * periodicRiesz d s z) * ‖periodicRieszGrad d s z‖ ≤ E * (Torus.tdist z 0 ^ (-t) + 1) := by
    -- common reduction
    have red : ∀ z : Torus d, z ≠ 0 → Torus.tdist z 0 < δ₀ → ∃ y : Euc d, y ≠ 0 ∧ ‖y‖ = Torus.tdist z 0 ∧
        0 < ‖y‖ ∧ ‖y‖ < δ ∧ ‖y‖ ≤ 1 / 4 ∧ Torus.mk y = z := by
      intro z hz hlt
      obtain ⟨y, hyz, hybox⟩ := KernelGrad.exists_mk_box z
      have hnorm : ‖y‖ = Torus.tdist z 0 := by rw [← hyz]; exact (KernelGrad.tdist_mk hybox).symm
      have hy0 : y ≠ 0 := by
        intro h; apply hz; rw [← hyz, h]; exact b15c_mk_zero
      refine ⟨y, hy0, hnorm, norm_pos_iff.2 hy0, ?_, ?_, hyz⟩
      · rw [hnorm]; exact lt_of_lt_of_le hlt (min_le_left _ _)
      · rw [hnorm]; exact (hlt.le.trans hδ₀1)
    rcases eq_or_lt_of_le hs0 with h0 | hpos
    · -- `s = 0`
      subst h0
      refine ⟨max (1 - a) 0, Real.exp (a * R) * CG * 2, le_max_right _ _, ?_, by positivity, ?_⟩
      · have : max (1 - a) 0 < d := by
          rcases max_cases (1 - a) 0 with h | h
          · rw [h.1]; have : (1 : ℝ) ≤ d := by exact_mod_cast hd
            linarith
          · rw [h.1]; exact hd0
        exact this
      · intro z hz hlt
        obtain ⟨y, hy0, hnorm, hypos, hyδ, hy4, hyz⟩ := red z hz hlt
        have hl := hloc y hy0 hyδ
        rw [hyz] at hl
        simp only [if_true] at hl
        set u := Torus.tdist z 0 with hu
        have hupos : 0 < u := KernelGrad.tdist_pos hz
        have hu1 : u ≤ 1 := by linarith
        rw [hnorm] at hl
        have e1 : Real.exp (-a * periodicRiesz d 0 z) ≤ Real.exp (a * R) * u ^ a := by
          have : -a * periodicRiesz d 0 z ≤ a * R + a * Real.log u := by nlinarith
          calc Real.exp (-a * periodicRiesz d 0 z) ≤ Real.exp (a * R + a * Real.log u) :=
                Real.exp_le_exp.2 this
            _ = Real.exp (a * R) * u ^ a := by
                rw [Real.exp_add, Real.rpow_def_of_pos hupos]; congr 2; ring
        have e2 : ‖periodicRieszGrad d 0 z‖ ≤ CG * (u ^ (-(1 : ℝ)) + 1) := by
          refine (hG.bound z hz).trans (le_of_eq ?_)
          simp only [neg_zero, zero_sub]
          rfl
        have e3 : u ^ a * (u ^ (-(1 : ℝ)) + 1) ≤ 2 * (u ^ (-(max (1 - a) 0)) + 1) := by
          have h1 : u ^ a * u ^ (-(1 : ℝ)) = u ^ (a - 1) := by
            rw [← Real.rpow_add hupos]; exact congrArg (u ^ ·) (by ring)
          have h2 : u ^ (a - 1) ≤ u ^ (-(max (1 - a) 0)) :=
            Real.rpow_le_rpow_of_exponent_ge hupos hu1 (by
              have := le_max_left (1 - a) 0; linarith)
          have h3 : u ^ a ≤ 1 := Real.rpow_le_one hupos.le hu1 ha.le
          have h4 : 0 ≤ u ^ (-(max (1 - a) 0)) := Real.rpow_nonneg hupos.le _
          calc u ^ a * (u ^ (-(1 : ℝ)) + 1) = u ^ (a - 1) + u ^ a := by rw [mul_add, h1, mul_one]
            _ ≤ 2 * (u ^ (-(max (1 - a) 0)) + 1) := by linarith
        calc Real.exp (-a * periodicRiesz d 0 z) * ‖periodicRieszGrad d 0 z‖ ≤
            (Real.exp (a * R) * u ^ a) * (CG * (u ^ (-(1 : ℝ)) + 1)) :=
              mul_le_mul e1 e2 (norm_nonneg _) (by positivity)
          _ = Real.exp (a * R) * CG * (u ^ a * (u ^ (-(1 : ℝ)) + 1)) := by ring
          _ ≤ Real.exp (a * R) * CG * (2 * (u ^ (-(max (1 - a) 0)) + 1)) :=
              mul_le_mul_of_nonneg_left e3 (by positivity)
          _ = Real.exp (a * R) * CG * 2 * (u ^ (-(max (1 - a) 0)) + 1) := by ring
    · -- `s > 0`
      set k : ℕ := ⌈1 / s⌉₊ with hk
      have hsk : 1 ≤ s * k := by
        have := Nat.le_ceil (1 / s)
        have h2 : 1 / s ≤ (k : ℝ) := this
        calc (1 : ℝ) = s * (1 / s) := by field_simp
          _ ≤ s * k := mul_le_mul_of_nonneg_left h2 hpos.le
      refine ⟨s, Real.exp (a * R) * ((k.factorial : ℝ) / a ^ k) * CG * 2, hpos.le, hsd, by positivity, ?_⟩
      intro z hz hlt
      obtain ⟨y, hy0, hnorm, hypos, hyδ, hy4, hyz⟩ := red z hz hlt
      have hl := hloc y hy0 hyδ
      rw [hyz] at hl
      simp only [hpos.ne', ite_false] at hl
      set u := Torus.tdist z 0 with hu
      have hupos : 0 < u := KernelGrad.tdist_pos hz
      have hu1 : u ≤ 1 := by linarith
      rw [hnorm] at hl
      have e1 : Real.exp (-a * periodicRiesz d s z) ≤ Real.exp (a * R) *
          ((k.factorial : ℝ) / a ^ k * u ^ (s * k)) := by
        have : -a * periodicRiesz d s z ≤ a * R + -(a * u ^ (-s)) := by nlinarith
        calc Real.exp (-a * periodicRiesz d s z) ≤ Real.exp (a * R + -(a * u ^ (-s))) :=
              Real.exp_le_exp.2 this
          _ = Real.exp (a * R) * Real.exp (-(a * u ^ (-s))) := Real.exp_add _ _
          _ ≤ Real.exp (a * R) * ((k.factorial : ℝ) / a ^ k * u ^ (s * k)) :=
              mul_le_mul_of_nonneg_left (movf_exp_neg_rpow ha hupos k) (Real.exp_pos _).le
      have e2 : ‖periodicRieszGrad d s z‖ ≤ CG * (u ^ (-s - 1) + 1) := hG.bound z hz
      have e3 : u ^ (s * k) * (u ^ (-s - 1) + 1) ≤ 2 * (u ^ (-s) + 1) := by
        have h1 : u ^ (s * k) * u ^ (-s - 1) = u ^ (s * k - s - 1) := by
          rw [← Real.rpow_add hupos]; exact congrArg (u ^ ·) (by ring)
        have h2 : u ^ (s * k - s - 1) ≤ u ^ (-s) :=
          Real.rpow_le_rpow_of_exponent_ge hupos hu1 (by linarith)
        have h3 : u ^ (s * k) ≤ 1 := Real.rpow_le_one hupos.le hu1 (by positivity)
        have h4 : 0 ≤ u ^ (-s) := Real.rpow_nonneg hupos.le _
        calc u ^ (s * k) * (u ^ (-s - 1) + 1) = u ^ (s * k - s - 1) + u ^ (s * k) := by
              rw [mul_add, h1, mul_one]
          _ ≤ 2 * (u ^ (-s) + 1) := by linarith
      have hE0 : 0 ≤ Real.exp (a * R) * ((k.factorial : ℝ) / a ^ k) := by positivity
      calc Real.exp (-a * periodicRiesz d s z) * ‖periodicRieszGrad d s z‖ ≤
          (Real.exp (a * R) * ((k.factorial : ℝ) / a ^ k * u ^ (s * k))) * (CG * (u ^ (-s - 1) + 1)) :=
            mul_le_mul e1 e2 (norm_nonneg _) (by positivity)
        _ = Real.exp (a * R) * ((k.factorial : ℝ) / a ^ k) * CG * (u ^ (s * k) * (u ^ (-s - 1) + 1)) := by ring
        _ ≤ Real.exp (a * R) * ((k.factorial : ℝ) / a ^ k) * CG * (2 * (u ^ (-s) + 1)) :=
            mul_le_mul_of_nonneg_left e3 (by positivity)
        _ = Real.exp (a * R) * ((k.factorial : ℝ) / a ^ k) * CG * 2 * (u ^ (-s) + 1) := by ring
  obtain ⟨t, E, ht0, htd, hE0, hnearz⟩ := hnear
  refine ⟨t, E, E + Cfar, ht0, htd, hE0, by positivity, fun z hz => ?_⟩
  have hnz : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hu : ‖z‖ ≤ Torus.tdist z 0 := KernelGrad.norm_le_tdist z
  rcases lt_or_ge (Torus.tdist z 0) δ₀ with hlt | hge
  · have h1 := hnearz z hz hlt
    have h2 : Torus.tdist z 0 ^ (-t) ≤ ‖z‖ ^ (-t) := Real.rpow_le_rpow_of_nonpos hnz hu (by linarith)
    calc _ ≤ E * (Torus.tdist z 0 ^ (-t) + 1) := h1
      _ ≤ E * (‖z‖ ^ (-t) + 1) := mul_le_mul_of_nonneg_left (by linarith) hE0
      _ ≤ E * ‖z‖ ^ (-t) + (E + Cfar) := by nlinarith
  · have h1 := hfar z hz hge
    have h2 : 0 ≤ E * ‖z‖ ^ (-t) := mul_nonneg hE0 (Real.rpow_nonneg hnz.le _)
    linarith

theorem movf_E_integrable (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : Torus d => Real.exp (-a * periodicRiesz d s z) * ‖periodicRieszGrad d s z‖) := by
  obtain ⟨t, C₁, C₂, ht0, htd, hC₁, hC₂, hb⟩ := movf_E_bound hd hs0 hsd ha
  have hgm : Measurable (periodicRiesz d s : Torus d → ℝ) := CoercAux.measurable_periodicRiesz_one hd hs0 hsd
  have hGm := KernelGrad.measurable_periodicRieszGrad hsd (d := d)
  have hm : Measurable fun z : Torus d => Real.exp (-a * periodicRiesz d s z) * ‖periodicRieszGrad d s z‖ :=
    (Real.measurable_exp.comp (measurable_const.mul hgm)).mul hGm.norm
  have hint : Integrable (fun z : Torus d => C₁ * ‖z‖ ^ (-t) + C₂) :=
    ((KernelGrad.integrable_norm_rpow_neg (by omega) htd).const_mul C₁).add (integrable_const _)
  refine hint.mono' hm.aestronglyMeasurable ?_
  filter_upwards [KernelGrad.torus_ae_ne' (by omega : 0 < d)] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
  exact hb z hz

end HRS

end
