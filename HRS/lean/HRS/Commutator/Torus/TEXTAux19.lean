import HRS.Commutator.Torus.TEXTAux18

/-!
# T-EXT-A helpers, part 19: `bernstein_T`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

theorem text_bernstein_main (hd : 1 ≤ d) (R : ℝ) (hR : 0 < R) (p q : ℝ≥0∞) (hp : 1 ≤ p)
    (hpq : p ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ a : Torus d → ℝ, MemLp a p volume →
      (∀ k : Lattice d, R < η * Lattice.enorm k → Torus.fcoef a k = 0) →
        MemLp a q volume ∧
          eLpNorm a q volume ≤
            ENNReal.ofReal (C * η ^ (-(d : ℝ) * ((p⁻¹).toReal - (q⁻¹).toReal))) *
              eLpNorm a p volume := by
  classical
  obtain ⟨B, C₁, hB, hC₁, hker⟩ := text_bern_kernel hd R hR
  by_cases hpt : p = ⊤
  · have hqt : q = ⊤ := top_le_iff.1 (hpt ▸ hpq)
    subst hpt; subst hqt
    refine ⟨1, one_pos, fun η hη hη1 a ha _ => ⟨ha, ?_⟩⟩
    simp
  set θ : ℝ := (p⁻¹).toReal with hθ
  set K₀ : ℝ := B ^ θ * C₁ ^ (1 - θ) with hK₀
  have hθ0 : 0 ≤ θ := ENNReal.toReal_nonneg
  have hp0' : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hp0 : (0 : ℝ) < p.toReal := ENNReal.toReal_pos hp0' hpt
  have hp1r : 1 ≤ p.toReal := by
    have := ENNReal.toReal_mono hpt hp
    simpa using this
  have hθp : θ * p.toReal = 1 := by rw [hθ, ENNReal.toReal_inv]; field_simp
  have hθ1 : θ ≤ 1 := by nlinarith
  have hK₀pos : 0 < K₀ := by positivity
  set s : ℝ := 1 - p.toReal * (q⁻¹).toReal with hs
  have hqinv : (q⁻¹).toReal ≤ θ :=
    ENNReal.toReal_mono (ENNReal.inv_ne_top.2 hp0') (ENNReal.inv_le_inv.2 hpq)
  have hqinv0 : 0 ≤ (q⁻¹).toReal := ENNReal.toReal_nonneg
  have hs0 : 0 ≤ s := by
    have : p.toReal * (q⁻¹).toReal ≤ p.toReal * θ := mul_le_mul_of_nonneg_left hqinv hp0.le
    rw [hs]; nlinarith
  have hs1 : s ≤ 1 := by rw [hs]; nlinarith [mul_nonneg hp0.le hqinv0]
  have hθs : θ * s = θ - (q⁻¹).toReal := by
    rw [hs]; nlinarith
  refine ⟨K₀ ^ s + 1, by positivity, fun η hη hη1 a ha hsupp => ?_⟩
  set p' : ℝ≥0∞ := ENNReal.conjExponent p with hp'
  haveI hpp : p.HolderConjugate p' := ENNReal.HolderConjugate.conjExponent hp
  obtain ⟨Ψ, hΨint, hΨsup, hΨ1, hΨcoef⟩ := hker η hη hη1
  have hbη : 0 ≤ B * η ^ (-(d : ℝ)) := by positivity
  have hKp' := text_kernel_Lp' p p' hp hpt hΨint hbη hC₁.le hΨsup hΨ1
  have hKeq : (B * η ^ (-(d : ℝ))) ^ θ * C₁ ^ (1 - θ) = K₀ * η ^ (-(d : ℝ) * θ) := by
    rw [Real.mul_rpow hB.le (by positivity), ← Real.rpow_mul hη.le, hK₀]; ring
  rw [hKeq] at hKp'
  have hΨmem : MemLp Ψ p' volume := memLp_iff.2 (lt_of_le_of_lt hKp' ENNReal.ofReal_lt_top)
  have ha1 : Integrable a := ha.integrable hp
  have hrep : a =ᵐ[volume] textConv Ψ a := by
    refine text_repro ha1 hΨint (fun k hk => ?_)
    by_contra hne
    have hle : η * Lattice.enorm k ≤ R := by
      by_contra hlt
      push Not at hlt
      exact hne (hsupp k hlt)
    apply hk
    rw [hΨcoef k]
    have : ‖R⁻¹ • η • Lattice.toEuc k‖ ≤ 1 := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hη,
        abs_of_pos (inv_pos.2 hR), ← mul_assoc, ← Lattice.enorm]
      rw [inv_mul_eq_div, div_mul_eq_mul_div, div_le_one hR]; exact hle
    rw [Whole.cmxFB_chi_one this]
    simp
  set Θ : ℝ≥0∞ := ENNReal.ofReal (K₀ * η ^ (-(d : ℝ) * θ)) with hΘ
  have hbd : ∀ᵐ x ∂(volume : Measure (Torus d)), ‖a x‖ₑ ≤ Θ * eLpNorm a p volume := by
    filter_upwards [hrep] with x hx
    rw [hx]
    exact (text_conv_enorm_le hΨmem ha x).trans (mul_le_mul' hKp' le_rfl)
  have hM : Θ * eLpNorm a p volume ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ha.eLpNorm_lt_top).ne
  have hmain : eLpNorm a q volume ≤ Θ ^ s * eLpNorm a p volume := by
    by_cases hqt : q = ⊤
    · subst hqt
      have hs' : s = 1 := by rw [hs]; simp
      rw [hs', ENNReal.rpow_one, eLpNorm_exponent_top ha.aestronglyMeasurable]
      exact eLpNormEssSup_le_of_ae_enorm_bound hbd
    · have hq' : q < ⊤ := lt_top_iff_ne_top.2 hqt
      have hq0 : 0 < q.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le (hp.trans hpq)).ne' hqt
      have h1 := text_interp (μ := (volume : Measure (Torus d))) hp hpq hq' ha hM hbd
      have hse : s = (q.toReal - p.toReal) / q.toReal := by
        rw [hs, ENNReal.toReal_inv]; field_simp
      have hη' : p.toReal / q.toReal = 1 - s := by rw [hse]; field_simp; ring
      rw [← hse, hη'] at h1
      refine h1.trans (le_of_eq ?_)
      rw [ENNReal.mul_rpow_of_nonneg _ _ hs0]
      calc Θ ^ s * eLpNorm a p volume ^ s * eLpNorm a p volume ^ (1 - s)
          = Θ ^ s * (eLpNorm a p volume ^ s * eLpNorm a p volume ^ (1 - s)) := by ring
        _ = Θ ^ s * eLpNorm a p volume := by
            rw [← ENNReal.rpow_add_of_nonneg _ _ hs0 (by linarith), add_sub_cancel, ENNReal.rpow_one]
  have hΘs : Θ ^ s = ENNReal.ofReal (K₀ ^ s * η ^ (-(d : ℝ) * ((p⁻¹).toReal - (q⁻¹).toReal))) := by
    rw [hΘ, ENNReal.ofReal_rpow_of_nonneg (by positivity) hs0,
      Real.mul_rpow hK₀pos.le (by positivity), ← Real.rpow_mul hη.le]
    congr 3
    rw [← hθ, ← hθs]; ring
  have hfin : Θ ^ s * eLpNorm a p volume < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hs0 ENNReal.ofReal_ne_top) ha.eLpNorm_lt_top
  refine ⟨memLp_iff.2 (lt_of_le_of_lt hmain hfin), hmain.trans ?_⟩
  rw [hΘs]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have : 0 < η ^ (-(d : ℝ) * ((p⁻¹).toReal - (q⁻¹).toReal)) := Real.rpow_pos_of_pos hη _
  nlinarith

end HRS.Commutator.TorusNote
