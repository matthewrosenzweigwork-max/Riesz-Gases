import HRS.Commutator.Torus.TSAMPAux3
import HRS.Commutator.Whole.LocalAuxSAMP5

/-!
# T-SAMP helpers, part 4: the periodised low-pass kernel `Ψ_η = perio ψ_{1/η}`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

lemma tsamp_mk_rep_add (x : Torus d) (l : Lattice d) :
    Torus.mk (Torus.rep x + Lattice.toEuc l) = x := by
  rw [Torus.mk_add, Torus.mk_toEuc, add_zero, Torus.mk_rep]

/-- Moment bound for a periodisation of a decaying function. -/
lemma tsamp_perio_moment {f : Euc d → ℝ} (hfm : Measurable f)
    (hsum : ∀ y : Euc d, Summable fun l : Lattice d => f (y + Lattice.toEuc l))
    (hsumG : ∀ y : Euc d, Summable fun l : Lattice d => |f (y + Lattice.toEuc l)| * ‖y + Lattice.toEuc l‖)
    (x : Torus d) :
    |perio f x| * KernelGrad.tdist x 0 ≤
      perio (fun z => |f z| * ‖z‖) x := by
  unfold perio
  set y := Torus.rep x with hy
  have h1 : |∑' l : Lattice d, f (y + Lattice.toEuc l)| ≤ ∑' l : Lattice d, |f (y + Lattice.toEuc l)| := by
    have := norm_tsum_le_tsum_norm (hsum y).norm
    simpa using this
  have h2 : ∀ l : Lattice d, KernelGrad.tdist x 0 ≤ ‖y + Lattice.toEuc l‖ := fun l => by
    have := EnergyAux.tdist_mk_le (y + Lattice.toEuc l)
    rwa [tsamp_mk_rep_add] at this
  have ht0 : 0 ≤ KernelGrad.tdist x 0 := KernelGrad.tdist_nonneg _ _
  calc |∑' l : Lattice d, f (y + Lattice.toEuc l)| * KernelGrad.tdist x 0
      ≤ (∑' l : Lattice d, |f (y + Lattice.toEuc l)|) * KernelGrad.tdist x 0 :=
        mul_le_mul_of_nonneg_right h1 ht0
    _ = ∑' l : Lattice d, |f (y + Lattice.toEuc l)| * KernelGrad.tdist x 0 := by
        rw [tsum_mul_right]
    _ ≤ ∑' l : Lattice d, |f (y + Lattice.toEuc l)| * ‖y + Lattice.toEuc l‖ :=
        Summable.tsum_le_tsum (fun l => mul_le_mul_of_nonneg_left (h2 l) (abs_nonneg _))
          ((hsum y).abs.mul_right _) (hsumG y)

theorem tsamp_psi_kernel (hd : 1 ≤ d) :
    ∃ B C₁ C₂ : ℝ, 0 < B ∧ 0 < C₁ ∧ 0 < C₂ ∧ ∀ η : ℝ, 0 < η → η ≤ 1 →
      Integrable (perio (Whole.psiL (d := d) η⁻¹) : Torus d → ℝ) ∧
      (∀ x : Torus d, x ≠ 0 → |perio (Whole.psiL (d := d) η⁻¹) x| ≤ B * η ^ (-(d : ℝ))) ∧
      (∫ x, |perio (Whole.psiL (d := d) η⁻¹) x|) ≤ C₁ ∧
      (∀ k : Lattice d, Torus.fcoef (perio (Whole.psiL (d := d) η⁻¹) : Torus d → ℝ) k =
        (((Whole.chi (η • Lattice.toEuc k)) : ℝ) : ℂ)) ∧
      (∫ x, |perio (Whole.psiL (d := d) η⁻¹) x| * KernelGrad.tdist x 0) ≤ C₂ * η := by
  classical
  obtain ⟨hcont, hint, ⟨Bs, hBs0, hBs⟩, hdec, hft⟩ := text_psiL_props (d := d) 1 one_pos
  choose A hA using hdec
  set ψ : Euc d → ℝ := Whole.psiL (d := d) 1 with hψ
  obtain ⟨C, hC, Cm, hCm, hmain⟩ := tsamp_gk hd 0 0 le_rfl (by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith) le_rfl (Kt := ψ) hcont.measurable hint (C₀ := Bs + 1) (by linarith)
    (fun x _ _ => by
      rw [Real.rpow_zero, mul_one]; linarith [hBs x])
    (fun m => A m + 1) (fun m => by linarith [(hA m).1])
    (fun m x hx => by
      have hx0 : x ≠ 0 := by
        intro h; rw [h, norm_zero] at hx; linarith
      have := (hA m).2 x hx0
      nlinarith [Real.rpow_nonneg (norm_nonneg x) (-(m : ℝ))])
  have hmom := Whole.SAMP1.psi_moment (d := d) 1
  set I₂ : ℝ := ∫ y : Euc d, ‖y‖ ^ 1 * |ψ y| with hI₂
  have hI₂0 : 0 ≤ I₂ := integral_nonneg fun y => by positivity
  set I₁ : ℝ := ∫ y : Euc d, ‖ψ y‖ with hI₁
  have hI₁0 : 0 ≤ I₁ := integral_nonneg fun y => norm_nonneg _
  refine ⟨max C (Cm 0), I₁ + 1, I₂ + 1, lt_max_of_lt_left hC, by linarith, by linarith, ?_⟩
  intro η hη hη1
  obtain ⟨hΨint, hcoef, hnear, hfar, hL1⟩ := hmain η hη hη1
  have e : textKeta ψ 0 η = Whole.psiL (d := d) η⁻¹ := (tsamp_psi_scale hη).symm
  rw [e] at hΨint hcoef hnear hfar hL1
  have hΨm : AEStronglyMeasurable (perio (Whole.psiL (d := d) η⁻¹) : Torus d → ℝ) volume :=
    hΨint.1
  refine ⟨hΨint, ?_, ?_, ?_, ?_⟩
  · intro x hx
    by_cases h1 : KernelGrad.tdist x 0 ≤ η
    · have := hnear x hx h1
      simp only [zero_sub, sub_zero, Real.rpow_zero, mul_one] at this
      refine this.trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_pos_of_pos hη _).le
    · push Not at h1
      have := hfar 0 x h1.le
      simp only [Nat.cast_zero, add_zero, zero_sub, neg_zero, Real.rpow_zero, mul_one] at this
      refine this.trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_pos_of_pos hη _).le
  · have h1 : ∫⁻ x, ‖perio (Whole.psiL (d := d) η⁻¹) x‖ₑ ≤ ENNReal.ofReal I₁ := by
      simpa [hI₁] using hL1
    have h2 : (∫ x, |perio (Whole.psiL (d := d) η⁻¹) x|) =
        (∫⁻ x, ‖perio (Whole.psiL (d := d) η⁻¹) x‖ₑ).toReal := by
      rw [← integral_norm_eq_lintegral_enorm hΨm]
      simp
    rw [h2]
    have h3 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rw [ENNReal.toReal_ofReal hI₁0] at h3
    linarith
  · intro k
    rw [hcoef k, hft]
    simp
  · -- the first moment
    rw [← e]
    set f : Euc d → ℝ := textKeta ψ 0 η with hf
    have hfm : Measurable f := text_Keta_measurable hcont.measurable 0 η
    have hfint : Integrable f := text_Keta_integrable hint hη 0
    have hfb : ∀ z : Euc d, z ≠ 0 →
        |f z| ≤ (A (d + 2) * η ^ ((0 : ℝ) - d + ((d + 2 : ℕ) : ℝ))) * ‖z‖ ^ (-((d + 2 : ℕ) : ℝ)) :=
      text_Keta_bound hη (hA (d + 2)).1 (hA (d + 2)).2
    have hsum : ∀ y : Euc d, Summable fun l : Lattice d => f (y + Lattice.toEuc l) := by
      intro y
      refine tpos_summable_shift (C := A (d + 2) * η ^ ((0 : ℝ) - d + ((d + 2 : ℕ) : ℝ)))
        (r := ((d + 2 : ℕ) : ℝ)) (by have := (hA (d + 2)).1; positivity) ?_ hfb y
      push_cast; linarith
    set G : Euc d → ℝ := fun z => |f z| * ‖z‖ with hG
    have hGm : Measurable G := hfm.abs.mul measurable_norm
    have hGb : ∀ z : Euc d, z ≠ 0 →
        |G z| ≤ (A (d + 2) * η ^ ((0 : ℝ) - d + ((d + 2 : ℕ) : ℝ))) * ‖z‖ ^ (-((d + 1 : ℕ) : ℝ)) := by
      intro z hz
      have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
      have h1 := hfb z hz
      have h2 : |G z| = |f z| * ‖z‖ := by
        simp only [hG, abs_mul, abs_abs, abs_norm]
      rw [h2]
      calc |f z| * ‖z‖ ≤ ((A (d + 2) * η ^ ((0 : ℝ) - d + ((d + 2 : ℕ) : ℝ))) *
            ‖z‖ ^ (-((d + 2 : ℕ) : ℝ))) * ‖z‖ := mul_le_mul_of_nonneg_right h1 hzpos.le
        _ = (A (d + 2) * η ^ ((0 : ℝ) - d + ((d + 2 : ℕ) : ℝ))) * ‖z‖ ^ (-((d + 1 : ℕ) : ℝ)) := by
            rw [mul_assoc]
            congr 1
            rw [show -((d + 1 : ℕ) : ℝ) = -((d + 2 : ℕ) : ℝ) + 1 by push_cast; ring,
              Real.rpow_add hzpos, Real.rpow_one]
    have hsumG : ∀ y : Euc d, Summable fun l : Lattice d => G (y + Lattice.toEuc l) := by
      intro y
      refine tpos_summable_shift (C := A (d + 2) * η ^ ((0 : ℝ) - d + ((d + 2 : ℕ) : ℝ)))
        (r := ((d + 1 : ℕ) : ℝ)) (by have := (hA (d + 2)).1; positivity) ?_ hGb y
      push_cast; linarith
    have hGnn : ∀ z, 0 ≤ G z := fun z => mul_nonneg (abs_nonneg _) (norm_nonneg _)
    have hGeq : ∀ y : Euc d, G y =
        η ^ (-(d : ℝ)) * ((fun u : Euc d => (η * ‖u‖ ^ 1) * |ψ u|) (η⁻¹ • y)) := by
      intro y
      simp only [hG, hf, textKeta, zero_sub, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hη _)]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hη)]
      field_simp
    have hg : Integrable (fun u : Euc d => (η * ‖u‖ ^ 1) * |ψ u|) := by
      have := hmom.const_mul η
      refine this.congr (Eventually.of_forall fun u => ?_)
      simp only [mul_assoc]
      rfl
    have hGint : Integrable G := by
      have h1 := (hg.comp_smul (inv_ne_zero hη.ne')).const_mul (η ^ (-(d : ℝ)))
      exact h1.congr (Eventually.of_forall fun y => (hGeq y).symm)
    have hGval : ∫ y, G y = η * I₂ := by
      simp_rw [hGeq]
      rw [integral_const_mul, MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg
        (μ := (volume : Measure (Euc d))) (fun u : Euc d => (η * ‖u‖ ^ 1) * |ψ u|) hη.le,
        finrank_euclideanSpace_fin, smul_eq_mul, ← mul_assoc, Real.rpow_neg hη.le,
        Real.rpow_natCast, inv_mul_cancel₀ (by positivity), one_mul, hI₂]
      simp_rw [mul_assoc]
      rw [integral_const_mul]
    have hPG : Integrable (perio G : Torus d → ℝ) := tpos_integrable_perio hGm hGint hGnn hsumG
    have hbd : ∀ x : Torus d, |perio f x| * KernelGrad.tdist x 0 ≤ perio G x :=
      fun x => tsamp_perio_moment hfm hsum hsumG x
    have hΦm : AEStronglyMeasurable
        (fun x : Torus d => |perio f x| * KernelGrad.tdist x 0) volume :=
      (((tpos_perio_measurable hfm).aestronglyMeasurable.norm).mul
        (tsamp_measurable_tdist 0).aestronglyMeasurable).congr
        (Eventually.of_forall fun x => by simp)
    have hle : ∫ x, |perio f x| * KernelGrad.tdist x 0 ≤ ∫ x, perio G x := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun x => by
        have := KernelGrad.tdist_nonneg x 0; positivity) hPG (Eventually.of_forall hbd)
    rw [tpos_integral_perio hGm hGint hsumG, hGval] at hle
    have : η * I₂ ≤ (I₂ + 1) * η := by nlinarith
    exact hle.trans this

end HRS.Commutator.TorusNote
