import HRS.Commutator.Torus.TEXTAux15

/-!
# T-EXT-A helpers, part 16: the kernel `Ψ_η = perio (η^{-d} ψ_R(·/η))`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

lemma text_bern_kernel (hd : 1 ≤ d) (R : ℝ) (hR : 0 < R) :
    ∃ B C₁ : ℝ, 0 < B ∧ 0 < C₁ ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ Ψ : Torus d → ℝ,
      Integrable Ψ ∧ (∀ x, |Ψ x| ≤ B * η ^ (-(d : ℝ))) ∧
      eLpNorm Ψ 1 volume ≤ ENNReal.ofReal C₁ ∧
      ∀ k : Lattice d, Torus.fcoef Ψ k = ((Whole.chi (R⁻¹ • η • Lattice.toEuc k) : ℝ) : ℂ) := by
  obtain ⟨hcont, hint, ⟨Bs, hBs0, hBs⟩, hdec, hft⟩ := text_psiL_props (d := d) R hR
  set ψ : Euc d → ℝ := Whole.psiL (d := d) R with hψ
  obtain ⟨A, hA0, hA⟩ := hdec (d + 1)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set S : ℝ := ∑' m : Lattice d, ‖Lattice.toEuc m‖ ^ (-((d + 1 : ℕ) : ℝ)) with hS
  have hSnn : 0 ≤ S := tsum_nonneg fun l => by positivity
  have hI0 : 0 ≤ ∫ x, ‖ψ x‖ :=
    integral_nonneg (μ := (volume : Measure (Euc d))) (f := fun x : Euc d => ‖ψ x‖)
      (fun x => norm_nonneg _)
  refine ⟨Bs + A * ((2 * d) ^ (d + 1) * S) + 1, (∫ x, ‖ψ x‖) + 1, by positivity,
    by linarith, ?_⟩
  intro η hη hη1
  set f : Euc d → ℝ := textKeta ψ 0 η with hf
  have hfm : Measurable f := text_Keta_measurable hcont.measurable 0 η
  have hfint : Integrable f := text_Keta_integrable hint hη 0
  have hfb : ∀ z : Euc d, z ≠ 0 →
      |f z| ≤ (A * η ^ ((0 : ℝ) - d + ((d + 1 : ℕ) : ℝ))) * ‖z‖ ^ (-((d + 1 : ℕ) : ℝ)) :=
    text_Keta_bound hη hA0 hA
  have hsum : ∀ y : Euc d, Summable fun l : Lattice d => f (y + Lattice.toEuc l) := by
    intro y
    refine tpos_summable_shift (C := A * η ^ ((0 : ℝ) - d + ((d + 1 : ℕ) : ℝ)))
      (r := ((d + 1 : ℕ) : ℝ)) (by positivity) ?_ hfb y
    push_cast; linarith
  have hsum' : ∀ y : Euc d, Summable fun l : Lattice d => (fun z => |f z|) (y + Lattice.toEuc l) :=
    fun y => (hsum y).abs
  refine ⟨perio f, text_integrable_perio_signed hfm hfint hsum, ?_, ?_, ?_⟩
  · intro x
    set c := KernelGrad.centeredRep x with hcdef
    have hc : ∀ i, |c i| ≤ 1 / 2 := KernelGrad.abs_centeredRep_le x
    have hx : perio f x = perio f (Torus.mk c) := by rw [hcdef, KernelGrad.mk_centeredRep]
    rw [hx]
    have h1 := text_perio_bound hd (f := f) (T := A * η ^ ((0 : ℝ) - d + ((d + 1 : ℕ) : ℝ)))
      (M := d + 1) (by positivity) (by omega) hfb c hc
    have h2 : |f c| ≤ Bs * η ^ (-(d : ℝ)) := by
      simp only [hf, textKeta, zero_sub]
      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hη _)]
      calc η ^ (-(d : ℝ)) * |ψ (η⁻¹ • c)| ≤ η ^ (-(d : ℝ)) * Bs :=
            mul_le_mul_of_nonneg_left (hBs _) (Real.rpow_pos_of_pos hη _).le
        _ = Bs * η ^ (-(d : ℝ)) := by ring
    have h3 : η ^ ((0 : ℝ) - d + ((d + 1 : ℕ) : ℝ)) ≤ η ^ (-(d : ℝ)) := by
      rw [zero_sub]
      refine Real.rpow_le_rpow_of_exponent_ge hη hη1 ?_
      have : (0 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    calc |perio f (Torus.mk c)| ≤ |f c| + (A * η ^ ((0 : ℝ) - d + ((d + 1 : ℕ) : ℝ))) *
          ((2 * d) ^ (d + 1) * S) := h1
      _ ≤ Bs * η ^ (-(d : ℝ)) + (A * η ^ (-(d : ℝ))) * ((2 * d) ^ (d + 1) * S) := by
          refine add_le_add h2 ?_
          have : 0 ≤ (2 * (d : ℝ)) ^ (d + 1) * S := by positivity
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hA0) this
      _ ≤ (Bs + A * ((2 * d) ^ (d + 1) * S) + 1) * η ^ (-(d : ℝ)) := by
          have : 0 < η ^ (-(d : ℝ)) := Real.rpow_pos_of_pos hη _
          nlinarith
  · have hPm : AEStronglyMeasurable (perio f : Torus d → ℝ) volume :=
      (tpos_perio_measurable hfm).aestronglyMeasurable
    rw [eLpNorm_one_eq_lintegral_enorm hPm]
    have hfn : ∫ y, ‖f y‖ = ∫ x, ‖ψ x‖ := by
      have h1 : ∀ y : Euc d, ‖f y‖ = η ^ (-(d : ℝ)) * ‖ψ (η⁻¹ • y)‖ := fun y => by
        simp only [hf, textKeta, zero_sub, norm_mul, Real.norm_eq_abs,
          abs_of_pos (Real.rpow_pos_of_pos hη _)]
      simp_rw [h1]
      rw [integral_const_mul, MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg
        (μ := (volume : Measure (Euc d))) (fun x : Euc d => ‖ψ x‖) hη.le,
        finrank_euclideanSpace_fin, smul_eq_mul, ← mul_assoc, Real.rpow_neg hη.le,
        Real.rpow_natCast, inv_mul_cancel₀ (by positivity), one_mul]
    calc ∫⁻ x, ‖perio f x‖ₑ ≤ ∫⁻ x, ENNReal.ofReal (perio (fun z => |f z|) x) := by
          refine lintegral_mono fun x => ?_
          rw [Real.enorm_eq_ofReal_abs]
          refine ENNReal.ofReal_le_ofReal ?_
          unfold perio
          exact (norm_tsum_le_tsum_norm (hsum _).norm).trans (le_of_eq (by simp))
      _ = ∫⁻ y, ENNReal.ofReal |f y| :=
          tpos_lintegral_perio hfm.abs (fun z => abs_nonneg _) hsum'
      _ = ENNReal.ofReal (∫ y, ‖f y‖) := by
          rw [ofReal_integral_norm_eq_lintegral_enorm hfint]
          refine lintegral_congr fun y => ?_
          rw [Real.enorm_eq_ofReal_abs]
      _ ≤ ENNReal.ofReal ((∫ x, ‖ψ x‖) + 1) := by
          rw [hfn]; exact ENNReal.ofReal_le_ofReal (by linarith)
  · intro k
    rw [tpos_fcoef_perio hfm hfint hsum k, hf, text_fourier_Keta hη ψ 0, hft]
    simp only [Real.rpow_zero, Complex.ofReal_one, one_mul]

end HRS.Commutator.TorusNote
