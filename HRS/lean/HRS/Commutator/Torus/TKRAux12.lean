import HRS.Commutator.Torus.TKRAux11

/-!
# T-KR helpers, part 12: `‖f_η(centeredRep ·)‖_{L^q(𝕋^d)} ≲ η^{d/q-s}`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.TorusNote

open HRS HRS.KernelGrad

variable {d : ℕ} {s : ℝ}

theorem tkr_u_Lq (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (p q : ℝ≥0∞)
    (hp : ENNReal.ofReal ((d : ℝ) / (d - s)) < p) (hpq : p⁻¹ + q⁻¹ = 1) :
    ∃ C2 : ℝ, 0 ≤ C2 ∧ ∀ η : ℝ, 0 < η → η ≤ 1 →
      eLpNorm (fun x : Torus d => Whole.fTrunc s η (KernelGrad.centeredRep x)) q volume ≤
        ENNReal.ofReal (C2 * η ^ ((d : ℝ) * (q⁻¹).toReal - s)) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hs2 : s < 2 * (d : ℝ) + 4 := by linarith
  obtain ⟨hqtop, hq1⟩ := tkr_q_props hd hs0 hsd p q hp hpq
  set qr : ℝ := q.toReal with hqr
  have hqr0 : 0 < qr := by linarith
  have hq0 : q ≠ 0 := by
    intro h; rw [h] at hqr; simp at hqr; linarith
  have hg : MemLp (Whole.fTrunc s 1 : Euc d → ℝ) q volume := Whole.fTrunc_Lq hd hs0 hsd p q hp hpq
  have hgi : Integrable (fun z : Euc d => (Whole.fTrunc s 1 z) ^ qr) := by
    have := hg.integrable_norm_rpow hq0 hqtop
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only
    rw [Real.norm_of_nonneg (tpos_fTrunc_nonneg hs0 hs2 1 z)]
  set Iq : ℝ := ∫ z : Euc d, (Whole.fTrunc s 1 z) ^ qr with hIq
  have hIq0 : 0 ≤ Iq := integral_nonneg fun z => Real.rpow_nonneg (tpos_fTrunc_nonneg hs0 hs2 1 z) _
  refine ⟨Iq ^ (1 / qr), Real.rpow_nonneg hIq0 _, fun η hη hη1 => ?_⟩
  set h : Euc d → ℝ := fun z => (Whole.fTrunc s η z) ^ qr with hh
  have hnn : ∀ z, 0 ≤ h z := fun z => Real.rpow_nonneg (tpos_fTrunc_nonneg hs0 hs2 η z) _
  have hmeas : Measurable h := (tpos_fTrunc_measurable (d := d) (s := s) hη).pow_const _
  have hh_eq : ∀ z : Euc d, h z = η ^ (-s * qr) * (Whole.fTrunc s 1 (η⁻¹ • z)) ^ qr := by
    intro z
    simp only [hh]
    rw [tpos_fTrunc_scale hη z, Real.mul_rpow (Real.rpow_nonneg hη.le _)
      (tpos_fTrunc_nonneg hs0 hs2 1 _), ← Real.rpow_mul hη.le]
  have hhi : Integrable h := by
    have := (hgi.comp_smul (inv_ne_zero hη.ne')).const_mul (η ^ (-s * qr))
    exact this.congr (Eventually.of_forall fun z => (hh_eq z).symm)
  have hhint : ∫ z, h z = η ^ (-s * qr) * (η ^ d * Iq) := by
    simp_rw [hh_eq]
    rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume
      (fun x : Euc d => (Whole.fTrunc s 1 x) ^ qr) hη.le]
    simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
    rfl
  -- summability of the shifts of `h`
  have hsum : ∀ y : Euc d, Summable fun m : Lattice d => h (y + Lattice.toEuc m) := by
    intro y
    have hcp := Whole.cPhi_pos d hs0 hs2
    have h2 : (0 : ℝ) < 2 * (d : ℝ) + 4 - s := by linarith
    set A : ℝ := Whole.cPhi d s / (2 * (d : ℝ) + 4 - s) * η ^ (2 * (d : ℝ) + 4 - s) with hA
    have hA0 : 0 ≤ A := by positivity
    refine tpos_summable_shift (h := h) (C := A ^ qr) (r := (2 * (d : ℝ) + 4) * qr)
      (Real.rpow_nonneg hA0 _) ?_ ?_ y
    · have : (2 * (d : ℝ) + 4) * qr ≥ 2 * (d : ℝ) + 4 := by nlinarith
      linarith
    · intro z hz
      rw [abs_of_nonneg (hnn z)]
      have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
      have h1 := tpos_fTrunc_le (d := d) hs0 hs2 hη hz
      calc h z = (Whole.fTrunc s η z) ^ qr := rfl
        _ ≤ (A * ‖z‖ ^ (-(2 * (d : ℝ) + 4))) ^ qr :=
            Real.rpow_le_rpow (tpos_fTrunc_nonneg hs0 hs2 η z) h1 hqr0.le
        _ = A ^ qr * ‖z‖ ^ (-((2 * (d : ℝ) + 4) * qr)) := by
            rw [Real.mul_rpow hA0 (Real.rpow_nonneg hzn.le _), ← Real.rpow_mul hzn.le]
            congr 2; ring
  have hle := tkr_lintegral_centered hmeas hnn hsum
  rw [← ofReal_integral_eq_lintegral_ofReal hhi (Eventually.of_forall hnn), hhint] at hle
  have hu : Measurable fun x : Torus d => Whole.fTrunc s η (KernelGrad.centeredRep x) :=
    (tpos_fTrunc_measurable (d := d) (s := s) hη).comp tkr_centeredRep_measurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqtop hu.aestronglyMeasurable]
  have hconv : ∀ x : Torus d, ‖Whole.fTrunc s η (KernelGrad.centeredRep x)‖ₑ ^ qr =
      ENNReal.ofReal (h (KernelGrad.centeredRep x)) := by
    intro x
    rw [Real.enorm_of_nonneg (tpos_fTrunc_nonneg hs0 hs2 η _),
      ENNReal.ofReal_rpow_of_nonneg (tpos_fTrunc_nonneg hs0 hs2 η _) hqr0.le]
  have hL : (∫⁻ x : Torus d, ‖Whole.fTrunc s η (KernelGrad.centeredRep x)‖ₑ ^ qr) =
      ∫⁻ x : Torus d, ENNReal.ofReal (h (KernelGrad.centeredRep x)) := lintegral_congr hconv
  beta_reduce
  rw [hL]
  have hrhs : 0 ≤ η ^ (-s * qr) * (η ^ d * Iq) := by positivity
  have hinv : (q⁻¹).toReal = 1 / qr := by rw [ENNReal.toReal_inv]; simp [hqr]
  calc (∫⁻ x : Torus d, ENNReal.ofReal (h (KernelGrad.centeredRep x))) ^ (1 / qr)
      ≤ (ENNReal.ofReal (η ^ (-s * qr) * (η ^ d * Iq))) ^ (1 / qr) :=
        ENNReal.rpow_le_rpow hle (by positivity)
    _ = ENNReal.ofReal ((η ^ (-s * qr) * (η ^ d * Iq)) ^ (1 / qr)) :=
        ENNReal.ofReal_rpow_of_nonneg hrhs (by positivity)
    _ = ENNReal.ofReal (Iq ^ (1 / qr) * η ^ ((d : ℝ) * (q⁻¹).toReal - s)) := by
        congr 1
        rw [hinv, show η ^ (-s * qr) * (η ^ d * Iq) = (η ^ (-s * qr) * η ^ d) * Iq by ring,
          Real.mul_rpow (by positivity) hIq0]
        have e1 : η ^ (-s * qr) * η ^ d = η ^ ((d : ℝ) - s * qr) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hη]; congr 1; ring
        rw [e1, ← Real.rpow_mul hη.le]
        have e2 : ((d : ℝ) - s * qr) * (1 / qr) = (d : ℝ) * (1 / qr) - s := by
          field_simp
        rw [e2, mul_comm]

end HRS.Commutator.TorusNote
