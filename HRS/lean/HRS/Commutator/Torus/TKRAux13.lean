import HRS.Commutator.Torus.TKRAux12

/-!
# T-KR helpers, part 13: `kernel_remainder_Lq_T`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.TorusNote

open HRS HRS.KernelGrad

variable {d : ℕ} {s : ℝ}

lemma tkr_ghi_measurable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd1 : s + 1 < (d : ℝ)) {η : ℝ} (hη : 0 < η) :
    Measurable (ghiForceT s η : Torus d → Euc d) := by
  have hG : Measurable (periodicRieszGrad d s : Torus d → Euc d) :=
    measurable_periodicRieszGrad (by linarith)
  have hglo : Measurable (gloForceT s η : Torus d → Euc d) := by
    have h1 : Measurable fun x : Torus d => (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm (gloForceT s η x) :=
      measurable_pi_iff.2 fun i => (tkr_glo_continuous hd hs0 hsd1 hη i).measurable
    have h2 : (gloForceT s η : Torus d → Euc d) = fun x => (MeasurableEquiv.toLp 2 (Fin d → ℝ))
        ((MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm (gloForceT s η x)) := by
      funext x; simp
    rw [h2]
    exact (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp h1
  exact hG.sub hglo

theorem tkr_kernel_remainder_Lq (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (p q : ℝ≥0∞)
    (hp : ENNReal.ofReal ((d : ℝ) / (d - s)) < p) (hpq : p⁻¹ + q⁻¹ = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 →
      MemLp (fun x : Torus d => KernelGrad.tdist x 0 * ‖ghiForceT s η x‖) q volume ∧
        eLpNorm (fun x : Torus d => KernelGrad.tdist x 0 * ‖ghiForceT s η x‖) q volume ≤
          ENNReal.ofReal (C * η ^ ((d : ℝ) * (q⁻¹).toReal - s)) := by
  have hd2 : 2 ≤ d := by omega
  have hsd1 : s + 1 < (d : ℝ) := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨C1, hC1, hrem⟩ := tkr_remainder_c hd hs0 hsd
  obtain ⟨C2, hC2, hu⟩ := tkr_u_Lq hd hs0 hsd p q hp hpq
  refine ⟨C1 * C2 + 1, by positivity, fun η hη hη1 => ?_⟩
  have hs2 : s < 2 * (d : ℝ) + 4 := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  set u : Torus d → ℝ := fun x => Whole.fTrunc s η (KernelGrad.centeredRep x) with hu_def
  have humeas : Measurable u :=
    (tpos_fTrunc_measurable (d := d) (s := s) hη).comp tkr_centeredRep_measurable
  have hWmeas : Measurable fun x : Torus d => KernelGrad.tdist x 0 * ‖ghiForceT s η x‖ := by
    have h1 : Measurable fun x : Torus d => KernelGrad.tdist x 0 := by
      have : (fun x : Torus d => KernelGrad.tdist x 0) = fun x => ‖KernelGrad.centeredRep x‖ := by
        funext x; exact KernelGrad.tdist_zero_right x
      rw [this]; exact tkr_centeredRep_measurable.norm
    exact h1.mul (tkr_ghi_measurable hd2 hs0 hsd1 hη).norm
  have hbound : ∀ᵐ x : Torus d, ‖KernelGrad.tdist x 0 * ‖ghiForceT s η x‖‖ ≤ C1 * u x := by
    filter_upwards [KernelAux.torus_ae_ne (by omega : 0 < d)] with x hx
    rw [Real.norm_of_nonneg (mul_nonneg (KernelGrad.tdist_nonneg _ _) (norm_nonneg _))]
    exact hrem η hη hη1 x hx
  have hefin : eLpNorm u q volume < ⊤ :=
    lt_of_le_of_lt (hu η hη hη1) ENNReal.ofReal_lt_top
  have hMu : MemLp u q volume := hefin
  refine ⟨(hMu.const_mul C1).mono' hWmeas.aestronglyMeasurable hbound, ?_⟩
  have hmono : eLpNorm (fun x : Torus d => KernelGrad.tdist x 0 * ‖ghiForceT s η x‖) q volume ≤
      eLpNorm (C1 • u) q volume := by
    refine eLpNorm_mono_ae hWmeas.aestronglyMeasurable ?_
    filter_upwards [hbound] with x hx
    refine hx.trans ?_
    simp only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
    exact le_abs_self _
  refine hmono.trans ?_
  rw [eLpNorm_const_smul]
  have hnorm : ‖C1‖ₑ = ENNReal.ofReal C1 := by
    rw [Real.enorm_of_nonneg hC1.le]
  rw [hnorm]
  calc ENNReal.ofReal C1 * eLpNorm u q volume ≤ ENNReal.ofReal C1 *
        ENNReal.ofReal (C2 * η ^ ((d : ℝ) * (q⁻¹).toReal - s)) :=
        by gcongr; exact hu η hη hη1
    _ = ENNReal.ofReal (C1 * (C2 * η ^ ((d : ℝ) * (q⁻¹).toReal - s))) :=
        (ENNReal.ofReal_mul hC1.le).symm
    _ ≤ ENNReal.ofReal ((C1 * C2 + 1) * η ^ ((d : ℝ) * (q⁻¹).toReal - s)) := by
        apply ENNReal.ofReal_le_ofReal
        have : 0 ≤ η ^ ((d : ℝ) * (q⁻¹).toReal - s) := Real.rpow_nonneg hη.le _
        nlinarith

end HRS.Commutator.TorusNote
