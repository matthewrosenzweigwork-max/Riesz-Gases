import HRS.Commutator.Whole.LOWVAux1
import HRS.Commutator.Whole.LocalAuxKR3
import HRS.Commutator.Whole.Local

/-!
# CMX-LOWV auxiliary 2: Fourier support of `∇g_{≤1}`

`gloForce s = ψ_1 * ∇g` has components with Fourier support in `B̄(0,2)` (the singular analogue of
`Pleq_fourierSupp`).  Names prefixed `lowv_`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

/-- Integrability of `(x,y) ↦ ‖Ψ(x-y)‖ ‖K y‖ ‖φ x‖` for a kernel `K` locally integrable and bounded
at infinity and Schwartz `Ψ, φ`. -/
theorem lowv_sing_integrable {K : Euc d → Euc d} (hK : cmxFB_KerOK K)
    (Ψ φ : SchwartzMap (Euc d) ℂ) :
    Integrable (fun p : Euc d × Euc d => ‖Ψ (p.1 - p.2)‖ * ‖K p.2‖ * ‖φ p.1‖)
      (volume.prod volume) := by
  obtain ⟨CΨ, hCΨ0, hCΨ⟩ := cmxFB_schwartz_a Ψ
  obtain ⟨c2, hc2⟩ := cmxFB_dom hK (fun z => Ψ z) CΨ hCΨ0 hCΨ
  have hmeas : AEStronglyMeasurable
      (fun p : Euc d × Euc d => ‖Ψ (p.1 - p.2)‖ * ‖K p.2‖ * ‖φ p.1‖) (volume.prod volume) := by
    have h1 : Continuous fun p : Euc d × Euc d => ‖Ψ (p.1 - p.2)‖ :=
      (Ψ.continuous.comp (continuous_fst.sub continuous_snd)).norm
    have h2 : AEStronglyMeasurable (fun p : Euc d × Euc d => ‖K p.2‖) (volume.prod volume) :=
      (hK.meas.norm).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have h3 : Continuous fun p : Euc d × Euc d => ‖φ p.1‖ :=
      (φ.continuous.comp continuous_fst).norm
    exact (h1.aestronglyMeasurable.mul h2).mul h3.aestronglyMeasurable
  have hinner : ∀ x : Euc d, ∫ y, ‖‖Ψ (x - y)‖ * ‖K y‖ * ‖φ x‖‖ ≤
      ‖φ x‖ * (CΨ * (∫ y in ball (0 : Euc d) 1, ‖K y‖) + c2 * (∫ y, cmxFB_a d y)) := by
    intro x
    have hb := cmxFB_bd_integrable hK CΨ c2 x
    calc ∫ y, ‖‖Ψ (x - y)‖ * ‖K y‖ * ‖φ x‖‖ ≤ ∫ y, ‖φ x‖ * cmxFB_bd K CΨ c2 x y := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _)
            (hb.const_mul _) (Eventually.of_forall fun y => ?_)
          show ‖‖Ψ (x - y)‖ * ‖K y‖ * ‖φ x‖‖ ≤ ‖φ x‖ * cmxFB_bd K CΨ c2 x y
          rw [Real.norm_of_nonneg (by positivity)]
          have := hc2 x x (by simp) y
          calc ‖Ψ (x - y)‖ * ‖K y‖ * ‖φ x‖ = ‖φ x‖ * (‖Ψ (x - y)‖ * ‖K y‖) := by ring
            _ ≤ ‖φ x‖ * cmxFB_bd K CΨ c2 x y := by gcongr
      _ = _ := by rw [integral_const_mul, cmxFB_bd_integral hK]
  rw [integrable_prod_iff hmeas]
  refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
  · have hb := cmxFB_bd_integrable hK CΨ c2 x
    refine (hb.const_mul ‖φ x‖).mono' ?_ (Eventually.of_forall fun y => ?_)
    · have h1 : Continuous fun y : Euc d => ‖Ψ (x - y)‖ :=
        (Ψ.continuous.comp (continuous_const.sub continuous_id)).norm
      have h2 : AEStronglyMeasurable (fun y => ‖Ψ (x - y)‖ * ‖K y‖ * ‖φ x‖) volume :=
        (h1.aestronglyMeasurable.mul hK.meas.norm).mul_const _
      exact h2
    · show ‖‖Ψ (x - y)‖ * ‖K y‖ * ‖φ x‖‖ ≤ ‖φ x‖ * cmxFB_bd K CΨ c2 x y
      rw [Real.norm_of_nonneg (by positivity)]
      have := hc2 x x (by simp) y
      calc ‖Ψ (x - y)‖ * ‖K y‖ * ‖φ x‖ = ‖φ x‖ * (‖Ψ (x - y)‖ * ‖K y‖) := by ring
        _ ≤ ‖φ x‖ * cmxFB_bd K CΨ c2 x y := by gcongr
  · refine ((φ.integrable (μ := (volume : Measure (Euc d)))).norm.mul_const
      (CΨ * (∫ y in ball (0 : Euc d) 1, ‖K y‖) + c2 * (∫ y, cmxFB_a d y))).mono' ?_
      (Eventually.of_forall fun x => ?_)
    · exact hmeas.norm.integral_prod_right'
    · rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
      exact hinner x


theorem lowv_gloForce_comp (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (x : Euc d)
    (i : Fin d) :
    ((gloForce s x i : ℝ) : ℂ) =
      ∫ y, cmxFB_Om (d := d) 1 one_pos (x - y) * ((kernGrad s y i : ℝ) : ℂ) := by
  have hK := cmxFB_kerOK hd hs0 hsd
  have hint := cmxFB_Phi_integrable hK (cmxFB_B0 d) (cmxFB_Om (d := d) 1 one_pos) x
  have h1 : gloForce s x i = ∫ y, (cmxFB_Om (d := d) 1 one_pos (x - y)).re * kernGrad s y i := by
    rw [cmxFB_gloForce_eq]
    unfold cmxFB_Phi
    have := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).integral_comp_comm hint
    simpa [cmxFB_B0_apply] using this.symm
  rw [h1, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [cmxFB_Om_apply one_pos]
  simp

theorem lowv_gloForce_fsupp (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (i : Fin d) :
    FourierSuppIn 2 (fun x : Euc d => gloForce s x i) := by
  refine lowv_fs_of (by norm_num) fun φ r hr hz => ?_
  have hK := cmxFB_kerOK hd hs0 hsd
  set Ψ := cmxFB_Om (d := d) 1 one_pos with hΨdef
  have hΨ : ∀ z, Ψ z = ((psiL 1 z : ℝ) : ℂ) := cmxFB_Om_apply one_pos
  have hΨeven : ∀ z, Ψ (-z) = Ψ z := fun z => by rw [hΨ, hΨ, cmxFB_psiL_neg]
  have hint : Integrable (fun p : Euc d × Euc d =>
      Ψ (p.1 - p.2) * ((kernGrad s p.2 i : ℝ) : ℂ) * φ p.1) (volume.prod volume) := by
    refine (lowv_sing_integrable hK Ψ φ).mono' ?_ (Eventually.of_forall fun p => ?_)
    · have h1 : Continuous fun p : Euc d × Euc d => Ψ (p.1 - p.2) :=
        Ψ.continuous.comp (continuous_fst.sub continuous_snd)
      have h2 : AEStronglyMeasurable (fun p : Euc d × Euc d => ((kernGrad s p.2 i : ℝ) : ℂ))
          (volume.prod volume) := by
        have : AEStronglyMeasurable (fun y : Euc d => ((kernGrad s y i : ℝ) : ℂ)) volume :=
          (Complex.continuous_ofReal.comp_aestronglyMeasurable
            ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hK.meas))
        exact this.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
      have h3 : Continuous fun p : Euc d × Euc d => φ p.1 := φ.continuous.comp continuous_fst
      exact (h1.aestronglyMeasurable.mul h2).mul h3.aestronglyMeasurable
    · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      gcongr
      simpa using PiLp.norm_apply_le (kernGrad s p.2) i
  have h2 : ∀ x, ((gloForce s x i : ℝ) : ℂ) * φ x =
      ∫ y, Ψ (x - y) * ((kernGrad s y i : ℝ) : ℂ) * φ x := by
    intro x
    rw [lowv_gloForce_comp hd hs0 hsd x i, ← integral_mul_const]
  simp_rw [h2]
  rw [integral_integral_swap hint]
  have h3 : ∀ y, ∫ x, Ψ (x - y) * ((kernGrad s y i : ℝ) : ℂ) * φ x = 0 := by
    intro y
    have h4 : ∫ x, φ x * Ψ (y - x) = 0 := by
      refine cmxFB_conv_zero one_pos φ (fun ξ hξ => ?_) y
      have := hz ξ (by linarith)
      rwa [← SchwartzMap.fourier_coe] at this
    have h5 : ∀ x, Ψ (x - y) * ((kernGrad s y i : ℝ) : ℂ) * φ x =
        ((kernGrad s y i : ℝ) : ℂ) * (φ x * Ψ (y - x)) := by
      intro x
      rw [← hΨeven (x - y), neg_sub]
      ring
    simp_rw [h5]
    rw [integral_const_mul, h4, mul_zero]
  simp [h3]

end HRS.Commutator.Whole
