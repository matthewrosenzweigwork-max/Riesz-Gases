import HRS.MS.ThmFixAux2
import HRS.MS.PsdAux1

/-!
# THM-5 (part 1): the abstract setting for `thermalDensity_spec` and the translation `F = G + β⁻¹ log c_γ`

* `t5K d s := fun x y => rieszKernel d s (x - y)`, `r = γ = gaussianComparison d a β`, `V = confinement a`.
* `t5_setting`: for `0 < s < d`, `1 ≤ d`, `a, β > 0`, there is `B` with `ThmSetting (t5K d s) γ B`
  (K1 from `riesz_conv_gaussian_bound`, K2 from `HRS.MS.Psd.riesz_energy_nonneg`).
* `freeEnergy_eq_Gfun_add`: on probability densities with `HasFiniteFreeEnergy`,
  `freeEnergy g V β ρ = Gfun g γ β ρ + β⁻¹ log c_γ` (the `log(ρ/γ) = log ρ - log c_γ + βV` identity, also at `ρ = 0`).
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Thm

open HRS.Whole

variable {d : ℕ}

/-- The Riesz interaction kernel in the two-variable form used by `ThmSetting`. -/
abbrev t5K (d : ℕ) (s : ℝ) : Euc d → Euc d → ℝ := fun x y => rieszKernel d s (x - y)

/-- The normalising constant `c_γ = (βa/2π)^{d/2}` of the Gaussian comparison density. -/
def t5c (d : ℕ) (a β : ℝ) : ℝ := (β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2)

lemma t5c_pos {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) : 0 < t5c d a β := by
  unfold t5c
  have : 0 < β * a / (2 * Real.pi) := by positivity
  positivity

lemma t5_gamma_eq (a β : ℝ) (x : Euc d) :
    gaussianComparison d a β x = t5c d a β * Real.exp (-β * confinement a x) := by
  rw [gaussianComparison_eq]
  unfold t5c confinement
  have : -(β * a / 2) * ‖x‖ ^ 2 = -β * (a * ‖x‖ ^ 2 / 2) := by ring
  rw [this]

lemma t5_log_gamma {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (x : Euc d) :
    Real.log (gaussianComparison d a β x) = Real.log (t5c d a β) - β * confinement a x := by
  rw [t5_gamma_eq, Real.log_mul (t5c_pos ha hβ).ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

/-! ### The setting -/

lemma t5_abs_to_integrable {s : ℝ} (hs : s ≠ 0) {f : Euc d → ℝ} (hf : Integrable f)
    (habs : Integrable (fun p : Euc d × Euc d => |t5K d s p.1 p.2 * f p.1 * f p.2|)
      ((volume : Measure (Euc d)).prod volume)) :
    Integrable (fun p : Euc d × Euc d => rieszKernel d s (p.1 - p.2) * (f p.1 * f p.2))
      ((volume : Measure (Euc d)).prod volume) := by
  have hK := t012_rieszK_measurable (d := d) hs
  have h1 : AEStronglyMeasurable (fun p : Euc d × Euc d => f p.1)
      ((volume : Measure (Euc d)).prod volume) :=
    hf.aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure (Euc d)))
        (ν := (volume : Measure (Euc d))))
  have h2 : AEStronglyMeasurable (fun p : Euc d × Euc d => f p.2)
      ((volume : Measure (Euc d)).prod volume) :=
    hf.aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Euc d)))
        (ν := (volume : Measure (Euc d))))
  have hm : AEStronglyMeasurable
      (fun p : Euc d × Euc d => rieszKernel d s (p.1 - p.2) * (f p.1 * f p.2))
      ((volume : Measure (Euc d)).prod volume) :=
    hK.aestronglyMeasurable.mul (h1.mul h2)
  refine (integrable_norm_iff hm).1 ?_
  refine habs.congr (ae_of_all _ fun p => ?_)
  simp only [Real.norm_eq_abs, mul_assoc]

/-- The abstract setting of THM-0..4 for the Riesz kernel `0 < s < d` and the Gaussian comparison density. -/
theorem t5_setting (hd : 1 ≤ d) {s a β : ℝ} (hs0 : 0 < s) (hsd : s < d) (ha : 0 < a)
    (hβ : 0 < β) :
    ∃ B : ℝ, ThmSetting (t5K d s) (gaussianComparison d a β) B := by
  obtain ⟨B, hB⟩ := riesz_conv_gaussian_bound (d := d) hd hs0 hsd ha hβ
  refine ⟨B, ?_⟩
  exact
    { meas := t012_rieszK_measurable hs0.ne'
      symm := fun x y => by
        simp only [t5K]
        rw [← HRS.MS.Psd.psd1_K_symm hs0 (x - y), neg_sub]
      nonneg := fun x y => t012_rieszK_nonneg hs0.ne' x y
      r_prob := gaussianComparison_isProbDensity ha hβ
      r_pos := gaussianComparison_pos ha hβ
      k1 := hB
      k2 := fun f hf habs hint => by
        exact HRS.MS.Psd.riesz_energy_nonneg hd hs0 hf (t5_abs_to_integrable hs0.ne' hf habs) }

/-! ### Translation of the free energy -/

lemma t5_ent_integrable {g : Euc d → ℝ} {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) (hfin : HasFiniteFreeEnergy g (confinement a) ρ) :
    Integrable fun x => ρ x * Real.log (ρ x / gaussianComparison d a β x) := by
  have hρi : Integrable ρ := Integrable.of_integral_ne_zero (by rw [hρ.integral_one]; norm_num)
  have := (hfin.1.sub (hρi.const_mul (Real.log (t5c d a β)))).add (hfin.2.1.const_mul β)
  refine this.congr (ae_of_all _ fun x => ?_)
  by_cases h0 : ρ x = 0
  · simp [h0]
  · have hρne : 0 < ρ x := lt_of_le_of_ne (hρ.nonneg x) (Ne.symm h0)
    have hγ := gaussianComparison_pos (d := d) ha hβ x
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [Real.log_div hρne.ne' hγ.ne', t5_log_gamma ha hβ]
    ring

lemma t5_relEnt_eq {g : Euc d → ℝ} {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) (hfin : HasFiniteFreeEnergy g (confinement a) ρ) :
    relEnt ρ (gaussianComparison d a β) =
      (∫ x, ρ x * Real.log (ρ x)) - Real.log (t5c d a β) + β * ∫ x, confinement a x * ρ x := by
  have hρi : Integrable ρ := Integrable.of_integral_ne_zero (by rw [hρ.integral_one]; norm_num)
  unfold relEnt
  have hpt : ∀ x, ρ x * Real.log (ρ x / gaussianComparison d a β x) =
      (ρ x * Real.log (ρ x) - Real.log (t5c d a β) * ρ x) + β * (confinement a x * ρ x) := by
    intro x
    by_cases h0 : ρ x = 0
    · simp [h0]
    · have hρne : 0 < ρ x := lt_of_le_of_ne (hρ.nonneg x) (Ne.symm h0)
      have hγ := gaussianComparison_pos (d := d) ha hβ x
      rw [Real.log_div hρne.ne' hγ.ne', t5_log_gamma ha hβ]
      ring
  simp_rw [hpt]
  have h1 : Integrable fun x => Real.log (t5c d a β) * ρ x := hρi.const_mul _
  have h2 : Integrable fun x => ρ x * Real.log (ρ x) - Real.log (t5c d a β) * ρ x :=
    hfin.1.sub h1
  have h3 : Integrable fun x => β * (confinement a x * ρ x) := hfin.2.1.const_mul β
  rw [integral_add h2 h3, integral_sub hfin.1 h1, integral_const_mul, integral_const_mul,
    hρ.integral_one]
  ring

/-- **Translation.**  On probability densities with finite free energy,
`F(ρ) = G(ρ) + β⁻¹ log c_γ` where `G = β⁻¹ H(· | γ) + ½ E_g`. -/
theorem freeEnergy_eq_Gfun_add {g : Euc d → ℝ} {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (hfin : HasFiniteFreeEnergy g (confinement a) ρ) :
    freeEnergy g (confinement a) β ρ =
      Gfun (fun x y => g (x - y)) (gaussianComparison d a β) β ρ + β⁻¹ * Real.log (t5c d a β) := by
  unfold Gfun pairE freeEnergy
  rw [t5_relEnt_eq ha hβ hρ hfin]
  have hb : β ≠ 0 := hβ.ne'
  field_simp
  ring

end HRS.MS.Thm

end
