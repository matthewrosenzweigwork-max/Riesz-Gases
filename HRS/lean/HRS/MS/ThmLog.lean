import HRS.MS.ThmLogAux2

/-!
# THM-7 (`s = 0`): proof of `HRS.Whole.logThermalDensity_spec`

Instantiate `ThmSetting` with `K = t67K d` (`K̃ x y = -log |x-y| + ½ l x + ½ l y + ½ log 2`, `l = log (1+|·|²)`) and
`r = γ̄ = t67gammaBar d a β` (the NORMALISED density `(1+|x|²)^{β/2} e^{-βa|x|²/2} / c̄`), `ThmLogAux2.t67_setting`.
THM-3/THM-4 give an a.e. Euler fixed point `μ ∈ C_M` minimising `G = β⁻¹ H(· | γ̄) + ½ E_K̃`, and
`ρ₀ = thermalRep μ = Tmap μ` is a pointwise fixed point.

Translation (`t67_freeEnergy_eq`): on probability densities with finite free energy,
`F(ρ) = G(ρ) - β⁻¹ log c̄ - ¼ log 2`.  It uses `l ≤ V + C` (`V = a|x|²/2`), so `∫ l ρ < ∞` from `V ρ ∈ L¹`, and
`∫ρ = 1`:  `E_K̃(ρ) = E_g(ρ) + ∫ l ρ + ½ log 2` and `H(ρ | γ̄) = ∫ρ log ρ - (β/2) ∫ l ρ + β ∫ V ρ + log c̄`.

Exports: `logThermalDensity_spec_proof : type_of% @HRS.Whole.logThermalDensity_spec`.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Thm

open HRS.Whole

variable {d : ℕ}

/-! ### Comparison `l ≤ V + C` and moments of `γ̄` -/

/-- The constant in `l ≤ V + C`. -/
def t67C2 (a : ℝ) : ℝ := a / 2 - 1 - Real.log (a / 2)

lemma t67l_le_V {a : ℝ} (ha : 0 < a) (x : Euc d) : t67l x ≤ confinement a x + t67C2 a := by
  have h := t67l_le (d := d) (ε := a / 2) (by positivity) x
  have e : a / 2 * ‖x‖ ^ 2 = confinement a x := by unfold confinement; ring
  unfold t67C2
  linarith

lemma t67_V_gammaBar_integrable {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    Integrable fun x : Euc d => confinement a x * t67gammaBar d a β x := by
  have hc := t67cbar_pos (d := d) ha hβ
  have h := (t012_integrable_sq_mul_exp (d := d) (b := β * a / 4) (by positivity)).const_mul
    (a / 2 * (Real.exp (β * (a / 2 - 1 - Real.log (a / 2)) / 2) / t67cbar d a β))
  have hm : Measurable fun x : Euc d => confinement a x * t67gammaBar d a β x := by
    unfold confinement
    exact (by fun_prop : Measurable fun x : Euc d => a * ‖x‖ ^ 2 / 2).mul (t67gammaBar_measurable a β)
  refine Integrable.mono' h hm.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  have hV0 : 0 ≤ confinement a x := by unfold confinement; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hV0 (t67gammaBar_pos ha hβ x).le)]
  unfold t67gammaBar
  have h1 : t67w a β x / t67cbar d a β ≤
      (Real.exp (β * (a / 2 - 1 - Real.log (a / 2)) / 2) * Real.exp (-(β * a / 4) * ‖x‖ ^ 2)) /
        t67cbar d a β := div_le_div_of_nonneg_right (t67w_le ha hβ x) hc.le
  calc confinement a x * (t67w a β x / t67cbar d a β)
      ≤ (a / 2 * ‖x‖ ^ 2) * ((Real.exp (β * (a / 2 - 1 - Real.log (a / 2)) / 2) *
          Real.exp (-(β * a / 4) * ‖x‖ ^ 2)) / t67cbar d a β) := by
        have e : confinement a x = a / 2 * ‖x‖ ^ 2 := by unfold confinement; ring
        rw [e]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

lemma t67_log_gammaBar {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (x : Euc d) :
    Real.log (t67gammaBar d a β x) =
      β / 2 * t67l x - β * confinement a x - Real.log (t67cbar d a β) := by
  unfold t67gammaBar t67w
  rw [Real.log_div (Real.exp_pos _).ne' (t67cbar_pos ha hβ).ne', Real.log_exp]

/-! ### Integrability bookkeeping for a probability density -/

section Density

variable {a β : ℝ} {ρ : Euc d → ℝ}

lemma t67_lrho_integrable (ha : 0 < a) (hρ : HRS.Whole.IsProbDensity ρ)
    (hV : Integrable fun x => confinement a x * ρ x) : Integrable fun x => t67l x * ρ x := by
  have hρi : Integrable ρ := t012_integrable_of_prob hρ
  refine Integrable.mono' (hV.add (hρi.const_mul (t67C2 a)))
    (t67l_measurable.mul hρ.measurable).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (t67l_nonneg x) (hρ.nonneg x))]
  have := mul_le_mul_of_nonneg_right (t67l_le_V ha x) (hρ.nonneg x)
  simp only [Pi.add_apply]
  nlinarith [this]

/-- The part of `K̃ ρ ρ` that does not come from `g`. -/
def t67E (ρ : Euc d → ℝ) (p : Euc d × Euc d) : ℝ :=
  (1 / 2) * ((t67l p.1 * ρ p.1) * ρ p.2) + (1 / 2) * (ρ p.1 * (t67l p.2 * ρ p.2)) +
    (1 / 2 * Real.log 2) * (ρ p.1 * ρ p.2)

lemma t67_decomp (ρ : Euc d → ℝ) (p : Euc d × Euc d) :
    t67K d p.1 p.2 * ρ p.1 * ρ p.2 = rieszKernel d 0 (p.1 - p.2) * ρ p.1 * ρ p.2 + t67E ρ p := by
  unfold t67K t67E
  ring

lemma t67_E_integrable (hρi : Integrable ρ) (hlρ : Integrable fun x => t67l x * ρ x) :
    Integrable (t67E ρ) ((volume : Measure (Euc d)).prod volume) := by
  unfold t67E
  exact (((hlρ.mul_prod hρi).const_mul (1 / 2)).add ((hρi.mul_prod hlρ).const_mul (1 / 2))).add
    ((hρi.mul_prod hρi).const_mul (1 / 2 * Real.log 2))

lemma t67_E_integral (hρ : HRS.Whole.IsProbDensity ρ) (hρi : Integrable ρ)
    (hlρ : Integrable fun x => t67l x * ρ x) :
    ∫ p, t67E ρ p ∂((volume : Measure (Euc d)).prod volume) =
      (∫ x, t67l x * ρ x) + (1 / 2) * Real.log 2 := by
  unfold t67E
  have h1 : Integrable (fun p : Euc d × Euc d => (1 / 2) * ((t67l p.1 * ρ p.1) * ρ p.2))
      ((volume : Measure (Euc d)).prod volume) := (hlρ.mul_prod hρi).const_mul _
  have h2 : Integrable (fun p : Euc d × Euc d => (1 / 2) * (ρ p.1 * (t67l p.2 * ρ p.2)))
      ((volume : Measure (Euc d)).prod volume) := (hρi.mul_prod hlρ).const_mul _
  have h3 : Integrable (fun p : Euc d × Euc d => (1 / 2 * Real.log 2) * (ρ p.1 * ρ p.2))
      ((volume : Measure (Euc d)).prod volume) := (hρi.mul_prod hρi).const_mul _
  have h12 : Integrable (fun p : Euc d × Euc d => (1 / 2) * ((t67l p.1 * ρ p.1) * ρ p.2) +
      (1 / 2) * (ρ p.1 * (t67l p.2 * ρ p.2))) ((volume : Measure (Euc d)).prod volume) := h1.add h2
  rw [integral_add h12 h3, integral_add h1 h2, integral_const_mul, integral_const_mul,
    integral_const_mul]
  rw [integral_prod_mul (fun x => t67l x * ρ x) ρ, integral_prod_mul ρ (fun x => t67l x * ρ x),
    integral_prod_mul ρ ρ, hρ.integral_one]
  ring

/-- `K̃`-pairing integrable on the product, from the `g`-pairing and `l ρ ∈ L¹`. -/
lemma t67_K_integrable_of_g (hρ : HRS.Whole.IsProbDensity ρ)
    (hlρ : Integrable fun x => t67l x * ρ x)
    (hg : Integrable (fun p : Euc d × Euc d => rieszKernel d 0 (p.1 - p.2) * ρ p.1 * ρ p.2)
      ((volume : Measure (Euc d)).prod volume)) :
    Integrable (fun p : Euc d × Euc d => t67K d p.1 p.2 * ρ p.1 * ρ p.2)
      ((volume : Measure (Euc d)).prod volume) :=
  (hg.add (t67_E_integrable (t012_integrable_of_prob hρ) hlρ)).congr
    (ae_of_all _ fun p => (t67_decomp ρ p).symm)

lemma t67_g_integrable_of_K (hρ : HRS.Whole.IsProbDensity ρ)
    (hlρ : Integrable fun x => t67l x * ρ x)
    (hK : Integrable (fun p : Euc d × Euc d => t67K d p.1 p.2 * ρ p.1 * ρ p.2)
      ((volume : Measure (Euc d)).prod volume)) :
    Integrable (fun p : Euc d × Euc d => rieszKernel d 0 (p.1 - p.2) * ρ p.1 * ρ p.2)
      ((volume : Measure (Euc d)).prod volume) :=
  (hK.sub (t67_E_integrable (t012_integrable_of_prob hρ) hlρ)).congr
    (ae_of_all _ fun p => by simp only [Pi.sub_apply, t67_decomp ρ p]; ring)

lemma t67_ent_pt (ha : 0 < a) (hβ : 0 < β) (hρ : HRS.Whole.IsProbDensity ρ) (x : Euc d) :
    ρ x * Real.log (ρ x / t67gammaBar d a β x) =
      (ρ x * Real.log (ρ x) - (β / 2) * (t67l x * ρ x)) +
        (β * (confinement a x * ρ x) + Real.log (t67cbar d a β) * ρ x) := by
  by_cases h0 : ρ x = 0
  · simp [h0]
  · have hρne : 0 < ρ x := lt_of_le_of_ne (hρ.nonneg x) (Ne.symm h0)
    rw [Real.log_div hρne.ne' (t67gammaBar_pos ha hβ x).ne', t67_log_gammaBar ha hβ]
    ring

lemma t67_ent_integrable (ha : 0 < a) (hβ : 0 < β) (hρ : HRS.Whole.IsProbDensity ρ)
    (hent : Integrable fun x => ρ x * Real.log (ρ x))
    (hV : Integrable fun x => confinement a x * ρ x) :
    Integrable fun x => ρ x * Real.log (ρ x / t67gammaBar d a β x) := by
  have hρi := t012_integrable_of_prob hρ
  have hlρ := t67_lrho_integrable ha hρ hV
  have := (hent.sub (hlρ.const_mul (β / 2))).add ((hV.const_mul β).add (hρi.const_mul (Real.log (t67cbar d a β))))
  exact this.congr (ae_of_all _ fun x => (t67_ent_pt ha hβ hρ x).symm)

lemma t67_ent_integrable' (ha : 0 < a) (hβ : 0 < β) (hρ : HRS.Whole.IsProbDensity ρ)
    (hlog : Integrable fun x => ρ x * Real.log (ρ x / t67gammaBar d a β x))
    (hV : Integrable fun x => confinement a x * ρ x) :
    Integrable fun x => ρ x * Real.log (ρ x) := by
  have hρi := t012_integrable_of_prob hρ
  have hlρ := t67_lrho_integrable ha hρ hV
  have := ((hlog.add (hlρ.const_mul (β / 2))).sub ((hV.const_mul β).add (hρi.const_mul (Real.log (t67cbar d a β)))))
  refine this.congr (ae_of_all _ fun x => ?_)
  have h := t67_ent_pt ha hβ hρ x
  simp only [Pi.sub_apply, Pi.add_apply]
  linarith

lemma t67_relEnt_eq (ha : 0 < a) (hβ : 0 < β) (hρ : HRS.Whole.IsProbDensity ρ)
    (hent : Integrable fun x => ρ x * Real.log (ρ x))
    (hV : Integrable fun x => confinement a x * ρ x) :
    relEnt ρ (t67gammaBar d a β) =
      (∫ x, ρ x * Real.log (ρ x)) - (β / 2) * (∫ x, t67l x * ρ x) +
        β * (∫ x, confinement a x * ρ x) + Real.log (t67cbar d a β) := by
  have hρi := t012_integrable_of_prob hρ
  have hlρ := t67_lrho_integrable ha hρ hV
  unfold relEnt
  simp_rw [t67_ent_pt ha hβ hρ]
  have h0 : Integrable fun x : Euc d => (β / 2) * (t67l x * ρ x) := hlρ.const_mul _
  have h1 : Integrable fun x : Euc d => ρ x * Real.log (ρ x) - (β / 2) * (t67l x * ρ x) :=
    hent.sub h0
  have h2a : Integrable fun x : Euc d => β * (confinement a x * ρ x) := hV.const_mul β
  have h2b : Integrable fun x : Euc d => Real.log (t67cbar d a β) * ρ x := hρi.const_mul _
  have h2 : Integrable fun x : Euc d => β * (confinement a x * ρ x) +
      Real.log (t67cbar d a β) * ρ x := h2a.add h2b
  rw [integral_add h1 h2, integral_sub hent h0, integral_add h2a h2b, integral_const_mul,
    integral_const_mul, integral_const_mul, hρ.integral_one]
  ring

/-- **Translation.**  `F(ρ) = G(ρ) - β⁻¹ log c̄ - ¼ log 2` on probability densities with finite free energy. -/
theorem t67_freeEnergy_eq (ha : 0 < a) (hβ : 0 < β) (hρ : HRS.Whole.IsProbDensity ρ)
    (hfin : HasFiniteFreeEnergy (rieszKernel d 0) (confinement a) ρ) :
    freeEnergy (rieszKernel d 0) (confinement a) β ρ =
      Gfun (t67K d) (t67gammaBar d a β) β ρ - β⁻¹ * Real.log (t67cbar d a β) -
        (1 / 4) * Real.log 2 := by
  have hρi := t012_integrable_of_prob hρ
  have hlρ := t67_lrho_integrable ha hρ hfin.2.1
  have hKi := t67_K_integrable_of_g hρ hlρ hfin.2.2
  have hpair : pairE (t67K d) ρ ρ =
      (∫ x, ∫ y, rieszKernel d 0 (x - y) * ρ x * ρ y) + ((∫ x, t67l x * ρ x) + (1 / 2) * Real.log 2) := by
    rw [t012_pairE_eq_prod hKi, ← t67_E_integral hρ hρi hlρ, ← integral_prod _ hfin.2.2,
      ← integral_add hfin.2.2 (t67_E_integrable hρi hlρ)]
    exact integral_congr_ae (ae_of_all _ fun p => t67_decomp ρ p)
  unfold Gfun freeEnergy
  rw [t67_relEnt_eq ha hβ hρ hfin.1 hfin.2.1, hpair]
  have hb : β ≠ 0 := hβ.ne'
  field_simp
  ring

end Density

/-! ### Bounded densities: finite free energy, the convolution, the thermal equation -/

section Fixed

variable {a β B M : ℝ} {ρ : Euc d → ℝ}

lemma t67_Vrho_of_le (ha : 0 < a) (hβ : 0 < β) (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ}
    (hρM : ∀ x, ρ x ≤ M * t67gammaBar d a β x) : Integrable fun x => confinement a x * ρ x := by
  have hm : Measurable fun x : Euc d => confinement a x * ρ x := by
    unfold confinement
    exact (by fun_prop : Measurable fun x : Euc d => a * ‖x‖ ^ 2 / 2).mul hρ.measurable
  refine Integrable.mono' ((t67_V_gammaBar_integrable ha hβ).const_mul M) hm.aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  have hV0 : 0 ≤ confinement a x := by unfold confinement; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hV0 (hρ.nonneg x))]
  calc confinement a x * ρ x ≤ confinement a x * (M * t67gammaBar d a β x) :=
        mul_le_mul_of_nonneg_left (hρM x) hV0
    _ = M * (confinement a x * t67gammaBar d a β x) := by ring

/-- A probability density `ρ ≤ M γ̄` has finite free energy for `g = -log |·|`. -/
theorem t67_hasFiniteFreeEnergy_of_le (hS : ThmSetting (t67K d) (t67gammaBar d a β) B)
    (ha : 0 < a) (hβ : 0 < β) (hM : 1 ≤ M) (hρ : ρ ∈ Cset (t67gammaBar d a β) M) :
    HasFiniteFreeEnergy (rieszKernel d 0) (confinement a) ρ := by
  have hρi := t012_integrable_of_prob hρ.1
  have hV := t67_Vrho_of_le ha hβ hρ.1 hρ.2
  have hlρ := t67_lrho_integrable ha hρ.1 hV
  have hlog := t012_integrable_mul_log_div_of_le (t67gammaBar_integrable ha hβ)
    (t67gammaBar_pos ha hβ) (t67gammaBar_measurable a β) hρ.1.measurable hρ.1.nonneg hρ.2
  have hent := t67_ent_integrable' ha hβ hρ.1 hlog hV
  have hKi := t012_prod_integrable hS.meas hS.nonneg (fun y => (hS.r_pos y).le) hS.k1
    hρ.1.measurable hρi hρ.1.measurable (by linarith) (fun y => by
      rw [abs_of_nonneg (hρ.1.nonneg y)]; exact hρ.2 y)
  exact ⟨hent, hV, t67_g_integrable_of_K hρ.1 hlρ hKi⟩

/-- The pairing `K̃ * ρ` against a bounded density, in terms of the `g`-convolution. -/
lemma t67_conv_eq (hS : ThmSetting (t67K d) (t67gammaBar d a β) B) (ha : 0 < a) (hβ : 0 < β)
    (hM : 1 ≤ M) (hρ : ρ ∈ Cset (t67gammaBar d a β) M) (z : Euc d) :
    Integrable (fun y => rieszKernel d 0 (z - y) * ρ y) ∧
      ∫ y, t67K d z y * ρ y = (∫ y, rieszKernel d 0 (z - y) * ρ y) + (1 / 2) * t67l z +
        (1 / 2) * (∫ y, t67l y * ρ y) + (1 / 2) * Real.log 2 := by
  have hρi := t012_integrable_of_prob hρ.1
  have hV := t67_Vrho_of_le ha hβ hρ.1 hρ.2
  have hlρ := t67_lrho_integrable ha hρ.1 hV
  obtain ⟨hKi, -, -⟩ := conv_bound_of_le hS.meas hS.nonneg hS.k1 hρ.1.measurable hρ.1.nonneg
    (by linarith : 0 ≤ M) hρ.2 z
  have hpt : ∀ y, t67K d z y * ρ y = rieszKernel d 0 (z - y) * ρ y +
      (((1 / 2 * t67l z) * ρ y + (1 / 2) * (t67l y * ρ y)) + (1 / 2 * Real.log 2) * ρ y) := by
    intro y; unfold t67K; ring
  have r1 : Integrable fun y : Euc d => (1 / 2 * t67l z) * ρ y := hρi.const_mul _
  have r2 : Integrable fun y : Euc d => (1 / 2) * (t67l y * ρ y) := hlρ.const_mul _
  have r3 : Integrable fun y : Euc d => (1 / 2 * Real.log 2) * ρ y := hρi.const_mul _
  have r12 : Integrable fun y : Euc d => (1 / 2 * t67l z) * ρ y + (1 / 2) * (t67l y * ρ y) := r1.add r2
  have hrest : Integrable fun y : Euc d =>
      ((1 / 2 * t67l z) * ρ y + (1 / 2) * (t67l y * ρ y)) + (1 / 2 * Real.log 2) * ρ y := r12.add r3
  have hgi : Integrable (fun y => rieszKernel d 0 (z - y) * ρ y) :=
    (hKi.sub hrest).congr (ae_of_all _ fun y => by simp only [Pi.sub_apply]; rw [hpt y]; ring)
  refine ⟨hgi, ?_⟩
  simp_rw [hpt]
  rw [integral_add hgi hrest, integral_add r12 r3, integral_add r1 r2, integral_const_mul,
    integral_const_mul, integral_const_mul, hρ.1.integral_one]
  ring

/-- An everywhere fixed point of `Tmap K̃ γ̄` in `C_M` solves the thermal equation for `g = -log |·|`. -/
theorem t67_thermalDensity_of_fixed (hS : ThmSetting (t67K d) (t67gammaBar d a β) B) (ha : 0 < a)
    (hβ : 0 < β) (hM : 1 ≤ M) (hρ : ρ ∈ Cset (t67gammaBar d a β) M)
    (hfix : ∀ x, ρ x = Tmap (t67K d) (t67gammaBar d a β) β ρ x) :
    HRS.Whole.IsThermalDensity (rieszKernel d 0) (confinement a) β ρ := by
  refine ⟨hρ.1, fun x => ?_⟩
  have hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d 0) (HRS.Whole.withDensityReal ρ) z =
      ∫ y, rieszKernel d 0 (z - y) * ρ y := fun z =>
    convMeasure_withDensityReal _ hρ.1.measurable hρ.1.nonneg z
  simp_rw [hconv]
  set c0 : ℝ := (1 / 2) * (∫ y, t67l y * ρ y) + (1 / 2) * Real.log 2 with hc0
  have hc := t67cbar_pos (d := d) ha hβ
  have key : ∀ z, t67gammaBar d a β z * Real.exp (-β * ∫ y, t67K d z y * ρ y) =
      (Real.exp (-β * c0) / t67cbar d a β) *
        Real.exp (-β * (confinement a z + ∫ y, rieszKernel d 0 (z - y) * ρ y)) := by
    intro z
    rw [(t67_conv_eq hS ha hβ hM hρ z).2]
    unfold t67gammaBar t67w
    have gen : ∀ A B C D : ℝ, A + B = D + C →
        Real.exp A / t67cbar d a β * Real.exp B = Real.exp D / t67cbar d a β * Real.exp C := by
      intro A B C D h
      rw [div_mul_eq_mul_div, ← Real.exp_add, h, Real.exp_add]
      ring
    apply gen
    rw [hc0]
    ring
  have hA : 0 < Real.exp (-β * c0) / t67cbar d a β := div_pos (Real.exp_pos _) hc
  rw [hfix x]
  unfold Tmap
  simp_rw [key]
  rw [integral_const_mul, mul_div_mul_left _ _ hA.ne']

/-- A fixed point of the Euler map in `C_M` is a thermal equilibrium for `s = 0` (existence part). -/
theorem t67_equilibrium_of_fixed (hS : ThmSetting (t67K d) (t67gammaBar d a β) B) (ha : 0 < a)
    (hβ : 0 < β) (hM : 1 ≤ M) (hρ : ρ ∈ Cset (t67gammaBar d a β) M)
    (hfix : ∀ x, ρ x = Tmap (t67K d) (t67gammaBar d a β) β ρ x) :
    HRS.Whole.IsThermalEquilibrium d 0 a β ρ := by
  have hfin := t67_hasFiniteFreeEnergy_of_le hS ha hβ hM hρ
  refine ⟨⟨hρ.1, hfin, ?_⟩, t67_thermalDensity_of_fixed hS ha hβ hM hρ hfix⟩
  intro ρ' hρ' hfin'
  have hfae : ρ =ᵐ[volume] Tmap (t67K d) (t67gammaBar d a β) β ρ := ae_of_all _ hfix
  have hlρ' := t67_lrho_integrable ha hρ' hfin'.2.1
  have hmin := (minimizer_of_fixedpoint hS hβ hM hρ hfae).1 ρ' hρ'
    (t67_ent_integrable ha hβ hρ' hfin'.1 hfin'.2.1) (t67_K_integrable_of_g hρ' hlρ' hfin'.2.2)
  rw [t67_freeEnergy_eq ha hβ hρ.1 hfin, t67_freeEnergy_eq ha hβ hρ' hfin']
  linarith

/-- Every free-energy minimiser equals the fixed point a.e. -/
theorem t67_minimizer_ae_eq (hS : ThmSetting (t67K d) (t67gammaBar d a β) B) (ha : 0 < a)
    (hβ : 0 < β) (hM : 1 ≤ M) (hρ : ρ ∈ Cset (t67gammaBar d a β) M)
    (hfix : ∀ x, ρ x = Tmap (t67K d) (t67gammaBar d a β) β ρ x) {l : Euc d → ℝ}
    (hl : HRS.Whole.IsFreeEnergyMinimizer (rieszKernel d 0) (confinement a) β l) :
    l =ᵐ[volume] ρ := by
  have hfae : ρ =ᵐ[volume] Tmap (t67K d) (t67gammaBar d a β) β ρ := ae_of_all _ hfix
  have hfin := t67_hasFiniteFreeEnergy_of_le hS ha hβ hM hρ
  obtain ⟨hlp, hlfin, hlmin⟩ := hl
  have h1 := hlmin ρ hρ.1 hfin
  rw [t67_freeEnergy_eq ha hβ hρ.1 hfin, t67_freeEnergy_eq ha hβ hlp hlfin] at h1
  have hlρ' := t67_lrho_integrable ha hlp hlfin.2.1
  have hent := t67_ent_integrable ha hβ hlp hlfin.1 hlfin.2.1
  have hKl := t67_K_integrable_of_g hlp hlρ' hlfin.2.2
  obtain ⟨hA, hB'⟩ := minimizer_of_fixedpoint hS hβ hM hρ hfae
  have h2 := hA l hlp hent hKl
  have h3 : Gfun (t67K d) (t67gammaBar d a β) β l = Gfun (t67K d) (t67gammaBar d a β) β ρ := by
    exact le_antisymm (by linarith) h2
  exact hB' l hlp hent hKl h3

end Fixed

/-- The data produced by THM-3/THM-4 for `K̃` and `γ̄`: an a.e. Euler fixed point in `C_M`. -/
theorem t67_exists_fixed (hd : 1 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    ∃ (B M : ℝ) (μ : Euc d → ℝ), ThmSetting (t67K d) (t67gammaBar d a β) B ∧ 1 ≤ M ∧
      Real.exp (β * B) ≤ M ∧ μ ∈ Cset (t67gammaBar d a β) M ∧
      μ =ᵐ[volume] Tmap (t67K d) (t67gammaBar d a β) β μ := by
  obtain ⟨B, hS⟩ := t67_setting hd ha hβ
  have hM : 1 ≤ max 1 (Real.exp (β * B)) := le_max_left _ _
  have hexp : Real.exp (β * B) ≤ max 1 (Real.exp (β * B)) := le_max_right _ _
  obtain ⟨μ, hμ, hmin⟩ := exists_min_Cset hS hM hβ
  exact ⟨B, _, μ, hS, hM, hexp, hμ, fixedpoint_of_min hS hβ hM hexp hμ hmin⟩

/-- Everything about the `s = 0` thermal equilibrium: the pointwise representative `ρ₀ = thermalRep μ` is a bounded
thermal equilibrium and every free-energy minimiser equals it a.e. -/
theorem t67_spec_data (hd : 1 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    ∃ ρ₀ : Euc d → ℝ, HRS.Whole.IsThermalEquilibrium d 0 a β ρ₀ ∧ (∃ C, ∀ x, ρ₀ x ≤ C) ∧
      ∀ l : Euc d → ℝ, HRS.Whole.IsFreeEnergyMinimizer (rieszKernel d 0) (confinement a) β l →
        l =ᵐ[volume] ρ₀ := by
  obtain ⟨B, M, μ, hS, hM, hexp, hμ, hfix⟩ := t67_exists_fixed hd ha hβ
  have hρC := thermalRep_mem_Cset hS hβ.le hexp hμ.1
  have hρfix := thermalRep_fixed hfix
  have hEq := t67_equilibrium_of_fixed hS ha hβ hM hρC hρfix
  refine ⟨_, hEq, ⟨M * (Real.exp (β * (a / 2 - 1 - Real.log (a / 2)) / 2) / t67cbar d a β), fun x => ?_⟩,
    fun l hl => t67_minimizer_ae_eq hS ha hβ hM hρC hρfix hl⟩
  exact (hρC.2 x).trans (mul_le_mul_of_nonneg_left (t67gammaBar_le ha hβ x) (by linarith))

/-- **THM-7.**  The logarithmic (`s = 0`) thermal equilibrium exists, is bounded, is the unique free-energy
minimiser (a.e.), and is `thermalDensity d 0 a β` (a.e.). -/
theorem logThermalDensity_spec_proof : type_of% @HRS.Whole.logThermalDensity_spec := by
  intro d hd a β ha hβ
  have hd1 : 1 ≤ d := by omega
  obtain ⟨ρ₀, hEq, hbd, hmin⟩ := t67_spec_data hd1 ha hβ
  have hex : ∃ ρ, HRS.Whole.IsThermalEquilibrium d 0 a β ρ := ⟨_, hEq⟩
  have hτ : HRS.Whole.IsThermalEquilibrium d 0 a β (thermalDensity d 0 a β) := by
    unfold thermalDensity
    rw [dif_pos hex]
    exact hex.choose_spec
  refine ⟨⟨ρ₀, hEq, hbd⟩, ?_, ?_⟩
  · intro ρ ρ' h h'
    exact (hmin ρ h).trans (hmin ρ' h').symm
  · intro ρ h
    exact (hmin ρ h).trans (hmin _ hτ.1).symm

end HRS.MS.Thm

end
