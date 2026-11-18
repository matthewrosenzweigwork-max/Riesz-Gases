import HRS.MS.MovEntAux10
import HRS.Main.MixEnt1

/-!
# S6.6, packet P6 (part 5): `Q_{N,β}(ρ₂ κ)` is a bounded tilt of `Q_{N,β}(ρ₂)`

`s66_tilt_identity`: if `ρ₁ = ρ₂ κ` (`κ > 0`) and `u = g*ρ₁ - g*ρ₂` is measurable, then
`Q_{N,β}(ρ₁) = Q_{N,β}(ρ₂).tilted w`, `w(X) = ∑_i (log κ(x_i) + β u(x_i))` (the modulated energies differ by `-(1/N)∑u(x_i) + const`).
`s66_gibbs_finite`: hence (with `u`, `log κ` bounded) finiteness of `H(f|Q(ρ₁))` implies finiteness of `H(f|Q(ρ₂))`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MovEnt

open HRS.Whole

local notation "wd" => Whole.withDensityReal

variable {d : ℕ}

theorem s66_modEnergy_diff {N : ℕ} (hN : 1 ≤ N) (g : Euc d → ℝ) (μ₁ μ₂ : Measure (Euc d)) (X : EucConfig d N) :
    (N : ℝ) * (Whole.modulatedEnergy g X μ₁ - Whole.modulatedEnergy g X μ₂) =
      -∑ i, (Whole.convMeasure g μ₁ (X i) - Whole.convMeasure g μ₂ (X i)) +
        (N : ℝ) / 2 * (Whole.energyPairing g μ₁ μ₁ - Whole.energyPairing g μ₂ μ₂) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  unfold Whole.modulatedEnergy
  rw [Finset.sum_sub_distrib]
  field_simp
  ring

theorem s66_w_bdd {N : ℕ} {β : ℝ} (hβ : 0 < β) {κ u : Euc d → ℝ} {B Lk : ℝ}
    (hB : ∀ x, |u x| ≤ B) (hLk : ∀ x, |Real.log (κ x)| ≤ Lk) (X : EucConfig d N) :
    |∑ i, (Real.log (κ (X i)) + β * u (X i))| ≤ N * (Lk + β * B) := by
  calc |∑ i, (Real.log (κ (X i)) + β * u (X i))| ≤ ∑ i, |Real.log (κ (X i)) + β * u (X i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, (Lk + β * B) := by
        refine Finset.sum_le_sum fun i _ => ?_
        calc |Real.log (κ (X i)) + β * u (X i)| ≤ |Real.log (κ (X i))| + |β * u (X i)| := abs_add_le _ _
          _ ≤ Lk + β * B := by
              rw [abs_mul, abs_of_pos hβ]
              exact add_le_add (hLk _) (mul_le_mul_of_nonneg_left (hB _) hβ.le)
    _ = N * (Lk + β * B) := by simp; ring

theorem s66_modGibbs_prob {N : ℕ} {s β : ℝ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    (hW : GibbsWellDefined (fun x y => rieszKernel d s (x - y)) N β μ) :
    IsProbabilityMeasure (Whole.modulatedGibbs (rieszKernel d s) N β μ) := by
  rw [s66_modGibbs_tilted hW]
  exact isProbabilityMeasure_tilted hW.weight_integrable

set_option maxHeartbeats 1600000 in
theorem s66_tilt_identity {N : ℕ} (hN : 1 ≤ N) {s β : ℝ} (hβ : 0 < β) {ρ₁ ρ₂ κ : Euc d → ℝ}
    (hρ₁ : Whole.IsProbDensity ρ₁) (hρ₂ : Whole.IsProbDensity ρ₂) (hκm : Measurable κ)
    (hκ0 : ∀ x, 0 < κ x) (hρκ : ∀ x, ρ₁ x = ρ₂ x * κ x)
    (hW₁ : GibbsWellDefined (fun x y => rieszKernel d s (x - y)) N β (wd ρ₁))
    (hW₂ : GibbsWellDefined (fun x y => rieszKernel d s (x - y)) N β (wd ρ₂))
    (hum : Measurable (fun x => Whole.convMeasure (rieszKernel d s) (wd ρ₁) x - Whole.convMeasure (rieszKernel d s) (wd ρ₂) x))
    {B Lk : ℝ} (hB : ∀ x, |Whole.convMeasure (rieszKernel d s) (wd ρ₁) x - Whole.convMeasure (rieszKernel d s) (wd ρ₂) x| ≤ B)
    (hLk : ∀ x, |Real.log (κ x)| ≤ Lk) :
    Whole.modulatedGibbs (rieszKernel d s) N β (wd ρ₁) =
      (Whole.modulatedGibbs (rieszKernel d s) N β (wd ρ₂)).tilted
        (fun X : EucConfig d N => ∑ i, (Real.log (κ (X i)) +
          β * (Whole.convMeasure (rieszKernel d s) (wd ρ₁) (X i) - Whole.convMeasure (rieszKernel d s) (wd ρ₂) (X i)))) := by
  set g : Euc d → ℝ := rieszKernel d s with hg
  set μ₁ : Measure (Euc d) := wd ρ₁ with hμ₁
  set μ₂ : Measure (Euc d) := wd ρ₂ with hμ₂
  haveI : IsProbabilityMeasure μ₁ := HRS.MS.Thm.cb_withDensityReal_isProb hρ₁
  haveI : IsProbabilityMeasure μ₂ := HRS.MS.Thm.cb_withDensityReal_isProb hρ₂
  set π₂ : Measure (EucConfig d N) := Measure.pi fun _ : Fin N => μ₂ with hπ₂
  set u : Euc d → ℝ := fun x => Whole.convMeasure g μ₁ x - Whole.convMeasure g μ₂ x with hu
  set cc : ℝ := Whole.energyPairing g μ₁ μ₁ - Whole.energyPairing g μ₂ μ₂ with hcc
  have hGm := HRS.MS.Wr.wr9_rieszKernel_pair_meas (d := d) s
  have hFm : ∀ μ : Measure (Euc d), SFinite μ → Measurable (fun X : EucConfig d N =>
      Whole.modulatedEnergy g X μ) := fun μ _ => HRS.MS.Wr.wr9_measurable_pairEnergy (k := fun x y => g (x - y)) (μ := μ) hGm
  -- Step 1: the product measure of `ρ₁ = ρ₂ κ`
  have hfm : Measurable (fun x : Euc d => ENNReal.ofReal (κ x)) := ENNReal.measurable_ofReal.comp hκm
  have hρ₂m : Measurable (fun x : Euc d => ENNReal.ofReal (ρ₂ x)) :=
    ENNReal.measurable_ofReal.comp hρ₂.measurable
  have hμ₁eq : μ₁ = μ₂.withDensity (fun x => ENNReal.ofReal (κ x)) := by
    simp only [hμ₁, hμ₂, Whole.withDensityReal]
    rw [← withDensity_mul volume hρ₂m hfm]
    congr 1
    funext x
    simp only [Pi.mul_apply, hρκ x]
    exact ENNReal.ofReal_mul (hρ₂.nonneg x)
  haveI : SigmaFinite (μ₂.withDensity (fun x => ENNReal.ofReal (κ x))) := by
    rw [← hμ₁eq]; infer_instance
  have hπ₁ : (Measure.pi fun _ : Fin N => μ₁) =
      π₂.withDensity (fun X => ∏ i, ENNReal.ofReal (κ (X i))) := by
    rw [hμ₁eq]
    exact HRS.Main.mx_pi_withDensity μ₂ _ hfm
  -- the weights
  set f₁ : EucConfig d N → ℝ := fun X => -β * N * Whole.modulatedEnergy g X μ₁ with hf₁
  set f₂ : EucConfig d N → ℝ := fun X => -β * N * Whole.modulatedEnergy g X μ₂ with hf₂
  set w : EucConfig d N → ℝ := fun X => ∑ i, (Real.log (κ (X i)) + β * u (X i)) with hw
  have hf₁m : Measurable f₁ := measurable_const.mul (hFm μ₁ inferInstance)
  have hf₂m : Measurable f₂ := measurable_const.mul (hFm μ₂ inferInstance)
  have hwm : Measurable w := by
    refine Finset.measurable_sum _ fun i _ => ?_
    have h1 : Measurable (fun X : EucConfig d N => Real.log (κ (X i))) :=
      Real.measurable_log.comp (hκm.comp (measurable_pi_apply i))
    have h2 : Measurable (fun X : EucConfig d N => u (X i)) := hum.comp (measurable_pi_apply i)
    exact h1.add (h2.const_mul β)
  have hDκm : Measurable (fun X : EucConfig d N => ∏ i, ENNReal.ofReal (κ (X i))) :=
    Finset.measurable_prod _ fun i _ => hfm.comp (measurable_pi_apply i)
  have hE1m : Measurable (fun X => ENNReal.ofReal (Real.exp (f₁ X))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hf₁m)
  have hE2m : Measurable (fun X => ENNReal.ofReal (Real.exp (f₂ X))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hf₂m)
  have hEwm : Measurable (fun X => ENNReal.ofReal (Real.exp (w X))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hwm)
  -- Step 2: pointwise identity of the densities
  set c₀ : ℝ := Real.exp (-β * N * cc / 2) with hc₀
  have hpt : ∀ X : EucConfig d N,
      (∏ i, ENNReal.ofReal (κ (X i))) * ENNReal.ofReal (Real.exp (f₁ X)) =
        ENNReal.ofReal c₀ * (ENNReal.ofReal (Real.exp (f₂ X)) * ENNReal.ofReal (Real.exp (w X))) := by
    intro X
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (hκ0 (X i)).le), ← ENNReal.ofReal_mul
      (Finset.prod_nonneg fun i _ => (hκ0 (X i)).le), ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    have hdiff := s66_modEnergy_diff hN g μ₁ μ₂ X
    have hprod : ∏ i, κ (X i) = Real.exp (∑ i, Real.log (κ (X i))) := by
      rw [Real.exp_sum]
      exact Finset.prod_congr rfl fun i _ => (Real.exp_log (hκ0 (X i))).symm
    rw [hprod, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    simp only [hf₁, hf₂, hw, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h2 : (N : ℝ) * (Whole.modulatedEnergy g X μ₁ - Whole.modulatedEnergy g X μ₂) =
        -∑ i, u (X i) + (N : ℝ) / 2 * cc := hdiff
    nlinarith [h2]
  -- Step 3: `Q₁` as a multiple of `Q₂.withDensity (e^w)`
  have hK₁pos : 0 < Whole.gibbsNormalizer g N β μ₁ := hW₁.normalizer_pos
  have hK₂pos : 0 < Whole.gibbsNormalizer g N β μ₂ := hW₂.normalizer_pos
  set K₁ : ℝ := Whole.gibbsNormalizer g N β μ₁ with hK₁
  set K₂ : ℝ := Whole.gibbsNormalizer g N β μ₂ with hK₂
  set M : Measure (EucConfig d N) := π₂.withDensity
    (fun X => ENNReal.ofReal (Real.exp (f₂ X)) * ENNReal.ofReal (Real.exp (w X))) with hM
  have hQ₂ : Whole.modulatedGibbs g N β μ₂ =
      (ENNReal.ofReal K₂)⁻¹ • π₂.withDensity (fun X => ENNReal.ofReal (Real.exp (f₂ X))) := rfl
  have hQ₁ : Whole.modulatedGibbs g N β μ₁ =
      (ENNReal.ofReal K₁)⁻¹ • (π₂.withDensity (fun X => ∏ i, ENNReal.ofReal (κ (X i)))).withDensity
          (fun X => ENNReal.ofReal (Real.exp (f₁ X))) := by
    show (ENNReal.ofReal K₁)⁻¹ •
        (Measure.pi fun _ : Fin N => μ₁).withDensity (fun X => ENNReal.ofReal (Real.exp (f₁ X))) = _
    rw [hπ₁]
  have hLHS : Whole.modulatedGibbs g N β μ₁ = ((ENNReal.ofReal K₁)⁻¹ * ENNReal.ofReal c₀) • M := by
    rw [hQ₁, ← withDensity_mul π₂ hDκm hE1m, hM]
    have e1 : ((fun X => ∏ i, ENNReal.ofReal (κ (X i))) * fun X => ENNReal.ofReal (Real.exp (f₁ X))) =
        ENNReal.ofReal c₀ • (fun X => ENNReal.ofReal (Real.exp (f₂ X)) * ENNReal.ofReal (Real.exp (w X))) := by
      funext X
      simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
      exact hpt X
    rw [e1, withDensity_smul' _ _ ENNReal.ofReal_ne_top, smul_smul]
  have hRHS : (Whole.modulatedGibbs g N β μ₂).withDensity (fun X => ENNReal.ofReal (Real.exp (w X))) =
      (ENNReal.ofReal K₂)⁻¹ • M := by
    rw [hQ₂, withDensity_smul_measure, hM, ← withDensity_mul π₂ hE2m hEwm]
    try rfl
  set κ' : ℝ≥0∞ := (ENNReal.ofReal K₁)⁻¹ * ENNReal.ofReal c₀ * ENNReal.ofReal K₂ with hκ'
  have hmain : Whole.modulatedGibbs g N β μ₁ =
      κ' • (Whole.modulatedGibbs g N β μ₂).withDensity (fun X => ENNReal.ofReal (Real.exp (w X))) := by
    rw [hLHS, hRHS, smul_smul]
    congr 1
    have this : ENNReal.ofReal K₂ * (ENNReal.ofReal K₂)⁻¹ = 1 :=
      ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 hK₂pos).ne' ENNReal.ofReal_ne_top
    rw [hκ', mul_assoc ((ENNReal.ofReal K₁)⁻¹ * ENNReal.ofReal c₀) (ENNReal.ofReal K₂), this, mul_one]
  -- Step 4: normalisation
  haveI hQ₁p : IsProbabilityMeasure (Whole.modulatedGibbs g N β μ₁) := s66_modGibbs_prob (s := s) hW₁
  haveI hQ₂p : IsProbabilityMeasure (Whole.modulatedGibbs g N β μ₂) := s66_modGibbs_prob (s := s) hW₂
  set Q₂ := Whole.modulatedGibbs g N β μ₂ with hQ₂def
  have hwb : ∀ X, |w X| ≤ N * (Lk + β * B) := fun X => s66_w_bdd hβ hB hLk X
  have hexpint : Integrable (fun X => Real.exp (w X)) Q₂ :=
    Integrable.of_bound (C := Real.exp (N * (Lk + β * B)))
      (Real.measurable_exp.comp hwm).aestronglyMeasurable
      (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 ((le_abs_self _).trans (hwb X)))
  set Z : ℝ := ∫ X, Real.exp (w X) ∂Q₂ with hZ
  have hZpos : 0 < Z := integral_exp_pos hexpint
  have hZl : ∫⁻ X, ENNReal.ofReal (Real.exp (w X)) ∂Q₂ = ENNReal.ofReal Z :=
    (ofReal_integral_eq_lintegral_ofReal hexpint (Eventually.of_forall fun X => (Real.exp_pos _).le)).symm
  have hone : κ' * ENNReal.ofReal Z = 1 := by
    have h1 := hQ₁p.measure_univ
    rw [hmain, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hZl,
      smul_eq_mul] at h1
    exact h1
  have hκ'eq : κ' = (ENNReal.ofReal Z)⁻¹ :=
    ENNReal.eq_inv_of_mul_eq_one_left hone
  rw [hmain, hκ'eq]
  unfold Measure.tilted
  have e : (fun X => ENNReal.ofReal (Real.exp (w X) / ∫ x, Real.exp (w x) ∂Q₂)) =
      (ENNReal.ofReal Z)⁻¹ • fun X => ENNReal.ofReal (Real.exp (w X)) := by
    funext X
    rw [ENNReal.ofReal_div_of_pos hZpos]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [ENNReal.div_eq_inv_mul]
  rw [e, withDensity_smul' _ _ (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hZpos).ne')]


theorem s66_gibbs_finite {N : ℕ} (hN : 1 ≤ N) {s β : ℝ} (hβ : 0 < β) {ρ₁ ρ₂ κ : Euc d → ℝ}
    (hρ₁ : Whole.IsProbDensity ρ₁) (hρ₂ : Whole.IsProbDensity ρ₂) (hκm : Measurable κ)
    (hκ0 : ∀ x, 0 < κ x) (hρκ : ∀ x, ρ₁ x = ρ₂ x * κ x)
    (hW₁ : GibbsWellDefined (fun x y => rieszKernel d s (x - y)) N β (wd ρ₁))
    (hW₂ : GibbsWellDefined (fun x y => rieszKernel d s (x - y)) N β (wd ρ₂))
    (hum : Measurable (fun x => Whole.convMeasure (rieszKernel d s) (wd ρ₁) x - Whole.convMeasure (rieszKernel d s) (wd ρ₂) x))
    {B Lk : ℝ} (hB : ∀ x, |Whole.convMeasure (rieszKernel d s) (wd ρ₁) x - Whole.convMeasure (rieszKernel d s) (wd ρ₂) x| ≤ B)
    (hLk : ∀ x, |Real.log (κ x)| ≤ Lk)
    (f : Measure (EucConfig d N)) [IsProbabilityMeasure f]
    (hfin : relEntropy f (Whole.modulatedGibbs (rieszKernel d s) N β (wd ρ₁)) ≠ ⊤) :
    relEntropy f (Whole.modulatedGibbs (rieszKernel d s) N β (wd ρ₂)) ≠ ⊤ := by
  haveI : IsProbabilityMeasure (wd ρ₂) := HRS.MS.Thm.cb_withDensityReal_isProb hρ₂
  haveI hQ₂p : IsProbabilityMeasure (Whole.modulatedGibbs (rieszKernel d s) N β (wd ρ₂)) :=
    s66_modGibbs_prob (s := s) hW₂
  have hid := s66_tilt_identity hN hβ hρ₁ hρ₂ hκm hκ0 hρκ hW₁ hW₂ hum hB hLk
  set w : EucConfig d N → ℝ := fun X : EucConfig d N => ∑ i, (Real.log (κ (X i)) +
    β * (Whole.convMeasure (rieszKernel d s) (wd ρ₁) (X i) - Whole.convMeasure (rieszKernel d s) (wd ρ₂) (X i))) with hw
  have hwm : Measurable w := by
    refine Finset.measurable_sum _ fun i _ => ?_
    have h1 : Measurable (fun X : EucConfig d N => Real.log (κ (X i))) :=
      Real.measurable_log.comp (hκm.comp (measurable_pi_apply i))
    have h2 := hum.comp (measurable_pi_apply i : Measurable fun X : EucConfig d N => X i)
    exact h1.add (h2.const_mul β)
  have hwb : ∀ X, |w X| ≤ N * (Lk + β * B) := fun X => s66_w_bdd hβ hB hLk X
  have hexp : Integrable (fun X => Real.exp (w X))
      (Whole.modulatedGibbs (rieszKernel d s) N β (wd ρ₂)) :=
    Integrable.of_bound (C := Real.exp (N * (Lk + β * B)))
      (Real.measurable_exp.comp hwm).aestronglyMeasurable
      (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 ((le_abs_self _).trans (hwb X)))
  have hwi : Integrable w f :=
    Integrable.of_bound (C := N * (Lk + β * B)) hwm.aestronglyMeasurable
      (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]; exact hwb X)
  unfold relEntropy at hfin ⊢
  rw [hid] at hfin
  exact ((s66_kl_tilted _ f hexp hwi).1).1 hfin

end HRS.MS.MovEnt

end
