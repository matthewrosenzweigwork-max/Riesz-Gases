import HRS.Commutator.Whole.ScaleAux

/-!
# Scaling of the modulated energy (packet CMX-SCALE, helpers, part 2)

Helpers carry the prefix `cmxSA_`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

lemma cmxSA_kern_scale_ne (hs : s ≠ 0) (η : ℝ) (hη : 0 < η) (z : Euc d) :
    kern s (η⁻¹ • z) = η ^ s * kern s z := by
  unfold kern
  simp only [hs, if_false]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hη),
    Real.mul_rpow (inv_nonneg.2 hη.le) (norm_nonneg _), Real.rpow_neg (inv_nonneg.2 hη.le),
    Real.inv_rpow hη.le, inv_inv]
  ring

lemma cmxSA_kern_scale_zero (η : ℝ) (hη : 0 < η) (z : Euc d) (hz : z ≠ 0) :
    kern 0 (η⁻¹ • z) = kern 0 z + Real.log η := by
  unfold kern
  simp only [if_true]
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hη),
    Real.log_mul (inv_pos.2 hη).ne' hn.ne', Real.log_inv]
  ring

/-- `1` off the diagonal, `0` on it. -/
def cmxSA_I (a b : Euc d) : ℝ := if a = b then 0 else 1

lemma cmxSA_pairGen_I {N : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d) (X : Fin N → Euc d)
    (hX : Function.Injective X) (ρ : Euc d → ℝ) (hmass : ∫ x, ρ x = 1) :
    pairGen cmxSA_I X ρ = -1 / (N : ℝ) := by
  haveI : NeZero d := ⟨by omega⟩
  haveI : Nontrivial (Euc d) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    infer_instance
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have e1 : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, cmxSA_I (X i) (X j) = (N : ℝ) - 1 := by
    intro i
    have : ∀ j ∈ Finset.univ.erase i, cmxSA_I (X i) (X j) = 1 := by
      intro j hj
      have : X i ≠ X j := fun h => (Finset.ne_of_mem_erase hj) (hX h).symm
      simp [cmxSA_I, this]
    rw [Finset.sum_congr rfl this]
    simp [Finset.card_erase_of_mem, Nat.cast_sub hN]
  have e2 : ∀ i : Fin N, ∫ y, cmxSA_I (X i) y * ρ y = 1 := by
    intro i
    rw [← hmass]
    refine integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume (X i)] with y hy
    simp [cmxSA_I, hy.symm]
  have e3 : ∫ x, ∫ y, cmxSA_I x y * ρ x * ρ y = 1 := by
    rw [← hmass]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    have : ∫ y, cmxSA_I x y * ρ x * ρ y = ∫ y, ρ x * ρ y := by
      refine integral_congr_ae ?_
      filter_upwards [Measure.ae_ne volume x] with y hy
      simp [cmxSA_I, hy.symm]
    rw [this, integral_const_mul, hmass, mul_one]
  unfold pairGen
  simp_rw [e1, e2, e3]
  simp
  field_simp
  ring

lemma cmxSA_pairGen_add {N : ℕ} (k₁ k₂ : Euc d → Euc d → ℝ) (X : Fin N → Euc d) (ρ : Euc d → ℝ)
    (h₁ : ∀ a, Integrable (fun y => k₁ a y * ρ y)) (h₂ : ∀ a, Integrable (fun y => k₂ a y * ρ y))
    (H₁ : Integrable (fun q : Euc d × Euc d => k₁ q.1 q.2 * ρ q.1 * ρ q.2))
    (H₂ : Integrable (fun q : Euc d × Euc d => k₂ q.1 q.2 * ρ q.1 * ρ q.2)) :
    pairGen (fun a b => k₁ a b + k₂ a b) X ρ = pairGen k₁ X ρ + pairGen k₂ X ρ := by
  unfold pairGen
  have e1 : ∀ i, ∫ y, (k₁ (X i) y + k₂ (X i) y) * ρ y =
      (∫ y, k₁ (X i) y * ρ y) + ∫ y, k₂ (X i) y * ρ y := by
    intro i
    rw [← integral_add (h₁ (X i)) (h₂ (X i))]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only; ring)
  have e2 : ∫ x, ∫ y, (k₁ x y + k₂ x y) * ρ x * ρ y =
      (∫ x, ∫ y, k₁ x y * ρ x * ρ y) + ∫ x, ∫ y, k₂ x y * ρ x * ρ y := by
    have i1 : ∀ x, Integrable (fun y => k₁ x y * ρ x * ρ y) := fun x => by
      have := (h₁ x).const_mul (ρ x)
      refine this.congr (Filter.Eventually.of_forall fun y => ?_)
      simp only; ring
    have i2 : ∀ x, Integrable (fun y => k₂ x y * ρ x * ρ y) := fun x => by
      have := (h₂ x).const_mul (ρ x)
      refine this.congr (Filter.Eventually.of_forall fun y => ?_)
      simp only; ring
    rw [← integral_add H₁.integral_prod_left H₂.integral_prod_left]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [← integral_add (i1 x) (i2 x)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only; ring)
  simp_rw [e1, e2, Finset.sum_add_distrib]
  ring

lemma cmxSA_bdd_integrable {ρ : Euc d → ℝ} (hρ : BddCptDensity ρ) : Integrable ρ := by
  obtain ⟨B, hB⟩ := hρ.bdd
  have hK : IsCompact (tsupport ρ) := hρ.cpt
  have hind : Integrable ((tsupport ρ).indicator (fun _ => B)) :=
    (integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne)
  refine hind.mono' hρ.measurable.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ tsupport ρ
  · rw [Set.indicator_of_mem hx]; exact hB x
  · have : ρ x = 0 := by
      by_contra h; exact hx (subset_tsupport _ h)
    rw [this]; simp only [norm_zero]
    exact Set.indicator_nonneg (fun y _ => (abs_nonneg (ρ y)).trans (hB y)) x

lemma cmxSA_bdd_memLp {ρ : Euc d → ℝ} (hρ : BddCptDensity ρ) : MemLp ρ ⊤ volume := by
  obtain ⟨B, hB⟩ := hρ.bdd
  exact memLp_top_of_bound hρ.measurable.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x => by simpa using hB x)

lemma cmxSA_bdd_W {ρ : Euc d → ℝ} (hρ : BddCptDensity ρ) :
    Integrable (fun x => cmxSA_W s x * ρ x) := by
  by_cases hs : s = 0
  · subst hs
    have hK : IsCompact (tsupport ρ) := hρ.cpt
    obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    have h1 := cmxSA_bdd_integrable hρ
    refine Integrable.mono' (h1.norm.const_mul (Real.log (2 + R))) 
      (((cmxSA_W_measurable 0).mul hρ.measurable).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : ρ x = 0
    · simp [hx]
    · have hxR : ‖x‖ ≤ R := hR x (subset_tsupport _ hx)
      simp only [cmxSA_W, if_true, norm_mul]
      have hl : 0 ≤ Real.log (2 + ‖x‖) := Real.log_nonneg (by linarith [norm_nonneg x])
      rw [Real.norm_of_nonneg hl]
      have : Real.log (2 + ‖x‖) ≤ Real.log (2 + R) :=
        Real.log_le_log (by positivity) (by linarith)
      gcongr
  · simp only [cmxSA_W, hs, if_false, zero_mul]
    exact integrable_zero _ _ _

theorem cmxSA_modEnergy_scale (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (η : ℝ)
    (hη : 0 < η) (ρ : Euc d → ℝ) (hρ : BddCptDensity ρ) {N : ℕ} (hN : 1 ≤ N) (X : Fin N → Euc d)
    (hX : Function.Injective X) :
    modEnergy s (scaleConf η X) (scaleDens η ρ) =
      η ^ s * modEnergy s X ρ - (if s = 0 then Real.log η / (2 * (N : ℝ)) else 0) := by
  unfold modEnergy
  rw [cmxSA_pairGen_scale _ η hη]
  haveI : NeZero d := ⟨by omega⟩
  haveI : Nontrivial (Euc d) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    infer_instance
  by_cases hs : s = 0
  · subst hs
    have hint := cmxSA_energy_all_meas hd hs0 hsd ⊤ (by simp) ρ hρ.measurable
      (cmxSA_bdd_integrable hρ) (cmxSA_bdd_memLp hρ) (cmxSA_bdd_W hρ)
    have hk : ∀ a b : Euc d, kern 0 (η⁻¹ • a - η⁻¹ • b) =
        kern 0 (a - b) + Real.log η * cmxSA_I a b := by
      intro a b
      rw [← smul_sub]
      by_cases hab : a = b
      · subst hab; simp [kern, cmxSA_I]
      · rw [cmxSA_kern_scale_zero η hη _ (sub_ne_zero.2 hab)]
        simp [cmxSA_I, hab]
    have hI1 : ∀ a, Integrable (fun y => (Real.log η * cmxSA_I a y) * ρ y) := by
      intro a
      have := (cmxSA_bdd_integrable hρ).const_mul (Real.log η)
      refine this.congr ?_
      filter_upwards [Measure.ae_ne volume a] with y hy
      simp [cmxSA_I, hy.symm]
    have hI2 : Integrable (fun q : Euc d × Euc d => (Real.log η * cmxSA_I q.1 q.2) * ρ q.1 * ρ q.2) := by
      have := ((cmxSA_bdd_integrable hρ).mul_prod (cmxSA_bdd_integrable hρ)).const_mul (Real.log η)
      refine this.congr ?_
      have hae : ∀ᵐ q : Euc d × Euc d ∂(volume.prod volume), q.1 ≠ q.2 := by
        have hm : MeasurableSet {q : Euc d × Euc d | q.1 ≠ q.2} :=
          (measurableSet_eq_fun measurable_fst measurable_snd).compl
        rw [Measure.ae_prod_iff_ae_ae hm]
        refine Filter.Eventually.of_forall fun x => ?_
        filter_upwards [Measure.ae_ne volume x] with y hy
        exact hy.symm
      filter_upwards [hae] with q hq
      simp [cmxSA_I, hq]; ring
    have hadd := cmxSA_pairGen_add (fun a b => kern 0 (a - b)) (fun a b => Real.log η * cmxSA_I a b) X ρ
      hint.1 hI1 hint.2 hI2
    have hc : pairGen (fun a b => Real.log η * cmxSA_I a b) X ρ = Real.log η * (-1 / (N : ℝ)) := by
      rw [cmxSA_pairGen_const_mul, cmxSA_pairGen_I hN (by omega) X hX ρ hρ.mass]
    simp_rw [hk]
    rw [hadd, hc]
    simp only [if_true, Real.rpow_zero, one_mul]
    field_simp
    ring
  · simp_rw [← smul_sub, cmxSA_kern_scale_ne hs η hη]
    rw [cmxSA_pairGen_const_mul]
    simp only [hs, if_false, sub_zero]
    ring

end HRS.Commutator.Whole
