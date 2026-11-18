import HRS.MS.S82RN6
import HRS.MS.S82RN7

/-!
# S8.2 R02 (S82R), N8: removal of one particle at measure level, with position weight
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Function
open scoped ENNReal BigOperators

namespace HRS.MS.S82R
open HRS.External HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

/-- The unpinned ensemble with the one extra pin `x` is the ensemble with the field lowered by `lam q(., x)`. -/
lemma s82r_pinnedLaw_empty_pin {μ : Measure (Euc d)} [IsProbabilityMeasure μ] (V : WeakPotential μ)
    (lam : ℝ) (n : ℕ) (x : Euc d) :
    pinnedLaw V lam n (pinsWith (fun e : Empty => e.elim) x) =
      fieldLaw V (s82r_Fld V (fun _ : Fin 1 => x) (fun _ => lam) Finset.univ V.φ) lam n := by
  unfold pinnedLaw
  congr 1
  funext z
  rw [pinField_pinsWith]
  simp [pinField, s82r_Fld]

lemma s82r_pinnedLaw_empty {μ : Measure (Euc d)} [IsProbabilityMeasure μ] (V : WeakPotential μ)
    (lam : ℝ) (n : ℕ) :
    pinnedLaw V lam n (fun e : Empty => e.elim) = fieldLaw V V.φ lam n := by
  unfold pinnedLaw
  congr 1
  funext z
  simp [pinField]

theorem s82r_removal_measure (hd : 2 ≤ d) {q : Euc d → ℝ} (hq : ShortRangePole d q) (M : ℝ)
    {Mψ M₁ P β γ : ℝ} (hβ : 0 < β) (hγ : 0 ≤ γ)
    (hα : β * γ * (Real.exp (Mψ + (M₁ + P)) + Real.exp (Mψ + (M₁ + P)) ^ 2) < 1) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ ρμ : Euc d → ℝ, HRS.Whole.IsProbDensity ρμ → (∀ x, ρμ x ≤ M) →
      ∀ (μ : Measure (Euc d)), μ = HRS.Whole.withDensityReal ρμ →
      ∀ (V : WeakPotential μ), (∀ x y, V.q x y = q (x - y)) →
      V.γ = γ → IsField μ V.φ Mψ M₁ →
      ∀ {n : ℕ} [NeZero n] {lam : ℝ}, 0 ≤ lam → lam * ((n : ℝ) + 1) * γ ≤ P →
      ((n : ℝ) - 1) * lam ≤ β → ∀ (i : Fin (n + 1)) (j : Fin n) {K' : ℝ}, 0 ≤ K' →
      (pinnedLaw V lam (n + 1) (fun e : Empty => e.elim)).map (fun y => y i) ≤
        ENNReal.ofReal K' • μ →
      ∀ {S : Set (Euc d)}, MeasurableSet S →
      |((pinnedLaw V lam (n + 1) (fun e : Empty => e.elim)).map (fun y => y (i.succAbove j))).real S -
        ((pinnedLaw V lam n (fun e : Empty => e.elim)).map (fun y => y j)).real S| ≤
        K' * (lam * (A * γ + B)) * μ.real S := by
  obtain ⟨A, B, hA, hB, hpin⟩ := s82r_pin_measure hd hq M hβ hγ hα
  refine ⟨A, B, hA, hB, fun ρμ hρ hM μ hμ V hVq hVγ hψ n _ lam hlam hP hnl i j K' hK' hmarg S hS => ?_⟩
  subst hμ
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρμ) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hqm : Measurable q := hq.measurable
  have hq0 := hq.nonneg
  have hrow : ∀ u : Euc d, ∫ z, q (z - u) ∂(HRS.Whole.withDensityReal ρμ) ≤ γ := fun u => by
    have := integral_q_left_le V u
    simp only [hVq] at this
    rwa [hVγ] at this
  have hrow' : ∀ z : Euc d, ∫ x, q (z - x) ∂(HRS.Whole.withDensityReal ρμ) ≤ γ := fun z => by
    have e : ∀ x, q (z - x) = q (x - z) := fun x => by rw [← hq.even (z - x), neg_sub]
    simp_rw [e]; exact hrow z
  have hqi : ∀ w : Euc d, Integrable (fun u => q (u - w)) (HRS.Whole.withDensityReal ρμ) := fun w =>
    s82r_row_integrable hd hq hρ hM w
  have hqi' : ∀ w : Euc d, Integrable (fun u => q (w - u)) (HRS.Whole.withDensityReal ρμ) := fun w => by
    have e : ∀ x, q (w - x) = q (x - w) := fun x => by rw [← hq.even (w - x), neg_sub]
    simp_rw [e]; exact hqi w
  have hP1 : (∑ ℓ : Fin 1, lam) * γ + lam * n * γ ≤ P := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul]
    nlinarith [hP]
  -- the pointwise comparison for each value of the removed coordinate
  set a0 : Empty → Euc d := fun e => e.elim with ha0
  set rr : Euc d → ℝ := fun x =>
    ((pinnedLaw V lam n (pinsWith a0 x)).map (fun y => y j)).real S with hrr
  set r0 : ℝ := ((pinnedLaw V lam n a0).map (fun y => y j)).real S with hr0
  have hr00 : 0 ≤ r0 := measureReal_nonneg
  have hfun : ∀ x : Euc d, Integrable (fun z => lam * (A * q (z - x) + B)) (HRS.Whole.withDensityReal ρμ) := fun x =>
    (((hqi x).const_mul A).add (integrable_const B)).const_mul lam
  have hfun0 : ∀ x z : Euc d, 0 ≤ lam * (A * q (z - x) + B) := fun x z =>
    mul_nonneg hlam (add_nonneg (mul_nonneg hA (hq0 _)) hB)
  have hfun0' : ∀ z x : Euc d, 0 ≤ lam * (A * q (z - x) + B) := fun z x =>
    mul_nonneg hlam (add_nonneg (mul_nonneg hA (hq0 _)) hB)
  have hpt : ∀ x : Euc d, |r0 - rr x| ≤ ∫ z in S, lam * (A * q (z - x) + B) ∂(HRS.Whole.withDensityReal ρμ) := by
    intro x
    have h := hpin ρμ hρ hM (HRS.Whole.withDensityReal ρμ) rfl V hVq hVγ hψ (m := 1) (n := n) (fun _ => x) (fun _ => lam)
      (fun _ => hlam) hlam hP1 hnl j hS
    have e0 : r0 = (fieldLaw V V.φ lam n).real ((fun y : Fin n → Euc d => y j) ⁻¹' S) := by
      rw [hr0, s82r_pinnedLaw_empty]
      simp only [Measure.real, Measure.map_apply (f := fun y : Fin n → Euc d => y j) (measurable_pi_apply j) hS]
    have e1 : rr x = (fieldLaw V (s82r_Fld V (fun _ : Fin 1 => x) (fun _ => lam) Finset.univ V.φ) lam n).real
        ((fun y : Fin n → Euc d => y j) ⁻¹' S) := by
      rw [hrr]
      simp only
      rw [s82r_pinnedLaw_empty_pin]
      simp only [Measure.real, Measure.map_apply (f := fun y : Fin n → Euc d => y j) (measurable_pi_apply j) hS]
    rw [e0, e1]
    simpa using h
  set d' : Euc d → ℝ≥0∞ := fun x => ∫⁻ z in S, ENNReal.ofReal (lam * (A * q (z - x) + B)) ∂(HRS.Whole.withDensityReal ρμ) with hd'
  have hfm : Measurable fun p : Euc d × Euc d => ENNReal.ofReal (lam * (A * q (p.2 - p.1) + B)) :=
    (measurable_const.mul ((measurable_const.mul (hqm.comp (measurable_snd.sub measurable_fst))).add
      measurable_const)).ennreal_ofReal
  have hdm : Measurable d' := hfm.lintegral_prod_right' (ν := (HRS.Whole.withDensityReal ρμ).restrict S)
  have hde : ∀ x, ENNReal.ofReal (∫ z in S, lam * (A * q (z - x) + B) ∂(HRS.Whole.withDensityReal ρμ)) = d' x := fun x => by
    rw [hd']
    exact ofReal_integral_eq_lintegral_ofReal (hfun x).integrableOn (ae_of_all _ fun z => hfun0 x z)
  have he0 : ∀ x, 0 ≤ ∫ z in S, lam * (A * q (z - x) + B) ∂(HRS.Whole.withDensityReal ρμ) := fun x =>
    setIntegral_nonneg hS fun z _ => hfun0 x z
  have hd1 : ∀ x, ENNReal.ofReal (rr x) ≤ ENNReal.ofReal r0 + d' x := fun x => by
    rw [← hde, ← ENNReal.ofReal_add hr00 (he0 x)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := (abs_le.1 (hpt x)).1
    linarith
  have hd2 : ∀ x, ENNReal.ofReal r0 ≤ ENNReal.ofReal (rr x) + d' x := fun x => by
    have hr : 0 ≤ rr x := measureReal_nonneg
    rw [← hde, ← ENNReal.ofReal_add hr (he0 x)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := (abs_le.1 (hpt x)).2
    linarith
  have hmz : ∀ x : Euc d, Measurable fun z : Euc d => ENNReal.ofReal (lam * (A * q (z - x) + B)) := fun x =>
    (measurable_const.mul ((measurable_const.mul (hqm.comp (measurable_id.sub measurable_const))).add
      measurable_const)).ennreal_ofReal
  set c : ℝ := K' * (lam * (A * γ + B)) with hc
  have hc0 : 0 ≤ c := mul_nonneg hK' (mul_nonneg hlam (add_nonneg (mul_nonneg hA hγ) hB))
  have hpm := s82r_pinWeight_meas V hlam (fun e : Empty => e.elim) i
  have hint : ∫⁻ x, pinWeight V lam a0 n x * d' x ∂(HRS.Whole.withDensityReal ρμ) ≤ ENNReal.ofReal c * (HRS.Whole.withDensityReal ρμ) S := by
    have e1 : ∀ x, pinWeight V lam a0 n x * d' x =
        ∫⁻ z in S, pinWeight V lam a0 n x * ENNReal.ofReal (lam * (A * q (z - x) + B)) ∂(HRS.Whole.withDensityReal ρμ) := fun x => by
      show _ * (∫⁻ z in S, ENNReal.ofReal (lam * (A * q (z - x) + B)) ∂(HRS.Whole.withDensityReal ρμ)) = _
      rw [lintegral_const_mul _ (hmz x)]
    simp_rw [e1]
    rw [lintegral_lintegral_swap]
    · calc ∫⁻ z in S, ∫⁻ x, pinWeight V lam a0 n x * ENNReal.ofReal (lam * (A * q (z - x) + B)) ∂(HRS.Whole.withDensityReal ρμ) ∂(HRS.Whole.withDensityReal ρμ)
          ≤ ∫⁻ z in S, ENNReal.ofReal c ∂(HRS.Whole.withDensityReal ρμ) := by
            refine lintegral_mono fun z => ?_
            have hg : Measurable fun x : Euc d => ENNReal.ofReal (lam * (A * q (z - x) + B)) :=
              (measurable_const.mul ((measurable_const.mul (hqm.comp (measurable_const.sub measurable_id))).add
                measurable_const)).ennreal_ofReal
            refine (s82r_pinWeight_lintegral_le V hlam a0 i hmarg hg).trans ?_
            have hint2 : Integrable (fun x => lam * (A * q (z - x) + B)) (HRS.Whole.withDensityReal ρμ) :=
              (((hqi' z).const_mul A).add (integrable_const B)).const_mul lam
            rw [← ofReal_integral_eq_lintegral_ofReal hint2 (ae_of_all _ fun x => hfun0' z x)]
            · rw [← ENNReal.ofReal_mul hK']
              refine ENNReal.ofReal_le_ofReal ?_
              rw [hc]
              refine mul_le_mul_of_nonneg_left ?_ hK'
              rw [integral_const_mul, integral_add ((hqi' z).const_mul A) (integrable_const B),
                integral_const_mul]
              simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
              have := hrow' z
              exact mul_le_mul_of_nonneg_left (by nlinarith [this, hA]) hlam
        _ = ENNReal.ofReal c * (HRS.Whole.withDensityReal ρμ) S := by
            rw [lintegral_const, Measure.restrict_apply_univ, mul_comm]
    · exact ((hpm.comp measurable_fst).mul (hfm.comp (measurable_fst.prodMk measurable_snd))).aemeasurable
  have hDt : ENNReal.ofReal c * (HRS.Whole.withDensityReal ρμ) S ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have := s82r_mix_compare V hlam a0 i j hS hr00 d' hdm hDt hd1 hd2 hint
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0] at this
  exact this

end HRS.MS.S82R

end
