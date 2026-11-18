import HRS.MP.SelfSimP5Chamber

/-!
# MPP5B (9): the initial term, `ss5_initial_bound`

`HRS.MP.SelfSimP5Impl.ss5_initial_bound_proof` has the statement of `HRS.MP.SelfSimP5.ss5_initial_bound`.
Route.  Both entropies are unnormalised free energies `klDiv μ w - w(univ)` for the finite reference measures
`w_G = Ḡ dξ` and `w_U = e^{-U_ε/θ} dz`.  Three generic facts about `klDiv` (finite measures): (A) it splits off the part
of the reference outside a set carrying `μ`; (B) `klDiv μ ν₂ + ν₁(univ) ≤ klDiv μ ν₁ + ν₂(univ)` if `ν₁ ≤ ν₂` (via the
integral representation with `klFun` and `dν₁/dν₂ ≤ 1`); (C) data processing for the measure preserving
map `toCh_σ`.  Geometry: `Ḡ = e^{-U/θ} ∘ toCh_σ` on `cone σ`, and `U_ε ≤ U` on the chamber because `φ_ε ≤ -log`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open HRS HRS.MP.SelfSimP5 HRS.MP.SelfSim HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP5Impl

/-! ### Generic facts on `klDiv` -/

theorem ss5i_klFun_mul_le {r t : ℝ} (hr : 0 ≤ r) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    klFun (r * t) ≤ t * klFun r + (1 - t) := by
  rcases hr.eq_or_lt with rfl | hr'
  · simp [klFun_zero]
  rcases ht0.eq_or_lt with rfl | ht'
  · simp [klFun_zero]
  have hlog : Real.log t ≤ 0 := Real.log_nonpos ht0 ht1
  simp only [klFun_apply]
  rw [Real.log_mul hr'.ne' ht'.ne']
  nlinarith [mul_nonneg hr'.le ht0, mul_nonneg (mul_nonneg hr'.le ht0) (neg_nonneg.2 hlog)]

/-- Monotonicity of the free energy `klDiv μ ν - ν(univ)` in the reference. -/
theorem ss5i_klDiv_ref_mono {α : Type*} [MeasurableSpace α] {μ ν₁ ν₂ : Measure α}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (h : ν₁ ≤ ν₂) (hμ : μ ≪ ν₁) :
    klDiv μ ν₂ + ν₁ Set.univ ≤ klDiv μ ν₁ + ν₂ Set.univ := by
  have h12 : ν₁ ≪ ν₂ := Measure.absolutelyContinuous_of_le h
  have hμ2 : μ ≪ ν₂ := hμ.trans h12
  set h' := ν₁.rnDeriv ν₂ with hh'
  have hle1 : ∀ᵐ x ∂ν₂, h' x ≤ 1 := Measure.rnDeriv_le_one_of_le h
  have hchain : ∀ᵐ x ∂ν₂, μ.rnDeriv ν₁ x * h' x = μ.rnDeriv ν₂ x := Measure.rnDeriv_mul_rnDeriv hμ
  have hlt : ∀ᵐ x ∂ν₂, μ.rnDeriv ν₂ x < ⊤ := Measure.rnDeriv_lt_top μ ν₂
  have hν₁ : ν₂.withDensity h' = ν₁ := Measure.withDensity_rnDeriv_eq _ _ h12
  have hh'm : Measurable h' := Measure.measurable_rnDeriv _ _
  set g : α → ℝ≥0∞ := fun x => ENNReal.ofReal (klFun (μ.rnDeriv ν₁ x).toReal) with hg
  have hgm : Measurable g := by
    have : Measurable fun x => (μ.rnDeriv ν₁ x).toReal := (Measure.measurable_rnDeriv _ _).ennreal_toReal
    exact (continuous_klFun.measurable.comp this).ennreal_ofReal
  have hpt : ∀ᵐ x ∂ν₂, ENNReal.ofReal (klFun (μ.rnDeriv ν₂ x).toReal) ≤
      h' x * g x + ENNReal.ofReal (1 - (h' x).toReal) := by
    filter_upwards [hle1, hchain, hlt] with x hx1 hx2 hx3
    by_cases h0 : h' x = 0
    · rw [← hx2, h0]
      simp [klFun_zero]
    have hhfin : h' x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hx1
    have hρ1 : μ.rnDeriv ν₁ x ≠ ⊤ := by
      intro htop
      rw [htop, ENNReal.top_mul h0] at hx2
      exact hx3.ne hx2.symm
    have ht0 : 0 ≤ (h' x).toReal := ENNReal.toReal_nonneg
    have ht1 : (h' x).toReal ≤ 1 := by
      have := ENNReal.toReal_mono ENNReal.one_ne_top hx1
      simpa using this
    have key := ss5i_klFun_mul_le (ENNReal.toReal_nonneg (a := μ.rnDeriv ν₁ x)) ht0 ht1
    rw [← hx2, ENNReal.toReal_mul]
    calc ENNReal.ofReal (klFun ((μ.rnDeriv ν₁ x).toReal * (h' x).toReal))
        ≤ ENNReal.ofReal ((h' x).toReal * klFun (μ.rnDeriv ν₁ x).toReal + (1 - (h' x).toReal)) :=
          ENNReal.ofReal_le_ofReal key
      _ ≤ ENNReal.ofReal ((h' x).toReal * klFun (μ.rnDeriv ν₁ x).toReal) +
            ENNReal.ofReal (1 - (h' x).toReal) := ENNReal.ofReal_add_le
      _ = h' x * g x + ENNReal.ofReal (1 - (h' x).toReal) := by
          rw [ENNReal.ofReal_mul ht0, ENNReal.ofReal_toReal hhfin]
  have hcompl : ∀ᵐ x ∂ν₂, ENNReal.ofReal (1 - (h' x).toReal) + h' x = 1 := by
    filter_upwards [hle1] with x hx
    have hhfin : h' x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hx
    have ht1 : (h' x).toReal ≤ 1 := by
      have := ENNReal.toReal_mono ENNReal.one_ne_top hx
      simpa using this
    have : ENNReal.ofReal (1 - (h' x).toReal) + ENNReal.ofReal (h' x).toReal = 1 := by
      rw [← ENNReal.ofReal_add (by linarith) ENNReal.toReal_nonneg]
      simp
    rwa [ENNReal.ofReal_toReal hhfin] at this
  have hmass : ∫⁻ x, ENNReal.ofReal (1 - (h' x).toReal) ∂ν₂ + ν₁ Set.univ = ν₂ Set.univ := by
    have e1 : ν₁ Set.univ = ∫⁻ x, h' x ∂ν₂ := by
      rw [← hν₁, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [e1, ← lintegral_add_right _ hh'm, lintegral_congr_ae hcompl]
    simp
  rw [klDiv_eq_lintegral_klFun_of_ac hμ2, klDiv_eq_lintegral_klFun_of_ac hμ]
  calc ∫⁻ x, ENNReal.ofReal (klFun (μ.rnDeriv ν₂ x).toReal) ∂ν₂ + ν₁ Set.univ
      ≤ ∫⁻ x, (h' x * g x + ENNReal.ofReal (1 - (h' x).toReal)) ∂ν₂ + ν₁ Set.univ := by
        exact add_le_add (lintegral_mono_ae hpt) le_rfl
    _ = ∫⁻ x, h' x * g x ∂ν₂ + (∫⁻ x, ENNReal.ofReal (1 - (h' x).toReal) ∂ν₂ + ν₁ Set.univ) := by
        rw [lintegral_add_left (f := fun x => h' x * g x) (hh'm.mul hgm), add_assoc]
    _ = ∫⁻ x, g x ∂ν₁ + ν₂ Set.univ := by
        rw [hmass, ← hν₁, lintegral_withDensity_eq_lintegral_mul _ hh'm hgm]
        rfl
    _ = _ := rfl

/-- Splitting off the part of the reference outside a set carrying `μ`. -/
theorem ss5i_klDiv_restrict {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {s : Set α} (hs : MeasurableSet s) (hμs : μ sᶜ = 0)
    (hμν : μ ≪ ν) : klDiv μ ν = klDiv μ (ν.restrict s) + ν sᶜ := by
  have hμr : μ ≪ ν.restrict s := by
    intro t ht
    rw [Measure.restrict_apply' hs] at ht
    have h1 : μ (t ∩ s) = 0 := hμν ht
    have h2 : t ⊆ (t ∩ s) ∪ sᶜ := fun x hx => by
      by_cases hxs : x ∈ s
      · exact Or.inl ⟨hx, hxs⟩
      · exact Or.inr hxs
    exact measure_mono_null h2 (measure_union_null h1 hμs)
  have hrestr : μ.restrict s = μ := Measure.restrict_eq_self_of_ae_mem (by
    rw [ae_iff]; exact hμs)
  have hrn : μ.rnDeriv (ν.restrict s) =ᵐ[ν.restrict s] μ.rnDeriv ν := by
    have e : (ν.restrict s).withDensity (μ.rnDeriv ν) = μ := by
      rw [← restrict_withDensity hs, Measure.withDensity_rnDeriv_eq _ _ hμν, hrestr]
    have := Measure.rnDeriv_withDensity (ν.restrict s) (Measure.measurable_rnDeriv μ ν)
    rwa [e] at this
  have hzero : ∀ᵐ x ∂(ν.restrict sᶜ), μ.rnDeriv ν x = 0 := by
    have h1 : ∫⁻ x in sᶜ, μ.rnDeriv ν x ∂ν = 0 := by
      rw [Measure.setLIntegral_rnDeriv' hμν hs.compl, hμs]
    exact (lintegral_eq_zero_iff (Measure.measurable_rnDeriv μ ν)).1 h1
  rw [klDiv_eq_lintegral_klFun_of_ac hμν, klDiv_eq_lintegral_klFun_of_ac hμr,
    ← lintegral_add_compl _ hs]
  congr 1
  · refine lintegral_congr_ae ?_
    filter_upwards [hrn] with x hx
    rw [hx]
  · have : ∫⁻ x in sᶜ, ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν = ∫⁻ x in sᶜ, 1 ∂ν := by
      refine lintegral_congr_ae ?_
      filter_upwards [hzero] with x hx
      simp [hx, klFun_zero]
    rw [this]
    simp

/-- Free-energy comparison with a reference that dominates the restriction to a set carrying `μ`. -/
theorem ss5i_klDiv_cmp {α : Type*} [MeasurableSpace α] {μ ν₁ ν₂ : Measure α}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] {s : Set α} (hs : MeasurableSet s)
    (hμs : μ sᶜ = 0) (hμ : μ ≪ ν₁) (h : ν₁.restrict s ≤ ν₂) :
    klDiv μ ν₂ + ν₁ Set.univ ≤ klDiv μ ν₁ + ν₂ Set.univ := by
  have hA := ss5i_klDiv_restrict hs hμs hμ
  have hμr : μ ≪ ν₁.restrict s := by
    intro t ht
    rw [Measure.restrict_apply' hs] at ht
    have h1 : μ (t ∩ s) = 0 := hμ ht
    have h2 : t ⊆ (t ∩ s) ∪ sᶜ := fun x hx => by
      by_cases hxs : x ∈ s
      · exact Or.inl ⟨hx, hxs⟩
      · exact Or.inr hxs
    exact measure_mono_null h2 (measure_union_null h1 hμs)
  have hB := ss5i_klDiv_ref_mono h hμr
  have hmass : ν₁ Set.univ = ν₁ s + ν₁ sᶜ := (measure_add_measure_compl hs).symm
  have hrs : (ν₁.restrict s) Set.univ = ν₁ s := by simp [Measure.restrict_apply, hs]
  rw [hrs] at hB
  calc klDiv μ ν₂ + ν₁ Set.univ = (klDiv μ ν₂ + ν₁ s) + ν₁ sᶜ := by rw [hmass, add_assoc]
    _ ≤ (klDiv μ (ν₁.restrict s) + ν₂ Set.univ) + ν₁ sᶜ := by gcongr
    _ = klDiv μ ν₁ + ν₂ Set.univ := by rw [hA]; ring

/-- Normalising a finite reference measure: finiteness is unchanged and the free energy is
`klDiv μ w + 1 - w(univ)`. -/
theorem ss5i_norm {α : Type*} [MeasurableSpace α] {μ w : Measure α} [IsProbabilityMeasure μ]
    [IsFiniteMeasure w] (hZ0 : w Set.univ ≠ 0) :
    (klDiv μ ((w Set.univ)⁻¹ • w) ≠ ⊤ ↔ klDiv μ w ≠ ⊤) ∧
    (klDiv μ w ≠ ⊤ → (klDiv μ ((w Set.univ)⁻¹ • w)).toReal - Real.log (w Set.univ).toReal =
      (klDiv μ w).toReal + 1 - (w Set.univ).toReal) := by
  set c : ℝ≥0∞ := (w Set.univ)⁻¹ with hc
  have hZt : w Set.univ ≠ ⊤ := measure_ne_top _ _
  have hc0 : c ≠ 0 := by simpa [hc] using hZt
  have hct : c ≠ ⊤ := by simpa [hc] using hZ0
  haveI : IsFiniteMeasure (c • w) := by
    refine ⟨?_⟩
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hct.lt_top (measure_lt_top _ _)
  have hνuniv : (c • w) Set.univ = 1 := by
    simp only [Measure.smul_apply, smul_eq_mul, hc]
    exact ENNReal.inv_mul_cancel hZ0 hZt
  have hac : μ ≪ c • w ↔ μ ≪ w := by
    refine ⟨fun h => h.trans Measure.smul_absolutelyContinuous, fun h => h.smul_right hc0⟩
  have hlogc : Real.log c.toReal = -Real.log (w Set.univ).toReal := by
    rw [hc, ENNReal.toReal_inv, Real.log_inv]
  have hint : μ ≪ w → (Integrable (llr μ (c • w)) μ ↔ Integrable (llr μ w) μ) := by
    intro h
    have e := llr_smul_right h c hc0 hct
    rw [integrable_congr e]
    refine ⟨fun h1 => ?_, fun h1 => h1.sub (integrable_const _)⟩
    exact (h1.add (integrable_const (Real.log c.toReal))).congr
      (Filter.Eventually.of_forall fun x => by simp)
  refine ⟨?_, ?_⟩
  · rw [klDiv_ne_top_iff, klDiv_ne_top_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have h1' := hac.1 h1
      exact ⟨h1', (hint h1').1 h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨hac.2 h1, (hint h1).2 h2⟩
  · intro hfin
    obtain ⟨h1, h2⟩ := klDiv_ne_top_iff.1 hfin
    have h3 : Integrable (llr μ (c • w)) μ := (hint h1).2 h2
    have e := llr_smul_right h1 c hc0 hct
    rw [toReal_klDiv (hac.2 h1) h3, toReal_klDiv h1 h2, integral_congr_ae e,
      integral_sub h2 (integrable_const _)]
    simp only [measureReal_def, hνuniv, measure_univ, ENNReal.toReal_one, integral_const, smul_eq_mul,
      mul_one, hlogc]
    ring

/-! ### Geometry: truncation, measure preserving chamber map, weight identity -/

theorem ss5i_log_le_quad {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    Real.log t ≤ (t - 1) - (t - 1) ^ 2 / 2 := by
  have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => (t - 1) - (t - 1) ^ 2 / 2 - Real.log t)
      (1 - (x - 1) - x⁻¹) x := by
    intro x hx
    have h1 : HasDerivAt (fun t : ℝ => t - 1) 1 x := (hasDerivAt_id x).sub_const 1
    have h2 := (h1.pow 2).div_const 2
    have h3 := Real.hasDerivAt_log (ne_of_gt hx)
    have := (h1.sub h2).sub h3
    convert this using 1
    simp
  have hanti : AntitoneOn (fun t : ℝ => (t - 1) - (t - 1) ^ 2 / 2 - Real.log t) (Ioi 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) ?_ ?_ ?_
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · rw [interior_Ioi]; exact fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi]
      intro x hx
      rw [(hd x hx).deriv]
      have hx0 : 0 < x := hx
      have : 1 - (x - 1) - x⁻¹ = -((x - 1) ^ 2 / x) := by field_simp; ring
      rw [this]
      have : 0 ≤ (x - 1) ^ 2 / x := by positivity
      linarith
  have := hanti (show t ∈ Ioi (0 : ℝ) from ht0) (show (1 : ℝ) ∈ Ioi 0 from by norm_num) ht1
  simp at this
  linarith

theorem ss5i_phi_le {ε g : ℝ} (hε : 0 < ε) (hg : 0 < g) : ss5_phiTr ε g ≤ -Real.log g := by
  unfold ss5_phiTr
  split_ifs with h
  · exact le_rfl
  · have hgε : g < ε := not_le.1 h
    have ht0 : 0 < g / ε := div_pos hg hε
    have ht1 : g / ε ≤ 1 := by rw [div_le_one hε]; exact hgε.le
    have hq := ss5i_log_le_quad ht0 ht1
    rw [Real.log_div hg.ne' hε.ne'] at hq
    have e1 : g / ε - 1 = (g - ε) / ε := by field_simp
    rw [e1] at hq
    have e2 : ((g - ε) / ε) ^ 2 / 2 = (g - ε) ^ 2 / (2 * ε ^ 2) := by field_simp
    rw [e2] at hq
    linarith

theorem ss5i_PhiTr_le {N : ℕ} {ε : ℝ} (hε : 0 < ε) {z : Ch5 N} (hz : z ∈ ss5_chamber N) :
    ss5_PhiTr N ε z ≤ ss5_Phi N z := by
  unfold ss5_PhiTr ss5_Phi
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => ?_
  by_cases hkl : k < l
  · simp only [hkl, if_true]
    exact ss5i_phi_le hε (sub_pos.2 (hz k l hkl))
  · simp [hkl]

theorem ss5i_phi_ge {ε : ℝ} (hε : 0 < ε) (g : ℝ) : -|g| - |Real.log ε| ≤ ss5_phiTr ε g := by
  unfold ss5_phiTr
  split_ifs with h
  · have hg : 0 < g := lt_of_lt_of_le hε h
    have := Real.log_le_sub_one_of_pos hg
    rw [abs_of_pos hg]; linarith [abs_nonneg (Real.log ε)]
  · have hs : 0 ≤ -(g - ε) / ε := div_nonneg (by linarith [not_le.1 h]) hε.le
    have h2 : 0 ≤ (g - ε) ^ 2 / (2 * ε ^ 2) := by positivity
    have : -Real.log ε - (g - ε) / ε + (g - ε) ^ 2 / (2 * ε ^ 2) ≥ -Real.log ε := by
      have e : -(g - ε) / ε = -((g - ε) / ε) := by ring
      linarith
    linarith [abs_nonneg g, le_abs_self (Real.log ε)]

theorem ss5i_PhiTr_ge {N : ℕ} {ε : ℝ} (hε : 0 < ε) (z : Ch5 N) :
    -(N : ℝ) * (2 * ‖z‖ + |Real.log ε|) ≤ ss5_PhiTr N ε z := by
  have hterm : ∀ k l : Fin N, -(2 * ‖z‖ + |Real.log ε|) ≤ (if k < l then ss5_phiTr ε (z l - z k) else 0) := by
    intro k l
    by_cases hkl : k < l
    · simp only [hkl, if_true]
      refine le_trans ?_ (ss5i_phi_ge hε _)
      have : |z l - z k| ≤ 2 * ‖z‖ := by
        rw [← ss5t_inner_v k l z]
        calc |inner ℝ (ss5t_v k l) z| ≤ ‖ss5t_v k l‖ * ‖z‖ := abs_real_inner_le_norm _ _
          _ ≤ 2 * ‖z‖ := by gcongr; exact ss5t_norm_v k l
      linarith
    · simp only [hkl, if_false]
      linarith [norm_nonneg z, abs_nonneg (Real.log ε)]
  unfold ss5_PhiTr
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0; simp
  · have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hsum : -((N : ℝ) * ((N : ℝ) * (2 * ‖z‖ + |Real.log ε|))) ≤
        ∑ k : Fin N, ∑ l : Fin N, (if k < l then ss5_phiTr ε (z l - z k) else 0) := by
      calc -((N : ℝ) * ((N : ℝ) * (2 * ‖z‖ + |Real.log ε|)))
          = ∑ k : Fin N, ∑ l : Fin N, (-(2 * ‖z‖ + |Real.log ε|)) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
        _ ≤ _ := Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hterm k l
    calc -(N : ℝ) * (2 * ‖z‖ + |Real.log ε|)
        = 1 / (N : ℝ) * (-((N : ℝ) * ((N : ℝ) * (2 * ‖z‖ + |Real.log ε|)))) := by field_simp
      _ ≤ _ := by gcongr

theorem ss5i_U_ge {N : ℕ} {ε : ℝ} (hε : 0 < ε) (z : Ch5 N) :
    (1 / 8 : ℝ) * ‖z‖ ^ 2 - (8 * (N : ℝ) ^ 2 + (N : ℝ) * |Real.log ε|) ≤ ss5_U N ε z := by
  have := ss5i_PhiTr_ge hε z
  unfold ss5_U
  nlinarith [sq_nonneg (‖z‖ - 8 * N), Nat.cast_nonneg (α := ℝ) N, abs_nonneg (Real.log ε)]

theorem ss5i_toCh_mp {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    MeasurePreserving (ss5_toCh σ : EucConfig 1 N → Ch5 N) volume volume := by
  have h0 : MeasurePreserving (fun x : Euc 1 => x 0) volume volume := by
    have h1 : MeasurePreserving (@WithLp.ofLp 2 (Fin 1 → ℝ)) := PiLp.volume_preserving_ofLp (Fin 1)
    exact (volume_preserving_funUnique (Fin 1) ℝ).comp h1
  have h1 : MeasurePreserving (fun (ξ : EucConfig 1 N) (i : Fin N) => ξ i 0) volume volume :=
    volume_preserving_pi (fun _ => h0)
  have h2 : MeasurePreserving (fun (g : Fin N → ℝ) (k : Fin N) => g (σ k)) volume volume := by
    have := (volume_measurePreserving_piCongrLeft (fun _ : Fin N => ℝ) σ).symm
    have e : (⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℝ) σ).symm) =
        fun (g : Fin N → ℝ) (k : Fin N) => g (σ k) := by
      funext g k
      change (Equiv.piCongrLeft (fun _ : Fin N => ℝ) σ).symm g k = _
      rw [Equiv.piCongrLeft_symm_apply]
    rwa [e] at this
  have h3 := PiLp.volume_preserving_toLp (Fin N)
  exact h3.comp (h2.comp h1)

theorem ss5i_preimage_chamber {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    (ss5_toCh σ) ⁻¹' (ss5_chamber N) = ss5_cone σ := rfl

theorem ss5i_chamber_measurable (N : ℕ) : MeasurableSet (ss5_chamber N) := by
  have hm : ∀ i : Fin N, Measurable fun z : Ch5 N => z i := fun i =>
    (EuclideanSpace.proj i : Ch5 N →L[ℝ] ℝ).continuous.measurable
  have : ss5_chamber N = ⋂ k : Fin N, ⋂ l : Fin N, ⋂ (_ : k < l), {z : Ch5 N | z k < z l} := by
    ext z; simp [ss5_chamber]
  rw [this]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun l => MeasurableSet.iInter fun _ =>
    measurableSet_lt (hm k) (hm l)

theorem ss5i_norm_euc1 (u : Euc 1) : ‖u‖ = |u 0| := by
  rw [EuclideanSpace.norm_eq]; simp [Real.sqrt_sq_eq_abs]

/-- On the cone, the self-similar weight is `e^{-U/θ}` of the chamber coordinates. -/
theorem ss5i_weight_cone {N : ℕ} (σ : Equiv.Perm (Fin N)) {θ : ℝ} {ξ : EucConfig 1 N}
    (hξ : ξ ∈ ss5_cone σ) :
    selfSimWeight 1 0 θ N 0 ξ =
      Real.exp (-(ss5_Phi N (ss5_toCh σ ξ) + (1 / 4 : ℝ) * ‖ss5_toCh σ ξ‖ ^ 2) / θ) := by
  have hnc : ξ ∉ eucCollisionSet 1 N := by
    rintro ⟨i, j, hij, he⟩
    obtain ⟨k, rfl⟩ := σ.surjective i
    obtain ⟨l, rfl⟩ := σ.surjective j
    have hkl : k ≠ l := fun h => hij (by rw [h])
    have h0 : ξ (σ k) 0 = ξ (σ l) 0 := by rw [he]
    rcases lt_or_gt_of_ne hkl with h | h
    · exact (ne_of_lt (hξ k l h)) h0
    · exact (ne_of_gt (hξ l k h)) h0
  unfold selfSimWeight
  rw [if_neg hnc]
  congr 1
  unfold selfSimPotential
  set z : Ch5 N := ss5_toCh σ ξ with hz
  have hzk : ∀ k, z k = ξ (σ k) 0 := fun k => rfl
  have ha : aSelfSim 0 0 = 1 := by simp [aSelfSim]
  rw [ha]
  have hV : ∑ i, ‖ξ i‖ ^ 2 = ‖z‖ ^ 2 := (ss5h_toCh_norm_sq σ ξ).symm
  rw [hV]
  -- the double sum in chamber coordinates
  set h : Fin N → Fin N → ℝ := fun k l => -Real.log |z k - z l| with hh
  have hh0 : ∀ k, h k k = 0 := fun k => by simp [hh]
  have hsymm : ∀ k l, h k l = h l k := fun k l => by simp only [hh]; rw [abs_sub_comm]
  have step1 : ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, rieszKernel 1 0 (ξ i - ξ j) =
      ∑ k : Fin N, ∑ l : Fin N, h k l := by
    rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e1 : ∑ j ∈ Finset.univ.erase (σ k), rieszKernel 1 0 (ξ (σ k) - ξ j) =
        ∑ l ∈ Finset.univ.erase k, h k l := by
      refine Finset.sum_equiv σ.symm (fun l => by simp [Finset.mem_erase, Equiv.symm_apply_eq])
        (fun j _ => ?_)
      simp only [hh, rieszKernel, if_true, ss5i_norm_euc1, PiLp.sub_apply, Equiv.apply_symm_apply, hzk]
    rw [e1]
    exact Finset.sum_erase Finset.univ (f := fun l => h k l) (a := k) (hh0 k)
  have step2 : ∑ k : Fin N, ∑ l : Fin N, h k l =
      2 * ∑ k : Fin N, ∑ l : Fin N, (if k < l then -Real.log (z l - z k) else 0) := by
    have hsplit : ∀ k l : Fin N, h k l =
        (if k < l then -Real.log (z l - z k) else 0) + (if l < k then -Real.log (z k - z l) else 0) := by
      intro k l
      rcases lt_trichotomy k l with hkl | hkl | hkl
      · have : 0 < z l - z k := sub_pos.2 (hξ k l hkl)
        simp only [hh, hkl, not_lt.2 hkl.le, if_true, if_false, add_zero]
        rw [abs_sub_comm, abs_of_pos this]
      · subst hkl; simp [hh0]
      · have : 0 < z k - z l := sub_pos.2 (hξ l k hkl)
        simp only [hh, hkl, not_lt.2 hkl.le, if_true, if_false, zero_add]
        rw [abs_of_pos this]
    simp only [hsplit, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun k l => if l < k then -Real.log (z k - z l) else 0)]
    ring
  rw [step1, step2]
  unfold ss5_Phi
  generalize (∑ k : Fin N, ∑ l : Fin N, (if k < l then -Real.log (z l - z k) else 0)) = S'
  have e : (1 / (2 * (N : ℝ))) * (2 * S') = (1 / (N : ℝ)) * S' := by
    rcases eq_or_ne (N : ℝ) 0 with h0 | h0
    · simp [h0]
    · field_simp
  rw [e]
  ring

/-! ### Partition function of the regularised weight, domination, assembly -/

theorem ss5i_gauss_ch (N : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun z : Ch5 N => Real.exp (-c * ‖z‖ ^ 2)) := by
  have := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Ch5 N) (b := (c : ℂ))
    (by simpa using hc) 0 0).norm
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  simp
  left
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

theorem ss5i_U_meas (N : ℕ) {ε : ℝ} (hε : 0 < ε) : Measurable (ss5_U N ε) :=
  (ss5t_contDiff_U hε).continuous.measurable

theorem ss5i_wU_meas (N : ℕ) {ε θ : ℝ} (hε : 0 < ε) :
    Measurable fun z : Ch5 N => ENNReal.ofReal (Real.exp (-ss5_U N ε z / θ)) :=
  (Real.measurable_exp.comp ((ss5i_U_meas N hε).neg.div_const θ)).ennreal_ofReal

theorem ss5i_partition {N : ℕ} {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) :
    ss5_partition θ (ss5_U N ε) ≠ 0 ∧ ss5_partition θ (ss5_U N ε) ≠ ⊤ := by
  have hm := ss5i_wU_meas N (θ := θ) hε
  constructor
  · unfold ss5_partition
    refine ((lintegral_pos_iff_support hm).2 ?_).ne'
    have : Function.support (fun z : Ch5 N => ENNReal.ofReal (Real.exp (-ss5_U N ε z / θ))) =
        Set.univ := by
      ext z; simp [Real.exp_pos]
    rw [this]; exact Measure.measure_univ_pos.2 (NeZero.ne _)
  · unfold ss5_partition
    set K : ℝ := Real.exp ((8 * (N : ℝ) ^ 2 + (N : ℝ) * |Real.log ε|) / θ) with hK
    have hc : 0 < 1 / (8 * θ) := by positivity
    have hG := ((ss5i_gauss_ch N hc).const_mul K).lintegral_lt_top
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun z => ?_) hG)
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := ss5i_U_ge hε z
    rw [hK, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h2 : -ss5_U N ε z / θ ≤
        -((1 / 8 : ℝ) * ‖z‖ ^ 2 - (8 * (N : ℝ) ^ 2 + (N : ℝ) * |Real.log ε|)) / θ := by
      apply div_le_div_of_nonneg_right _ hθ.le
      linarith
    refine h2.trans (le_of_eq ?_)
    field_simp
    ring

/-- Domination of the pushed-forward weight on the chamber by the regularised weight. -/
theorem ss5i_dom {N : ℕ} (σ : Equiv.Perm (Fin N)) {θ ε : ℝ} (hθ : 0 < θ) (hε : 0 < ε) :
    ((volume.withDensity fun ξ : EucConfig 1 N =>
        ENNReal.ofReal (selfSimWeight 1 0 θ N 0 ξ)).map (ss5_toCh σ)).restrict (ss5_chamber N) ≤
      (volume : Measure (Ch5 N)).withDensity
        fun z => ENNReal.ofReal (Real.exp (-ss5_U N ε z / θ)) := by
  have hT : Measurable (ss5_toCh σ : EucConfig 1 N → Ch5 N) := (ss5i_toCh_mp σ).measurable
  have hC := ss5i_chamber_measurable N
  refine Measure.le_iff.2 fun A hA => ?_
  have hAC : MeasurableSet (A ∩ ss5_chamber N) := hA.inter hC
  have hpre : MeasurableSet ((ss5_toCh σ) ⁻¹' (A ∩ ss5_chamber N)) := hT hAC
  rw [Measure.restrict_apply hA, Measure.map_apply hT hAC, withDensity_apply _ hpre,
    withDensity_apply _ hA]
  calc ∫⁻ x in (ss5_toCh σ) ⁻¹' (A ∩ ss5_chamber N), ENNReal.ofReal (selfSimWeight 1 0 θ N 0 x)
      ≤ ∫⁻ x in (ss5_toCh σ) ⁻¹' (A ∩ ss5_chamber N),
          (fun z : Ch5 N => ENNReal.ofReal (Real.exp (-ss5_U N ε z / θ))) (ss5_toCh σ x) := by
        refine setLIntegral_mono' hpre fun x hx => ?_
        have hxc : x ∈ ss5_cone σ := hx.2
        simp only
        rw [ss5i_weight_cone σ hxc]
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
        have h1 := ss5i_PhiTr_le (N := N) hε hx.2
        unfold ss5_U
        apply div_le_div_of_nonneg_right _ hθ.le
        linarith
    _ = ∫⁻ z in A ∩ ss5_chamber N, ENNReal.ofReal (Real.exp (-ss5_U N ε z / θ)) :=
        (ss5i_toCh_mp σ).setLIntegral_comp_preimage hAC (ss5i_wU_meas N hε)
    _ ≤ ∫⁻ z in A, ENNReal.ofReal (Real.exp (-ss5_U N ε z / θ)) :=
        lintegral_mono_set Set.inter_subset_left

/-- **9 (initial term).**  Statement of `HRS.MP.SelfSimP5.ss5_initial_bound`. -/
theorem ss5_initial_bound_proof (N : ℕ) (hN : 2 ≤ N) (invβ : ℝ) (hβ : 0 < invβ)
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q] (σ : Equiv.Perm (Fin N))
    {Y₀ : Ω → EucConfig 1 N} (hY₀ : Measurable Y₀) (h0 : ∀ᵐ ζ ∂Q, Y₀ ζ ∈ ss5_cone σ) {ε : ℝ} (hε : 0 < ε) :
    ss5_ent invβ (ss5_U N ε) (Q.map fun ζ => ss5_toCh σ (Y₀ ζ)) ≤
      gibbsEntropyW (selfSimWeight 1 0 invβ N 0) (law Q Y₀) := by
  have hT : Measurable (ss5_toCh σ : EucConfig 1 N → Ch5 N) := (ss5i_toCh_mp σ).measurable
  have hC := ss5i_chamber_measurable N
  set θ := invβ with hθdef
  set G := selfSimWeight 1 0 θ N 0 with hG
  set μ : Measure (EucConfig 1 N) := law Q Y₀ with hμ
  haveI : IsProbabilityMeasure μ := inferInstanceAs (IsProbabilityMeasure (Q.map Y₀))
  have hmap : Q.map (fun ζ => ss5_toCh σ (Y₀ ζ)) = μ.map (ss5_toCh σ) :=
    (Measure.map_map hT hY₀).symm
  rw [hmap]
  haveI : IsProbabilityMeasure (μ.map (ss5_toCh σ)) := by
    haveI : IsProbabilityMeasure μ := inferInstance
    infer_instance
  set wG : Measure (EucConfig 1 N) := volume.withDensity fun ξ => ENNReal.ofReal (G ξ) with hwG
  set wU : Measure (Ch5 N) :=
    volume.withDensity fun z => ENNReal.ofReal (Real.exp (-ss5_U N ε z / θ)) with hwU
  have hZG : gibbsPartitionW G = wG Set.univ := by
    rw [hwG, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; rfl
  have hZU : ss5_partition θ (ss5_U N ε) = wU Set.univ := by
    rw [hwU, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; rfl
  have hrefG : gibbsRefW G = (wG Set.univ)⁻¹ • wG := by
    unfold gibbsRefW; rw [hZG]
  have hrefU : ss5_ref θ (ss5_U N ε) = (wU Set.univ)⁻¹ • wU := by
    unfold ss5_ref; rw [hZU]
  unfold gibbsEntropyW ss5_ent
  change ((klDiv (μ.map (ss5_toCh σ)) (ss5_ref θ (ss5_U N ε)) : ℝ≥0∞) : EReal) -
      ((Real.log (ss5_partition θ (ss5_U N ε)).toReal : ℝ) : EReal) ≤
    ((klDiv μ (gibbsRefW G) : ℝ≥0∞) : EReal) - ((Real.log (gibbsPartitionW G).toReal : ℝ) : EReal)
  rw [hrefG, hrefU, hZG, hZU]
  by_cases hK : klDiv μ ((wG Set.univ)⁻¹ • wG) = ⊤
  · rw [hK]
    simp [EReal.top_sub_coe]
  -- Z_G is finite and nonzero because the normalised reference is not zero
  have hZG0 : wG Set.univ ≠ 0 ∧ wG Set.univ ≠ ⊤ := by
    constructor
    · intro h0'
      have : wG = 0 := Measure.measure_univ_eq_zero.1 h0'
      apply hK
      rw [this, smul_zero]
      exact klDiv_zero_right
    · intro htop
      apply hK
      rw [htop, ENNReal.inv_top, zero_smul]
      exact klDiv_zero_right
  haveI : IsFiniteMeasure wG := ⟨lt_top_iff_ne_top.2 hZG0.2⟩
  obtain ⟨hZU0, hZUt⟩ := ss5i_partition (N := N) hε hβ
  rw [hZU] at hZU0 hZUt
  haveI : IsFiniteMeasure wU := ⟨lt_top_iff_ne_top.2 hZUt⟩
  obtain ⟨hn1, hn2⟩ := ss5i_norm (μ := μ) (w := wG) hZG0.1
  have hKw : klDiv μ wG ≠ ⊤ := hn1.1 hK
  have hμac : μ ≪ wG := (klDiv_ne_top_iff.1 hKw).1
  -- the comparison
  have hcone : MeasurableSet (ss5_cone σ) := by
    rw [← ss5i_preimage_chamber]; exact hT hC
  have hμs : (μ.map (ss5_toCh σ)) (ss5_chamber N)ᶜ = 0 := by
    rw [Measure.map_apply hT hC.compl, Set.preimage_compl, ss5i_preimage_chamber, hμ,
      Measure.map_apply hY₀ hcone.compl]
    exact ae_iff.1 h0
  have hμ' : μ.map (ss5_toCh σ) ≪ wG.map (ss5_toCh σ) := hμac.map hT
  have hdp : klDiv (μ.map (ss5_toCh σ)) (wG.map (ss5_toCh σ)) ≤ klDiv μ wG :=
    klDiv_map_le μ wG hT
  have hcmp := ss5i_klDiv_cmp (μ := μ.map (ss5_toCh σ)) (ν₁ := wG.map (ss5_toCh σ)) (ν₂ := wU) hC hμs
    hμ' (ss5i_dom σ hβ hε)
  have hmass : (wG.map (ss5_toCh σ)) Set.univ = wG Set.univ := by
    rw [Measure.map_apply hT MeasurableSet.univ]; rfl
  rw [hmass] at hcmp
  have hle : klDiv (μ.map (ss5_toCh σ)) wU + wG Set.univ ≤ klDiv μ wG + wU Set.univ :=
    hcmp.trans (by gcongr)
  have hKU : klDiv (μ.map (ss5_toCh σ)) wU ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hKw, hZUt⟩) (le_self_add.trans hle)
  obtain ⟨hm1, hm2⟩ := ss5i_norm (μ := μ.map (ss5_toCh σ)) (w := wU) hZU0
  have hKU' := hm1.2 hKU
  have e1 := hm2 hKU
  have e2 := hn2 hKw
  rw [← EReal.coe_ennreal_toReal hKU', ← EReal.coe_ennreal_toReal hK, ← EReal.coe_sub,
    ← EReal.coe_sub, EReal.coe_le_coe_iff, e1, e2]
  have h3 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hKw, hZUt⟩) hle
  rw [ENNReal.toReal_add hKU hZG0.2, ENNReal.toReal_add hKw hZUt] at h3
  linarith

example := (@ss5_initial_bound_proof : type_of% @HRS.MP.SelfSimP5.ss5_initial_bound)

end HRS.MP.SelfSimP5Impl
