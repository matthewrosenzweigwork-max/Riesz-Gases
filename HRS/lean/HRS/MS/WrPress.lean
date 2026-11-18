import HRS.MS.WrPressAux2

/-!
# HRS.MS.WrPress -- proof of the pressure bound of Proposition S3.1 (WR-8)

Packet WR-8 of `docs/SUPP_FOUND_PACKETS.md` (Track D), namespace `HRS.MS.Wr`.

* `wr8_fam_pos`: for `0 < s < d` the heat split `|z|^{-s} = qTau + kTau` (`τ` depending on `ε`) gives the data
  `Wr8Split` with `E0 = 1`, `P = kTau`, `Kw = κ = kTau 0`, `m = 0`.
* `wr8_fam_zero`: for `s = 0` the logarithmic split `-log|z| = qTauLog + kTauLog` (`τ ≤ 1`, uniform envelope
  `q_τ ≤ q_1 ≤ 1 + W_0`, `Kw = 1/(2τ) + τ/2`, `m = Kw + 2L`, `κ = kTauLog 0` from `kTauLog_diag_bound`).
* `euclidean_pressure_pos`: the case `s > 0` of `HRS.Whole.euclidean_pressure`.
* `euclidean_pressure_proof : type_of% @HRS.Whole.euclidean_pressure`: the full statement (`GibbsWellDefined`
  kept in the conclusion); tie in `HRS/MS/WrPressTie.lean`.

Statement adjustments: none.  The generic core `wr8_core` (`WrPressAux2`) handles both cases through `Wr8Split`.

Helper lemmas carry the prefix `wr8_`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

open HRS.Whole HRS.MS.Psd

variable {d N : ℕ}

/-! ### `s > 0`: the heat split -/

theorem wr8_qTau_meas {s τ : ℝ} : Measurable (qTau d s τ) := by
  unfold qTau
  have hm : Measurable (fun p : Euc d × ℝ => psd3_F d s p.2 p.1) :=
    (psd3_F_meas (d := d) s).comp measurable_swap
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) τ))).measurable

theorem wr8_qTau_even {s τ : ℝ} (z : Euc d) : qTau d s τ (-z) = qTau d s τ z := by
  unfold qTau psd3_F heatKerE
  simp only [norm_neg]

theorem wr8_kTau_bound {s : ℝ} (hs : 0 < s) {τ : ℝ} (hτ : 0 < τ) {μ : Measure (Euc d)}
    [IsFiniteMeasure μ] (x : Euc d) : ∀ᵐ y ∂μ, ‖kTau d s τ (x - y)‖ ≤ kTau d s τ 0 :=
  Filter.Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs]; exact wr7_kTau_abs_le hs hτ _

theorem wr8_fam_pos (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) (L ε : ℝ) (hε : 0 < ε) :
    ∃ (q P : Euc d → ℝ) (Kw κ m : ℝ), Wr8Split d s L 1 ε q P Kw κ m := by
  have hα : 0 < ((d : ℝ) - s) / 2 := by linarith
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = aDS d s / (((d : ℝ) - s) / 2) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by
    rw [hcdef]; exact div_nonneg (psd3_aDS_pos hs).le hα.le
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = (ε / (c + 1)) ^ (1 / (((d : ℝ) - s) / 2)) := ⟨_, rfl⟩
  have hτ : 0 < τ := by rw [hτdef]; exact Real.rpow_pos_of_pos (by positivity) _
  have hτα : τ ^ (((d : ℝ) - s) / 2) = ε / (c + 1) := by
    rw [hτdef, ← Real.rpow_mul (by positivity), one_div_mul_cancel hα.ne', Real.rpow_one]
  obtain ⟨hqi, hqI⟩ := qTau_integrable_integral hs hsd hτ
  have hqε : ∫ z, qTau d s τ z ≤ ε := by
    rw [hqI, ← hcdef, hτα]
    calc c * (ε / (c + 1)) = ε * (c / (c + 1)) := by ring
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left (by rw [div_le_one (by positivity)]; linarith) hε.le
      _ = ε := mul_one _
  have hk0 : 0 ≤ kTau d s τ 0 := kTau_nonneg hs hτ 0
  have hkm : Measurable (fun p : Euc d × Euc d => kTau d s τ (p.1 - p.2)) :=
    (kTau_continuous hs hτ).measurable.comp (measurable_fst.sub measurable_snd)
  have hW : ∀ z : Euc d, rieszWeight s z = rieszKernel d s z := by
    intro z; unfold rieszWeight rieszKernel; rw [if_neg hs.ne', if_neg hs.ne']
  refine ⟨qTau d s τ, kTau d s τ, kTau d s τ 0, kTau d s τ 0, 0, ?_⟩
  refine ⟨wr8_qTau_meas, wr8_qTau_even, qTau_nonneg hs, hqi, hqε, ?_, ?_, ?_, hk0, ?_, ?_, ?_⟩
  · intro z hz; exact riesz_heat_split hs hτ hz
  · intro z hz
    have h1 := riesz_heat_split hs hτ hz
    have h2 := kTau_nonneg hs hτ z
    rw [hW]; linarith
  · intro z hz
    have h1 := riesz_heat_split hs hτ hz
    have h2 := kTau_le_zero hs hτ z
    rw [hW]; linarith
  · intro μ _ _
    refine ⟨?_, fun x => ?_, ?_⟩
    · exact hkm
    · exact Integrable.of_bound
        ((kTau_continuous hs hτ).measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
        (kTau d s τ 0) (wr8_kTau_bound hs hτ x)
    · exact Integrable.of_bound hkm.aestronglyMeasurable (kTau d s τ 0)
        (Filter.Eventually.of_forall fun p => by
          rw [Real.norm_eq_abs]; exact wr7_kTau_abs_le hs hτ _)
  · intro μ _ _
    simp only [neg_zero]
    exact integral_nonneg fun p => kTau_nonneg hs hτ _
  · intro μ _ _ N hN X
    have := kTau_diag_bound hs hτ hN μ X
    linarith


/-- The case `s > 0` of `HRS.Whole.euclidean_pressure` (the `s = 0` hypothesis is vacuous). -/
theorem euclidean_pressure_pos (hd : 2 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d)
    (M L bm bp B : ℝ) (hbm : 0 < bm) :
    ∃ θ₀ > 0, ∃ C : ℝ, ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      (s = 0 → HasLogMoment (HRS.Whole.withDensityReal ρ) L) →
      ∀ h : Euc d → Euc d → ℝ, IsBoundedPairKernel s B h →
      ∀ N, 2 ≤ N → ∀ b ∈ Set.Icc bm bp, ∀ θ : ℝ, |θ| ≤ θ₀ →
        GibbsWellDefined (fun x y => rieszKernel d s (x - y) - θ * h x y) N b
          (HRS.Whole.withDensityReal ρ) ∧
        |Real.log (pairNormalizer (fun x y => rieszKernel d s (x - y) - θ * h x y) N b
          (HRS.Whole.withDensityReal ρ))| ≤ C * N * deltaN d s N :=
  wr8_core hd hs.le hsd M L bm bp B 1 hbm zero_le_one
    (fun ε hε => wr8_fam_pos (by omega) hs hsd L ε hε)


/-! ### `s = 0`: the logarithmic heat split -/

theorem wr8_qLog_meas {τ : ℝ} : Measurable (qTauLog d τ) := by
  unfold qTauLog
  have hm : Measurable (fun p : Euc d × ℝ => Real.exp (-(‖p.1‖ ^ 2 * p.2)) / p.2) :=
    (Real.measurable_exp.comp (((measurable_norm.comp measurable_fst).pow_const 2).mul measurable_snd).neg).div
      measurable_snd
  exact measurable_const.mul
    (hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi (1 / τ)))).measurable

theorem wr8_qLog_even {τ : ℝ} (z : Euc d) : qTauLog d τ (-z) = qTauLog d τ z := by
  unfold qTauLog
  simp only [norm_neg]

/-- `q_τ ≤ q_1` for `τ ≤ 1` (the tail integral over `(1/τ, ∞) ⊆ (1, ∞)`), off the origin. -/
theorem wr8_qLog_mono {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {z : Euc d} (hz : z ≠ 0) :
    qTauLog d τ z ≤ qTauLog d 1 z := by
  have hn : 0 < ‖z‖ ^ 2 := by have := norm_pos_iff.2 hz; positivity
  unfold qTauLog
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have h1 : IntegrableOn (fun u : ℝ => Real.exp (-(‖z‖ ^ 2 * u)) / u) (Ioi (1 / (1 : ℝ))) :=
    psd3_tail_integrableOn hn one_pos
  have hsub : Ioi (1 / τ) ⊆ Ioi (1 / (1 : ℝ)) := by
    refine Ioi_subset_Ioi ?_
    rw [div_one]
    rw [le_div_iff₀ hτ]; linarith
  refine setIntegral_mono_set h1 ?_ (Filter.Eventually.of_forall hsub)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu' : 1 / (1 : ℝ) < u := hu
  have : 0 < u := lt_trans (by norm_num) hu'
  positivity

/-- The uniform envelope `q_τ(z) ≤ 1 + W_0(z)` for `0 < τ ≤ 1`, `z ≠ 0`. -/
theorem wr8_qLog_env {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {z : Euc d} (hz : z ≠ 0) :
    qTauLog d τ z ≤ 1 * (1 + rieszWeight 0 z) := by
  have hW0 : 0 ≤ rieszWeight 0 z := wr3_rieszWeight_nonneg 0 z
  refine (wr8_qLog_mono hτ hτ1 hz).trans ?_
  rcases le_total 1 ‖z‖ with h | h
  · have := psd3_q_le (d := d) one_pos h
    linarith
  · have hk := riesz_log_heat_split (d := d) one_pos hz
    have hq0 := qTauLog_nonneg (d := d) one_pos z
    have hku := kTauLog_abs_le_unit (d := d) one_pos h
    have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hlog : Real.log ‖z‖ ≤ 0 := Real.log_nonpos hn.le h
    have hW : rieszWeight 0 z = -Real.log ‖z‖ := by
      unfold rieszWeight; rw [if_pos rfl]; exact max_eq_left (by linarith)
    have hr : rieszKernel d 0 z = -Real.log ‖z‖ := by simp [rieszKernel]
    rw [abs_le] at hku
    norm_num at hku
    linarith [hku.1, hku.2]

theorem wr8_kLog_bound {τ : ℝ} (hτ : 0 < τ) {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    (hlog : Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) μ) :
    -(1 / (2 * τ) + τ / 2 + 2 * ∫ x, Real.log (2 + ‖x‖) ∂μ) ≤
      ∫ p : Euc d × Euc d, kTauLog d τ (p.1 - p.2) ∂(μ.prod μ) := by
  set M : Euc d → ℝ := fun x => Real.log (2 + ‖x‖) with hM
  have hk := wr7_kTauLog_int hτ hlog hlog
  have h1 : Integrable (fun z : Euc d × Euc d => M z.1 * 1) (μ.prod μ) :=
    hlog.mul_prod (integrable_const (1 : ℝ) : Integrable (fun _ : Euc d => (1 : ℝ)) μ)
  have h2 : Integrable (fun z : Euc d × Euc d => 1 * M z.2) (μ.prod μ) :=
    (integrable_const (1 : ℝ) : Integrable (fun _ : Euc d => (1 : ℝ)) μ).mul_prod hlog
  have hA : Integrable (fun z : Euc d × Euc d => (1 / (2 * τ) + τ / 2 + M z.1 * 1) + 1 * M z.2) (μ.prod μ) :=
    ((integrable_const _).add h1).add h2
  have hmono : ∫ z : Euc d × Euc d, -((1 / (2 * τ) + τ / 2 + M z.1 * 1) + 1 * M z.2) ∂(μ.prod μ) ≤
      ∫ p : Euc d × Euc d, kTauLog d τ (p.1 - p.2) ∂(μ.prod μ) := by
    refine integral_mono hA.neg hk (fun z => ?_)
    have h1 := kTauLog_abs_le hτ (z.1 - z.2)
    have h2 := psd3_log_sub_le z.1 z.2
    have := neg_abs_le (kTauLog d τ (z.1 - z.2))
    simp only [hM] at *
    linarith
  refine le_trans (le_of_eq ?_) hmono
  have e1 : ∫ z : Euc d × Euc d, ((1 / (2 * τ) + τ / 2 + M z.1 * 1) + 1 * M z.2) ∂(μ.prod μ) =
      (∫ z : Euc d × Euc d, (1 / (2 * τ) + τ / 2 + M z.1 * 1) ∂(μ.prod μ)) +
        ∫ z : Euc d × Euc d, 1 * M z.2 ∂(μ.prod μ) :=
    integral_add ((integrable_const _).add h1) h2
  have e2 : ∫ z : Euc d × Euc d, (1 / (2 * τ) + τ / 2 + M z.1 * 1) ∂(μ.prod μ) =
      (∫ _z : Euc d × Euc d, (1 / (2 * τ) + τ / 2) ∂(μ.prod μ)) +
        ∫ z : Euc d × Euc d, M z.1 * 1 ∂(μ.prod μ) :=
    integral_add (integrable_const _) h1
  have e3 := integral_prod_mul (μ := μ) (ν := μ) M (fun _ => (1 : ℝ))
  have e4 := integral_prod_mul (μ := μ) (ν := μ) (fun _ => (1 : ℝ)) M
  rw [integral_neg, e1, e2, e3, e4]
  simp [Measure.real]
  ring

theorem wr8_fam_zero (hd : 1 ≤ d) (L ε : ℝ) (hε : 0 < ε) :
    ∃ (q P : Euc d → ℝ) (Kw κ m : ℝ), Wr8Split d 0 L 1 ε q P Kw κ m := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = Real.pi ^ ((d : ℝ) / 2) / d := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  obtain ⟨τ0, hτ0def⟩ : ∃ τ0 : ℝ, τ0 = (ε / (c + 1)) ^ (2 / (d : ℝ)) := ⟨_, rfl⟩
  have hτ0 : 0 < τ0 := by rw [hτ0def]; exact Real.rpow_pos_of_pos (by positivity) _
  have hτ0α : τ0 ^ ((d : ℝ) / 2) = ε / (c + 1) := by
    rw [hτ0def, ← Real.rpow_mul (by positivity)]
    rw [show 2 / (d : ℝ) * ((d : ℝ) / 2) = 1 by field_simp, Real.rpow_one]
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = min 1 τ0 := ⟨_, rfl⟩
  have hτ : 0 < τ := by rw [hτdef]; exact lt_min one_pos hτ0
  have hτ1 : τ ≤ 1 := by rw [hτdef]; exact min_le_left _ _
  have hτα : τ ^ ((d : ℝ) / 2) ≤ ε / (c + 1) := by
    rw [← hτ0α]
    exact Real.rpow_le_rpow hτ.le (by rw [hτdef]; exact min_le_right _ _) (by positivity)
  obtain ⟨hqi, hqI⟩ := qTauLog_integrable_integral hd hτ
  have hqε : ∫ z, qTauLog d τ z ≤ ε := by
    rw [hqI]
    have e : Real.pi ^ ((d : ℝ) / 2) * τ ^ ((d : ℝ) / 2) / d = c * τ ^ ((d : ℝ) / 2) := by
      rw [hcdef]; ring
    rw [e]
    calc c * τ ^ ((d : ℝ) / 2) ≤ c * (ε / (c + 1)) := mul_le_mul_of_nonneg_left hτα hc0
      _ = ε * (c / (c + 1)) := by ring
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left (by rw [div_le_one (by positivity)]; linarith) hε.le
      _ = ε := mul_one _
  have hKw : 0 ≤ 1 / (2 * τ) + τ / 2 := by positivity
  have hW0 : ∀ z : Euc d, rieszWeight 0 z = max (-Real.log ‖z‖) 0 := by
    intro z; unfold rieszWeight; rw [if_pos rfl]
  refine ⟨qTauLog d τ, kTauLog d τ, 1 / (2 * τ) + τ / 2, kTauLog d τ 0,
    1 / (2 * τ) + τ / 2 + 2 * L, ?_⟩
  refine ⟨wr8_qLog_meas, wr8_qLog_even, qTauLog_nonneg hτ, hqi, hqε, ?_, ?_, ?_, hKw, ?_, ?_, ?_⟩
  · intro z hz; exact riesz_log_heat_split hτ hz
  · intro z hz; exact wr8_qLog_env hτ hτ1 hz
  · intro z hz
    have hq0 := qTauLog_nonneg (d := d) hτ z
    rcases le_total ‖z‖ 1 with h | h
    · have hk := riesz_log_heat_split (d := d) hτ hz
      have hku := kTauLog_abs_le_unit hτ h
      have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
      have hlog : Real.log ‖z‖ ≤ 0 := Real.log_nonpos hn.le h
      have hr : rieszKernel d 0 z = -Real.log ‖z‖ := by simp [rieszKernel]
      rw [hW0, max_eq_left (by linarith)]
      rw [abs_le] at hku
      linarith [hku.1, hku.2]
    · have hn : 0 < ‖z‖ := by linarith
      have hlog : 0 ≤ Real.log ‖z‖ := Real.log_nonneg h
      rw [hW0, max_eq_right (by linarith)]
      linarith
  · intro μ _ hlog
    have hl := (hlog rfl).1
    refine ⟨(kTauLog_continuous hτ).measurable.comp (measurable_fst.sub measurable_snd), fun x => ?_,
      kTauLog_pair_integrable hτ μ hl⟩
    exact kTauLog_rows_integrable hτ μ hl x
  · intro μ _ hlog
    have hl := hlog rfl
    have := wr8_kLog_bound hτ hl.1
    have h2 := hl.2
    linarith
  · intro μ _ hlog N hN X
    have := kTauLog_diag_bound hτ hN μ (hlog rfl).1 X
    linarith


/-- **Proposition S3.1, main bound** (`HRS.Whole.euclidean_pressure`): proof by the heat split
`g = q_τ + k_τ`, the perturbation `q_θ = q_τ - θ h̃ + |θ| D`, the Euclidean weak reference
(`weak_reference_pressure_pairNormalizer_E`), the diagonal bound (`kTau_diag_bound`, `kTauLog_diag_bound`) and the
Jensen lower bound.  Constants `θ₀, C` are chosen before `ρ, h`. -/
theorem euclidean_pressure_proof : type_of% @HRS.Whole.euclidean_pressure := by
  intro d s hd hs0 hsd M L bm bp B hbm hb
  rcases hs0.eq_or_lt with h0 | hpos
  · subst h0
    exact wr8_core hd le_rfl hsd M L bm bp B 1 hbm zero_le_one
      (fun ε hε => wr8_fam_zero (by omega) L ε hε)
  · exact euclidean_pressure_pos hd hpos hsd M L bm bp B hbm

end HRS.MS.Wr
