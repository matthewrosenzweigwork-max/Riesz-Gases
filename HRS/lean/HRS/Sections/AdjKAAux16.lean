import HRS.Sections.AdjKAAux15

/-!
# ADJKA part 16: BCONV (`adjk_conv_kolmogorov`)
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.AdjK

open HRS HRS.Uniform HRS.Uniform.Q54 HRS.Uniform.Q48b

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem adjka_bconv (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    (j : ℕ) (hj : (d : ℝ) + 2 ≤ j) (m : ℝ) (hjm : (j : ℝ) + 2 ≤ m) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ mΩ) (μ : ℝ → Ω → Measure (Torus d)) (_ : ∀ r ω, IsProbabilityMeasure (μ r ω))
      (M : ℝ → Ω → NegSobolev d m),
      IsHilbertMartingaleWithCovariation P ℱ T M (fun r ω => covForm m β⁻¹ (μ r ω)) →
      ∀ Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m,
        IsDualEvolution htr.dyn ρ m Vev → (∀ T' : ℝ, 0 ≤ T' → IsPlainEvolution Vev T') →
        ∀ Z : ℝ → Ω → NegSobolev d m,
          (∀ t ∈ Set.Icc (0 : ℝ) T,
            IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) M 0 t (Z t)) →
          (∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 T)) → (∀ t, Measurable (Z t)) →
          ∫⁻ ω, ⨆ t ∈ ratIcc 0 T, adjkEnergy (j : ℝ) m (Z t ω) ∂P ≤ ENNReal.ofReal C ∧
          ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
            ∫⁻ ω, ‖Z t ω - Z s ω‖ₑ ^ (4 : ℝ) ∂P ≤ ENNReal.ofReal (C * |t - s| ^ 2) := by
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hm2 : (d : ℝ) / 2 + 2 < m := by linarith
  have hq : 0 ≤ β⁻¹ := (inv_pos.2 htr.hβ).le
  obtain ⟨C₁, hC₁, hG2⟩ := adjka_energy_moment hd htr j hj m hjm T hT 2 le_rfl
  obtain ⟨C₄, hC₄, hG4⟩ := adjka_energy_moment hd htr j hj m hjm T hT 4 (by norm_num)
  obtain ⟨CA, hCA, hA2⟩ := adjk_evolution_increment_proof hd htr j hj
  obtain ⟨Vj, hVj, -, -, -⟩ := adjka_levelInput_traj hd htr (j : ℝ)
  obtain ⟨Vm', hVm', hVmp', hB1⟩ := adjk_evolution_moment_proof hd htr m 4 (by norm_num)
  obtain ⟨CB4, hCB4, hB1'⟩ := hB1 T hT
  set Bm : ℝ := 4 * β⁻¹ * d * Q14.q14S d (m - 1) with hBm
  have hBm0 : 0 ≤ Bm := by
    have := Q14.q14S_nonneg d (m - 1)
    positivity
  set C2 : ℝ := 8 * (CA ^ 4 * T ^ 2 * C₄ + CB4 * Bm ^ 2) with hC2
  have hC20 : 0 ≤ C2 := by positivity
  refine ⟨max C₁ C2, le_max_of_le_left hC₁, ?_⟩
  intro Ω mΩ P _ ℱ μ hμ M hM Vev hVev hplain Z hZ hZc hZm
  refine ⟨?_, ?_⟩
  · have h := hG2 Ω P ℱ μ hμ M hM Vev hVev Z hZ (fun t _ => (hZm t).aemeasurable)
    rw [show (2 : ℝ) / 2 = 1 by norm_num] at h
    simp only [ENNReal.rpow_one] at h
    exact h.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · have key : ∀ s' t' : ℝ, s' ∈ Set.Icc (0 : ℝ) T → t' ∈ Set.Icc (0 : ℝ) T → s' ≤ t' →
        ∫⁻ ω, ‖Z t' ω - Z s' ω‖ₑ ^ (4 : ℝ) ∂P ≤ ENNReal.ofReal (C2 * (t' - s') ^ 2) := by
      intro s' t' hs' ht' hle
      rcases hle.eq_or_lt with heq | hlt
      · subst heq
        simp
      set h : ℝ := t' - s' with hh
      have hh0 : 0 < h := sub_pos.2 hlt
      have hhT : h ≤ T := by linarith [hs'.1, ht'.2]
      have hst : s' + h = t' := by rw [hh]; ring
      have hMt : IsHilbertMartingaleWithCovariation P ℱ (s' + h) M (fun r ω => covForm m β⁻¹ (μ r ω)) := by
        rw [hst]; exact adjka_isHMC_mono hM ht'.2
      obtain ⟨Z', hZ'conv, -, hZ'meas, hZ'bd⟩ := hB1' Ω P ℱ s' h hs'.1 hh0 hhT M _ hMt
      have ht'I : t' ∈ Set.Icc s' (s' + h) := ⟨hle, hst.symm.le⟩
      have hZ'c : IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) M s' t' (Z' t') := by
        refine adjka_isStochConv_congr_ev ?_ (hZ'conv t' ht'I)
        intro r hr1 hr2
        exact adjka_dual_unique hVm' hVev (hs'.1.trans hr1) hr2
      have hcoc := (hplain t' ht'.1).2.1
      have hMt' : ∀ τ ∈ Set.Icc (0 : ℝ) t', AEStronglyMeasurable (M τ) P := fun τ hτ =>
        (hM.sq_int τ ⟨hτ.1, hτ.2.trans ht'.2⟩).aestronglyMeasurable
      have hsplit := adjka_splitting hs'.1 hle hcoc hMt' (hZ t' ht') (hZ s' hs') hZ'c
        (hZm t').aemeasurable (hZm s').aemeasurable (hZ'meas t' ht'I)
      set G : Ω → ℝ≥0∞ := fun ω => ⨆ q ∈ ratIcc 0 T, adjkEnergy (j : ℝ) m (Z q ω) with hG
      have hGm : AEMeasurable G P :=
        AEMeasurable.biSup (ratIcc 0 T) (ratIcc_countable 0 T)
          (fun q hq => ((adjkEnergy_measurable (j : ℝ) m).comp (hZm q)).aemeasurable)
      have hG4'' : ∫⁻ ω, G ω ^ 2 ∂P ≤ ENNReal.ofReal C₄ := by
        have := hG4 Ω P ℱ μ hμ M hM Vev hVev Z hZ (fun t _ => (hZm t).aemeasurable)
        rw [show (4 : ℝ) / 2 = ((2 : ℕ) : ℝ) by norm_num] at this
        simpa [ENNReal.rpow_natCast] using this
      have hGtop : ∀ᵐ ω ∂P, G ω < ⊤ := by
        have h1 := ae_lt_top' (hGm.pow_const 2) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hG4'')
        filter_upwards [h1] with ω hω
        by_contra hcon
        have : G ω = ⊤ := not_lt_top_iff.1 hcon
        rw [this] at hω
        simp at hω
      have hE : ∀ᵐ ω ∂P, adjkEnergy (j : ℝ) m (Z s' ω) ≤ G ω := by
        filter_upwards [hZc] with ω hω
        exact adjka_energy_le_sup_rat hT.le hω hs'
      set Y : Ω → ℝ≥0∞ := fun ω => ‖Z' t' ω‖ₑ ^ (4 : ℝ) with hY
      have hpt : ∀ᵐ ω ∂P, ‖Z t' ω - Z s' ω‖ₑ ^ (4 : ℝ) ≤
          8 * (ENNReal.ofReal ((CA * h) ^ 4) * G ω ^ 2 + Y ω) := by
        filter_upwards [hsplit, hGtop, hE] with ω h1 h2 h3
        have hne : adjkEnergy (j : ℝ) m (Z s' ω) ≠ ⊤ := (h3.trans_lt h2).ne
        have e : Z t' ω - Z s' ω = (Vev t' s' (Z s' ω) - Z s' ω) + Z' t' ω := by
          rw [h1]; abel
        rw [e]
        refine le_trans (ENNReal.rpow_le_rpow (enorm_add_le _ _) (by norm_num)) (le_trans (adjka_pow4_add_le _ _) ?_)
        gcongr
        refine (adjka_drift_bound hjm hVj hVev hCA (hA2 Vj hVj) hs'.1 hle (Z s' ω) hne).trans ?_
        gcongr
      have hYb : ∫⁻ ω, Y ω ∂P ≤ ENNReal.ofReal CB4 * ENNReal.ofReal ((h * Bm) ^ 2) := by
        have h1 : ∀ ω, Y ω ≤ (⨆ t ∈ Set.Icc s' (s' + h), ‖Z' t ω‖ₑ) ^ (4 : ℝ) := fun ω =>
          ENNReal.rpow_le_rpow (le_iSup₂ (f := fun t (_ : t ∈ Set.Icc s' (s' + h)) => ‖Z' t ω‖ₑ) t' ht'I)
            (by norm_num)
        have htr : ∀ (u : ℝ) (ω : Ω), traceNormForm (covForm m β⁻¹ (μ u ω)) ≤ Bm := fun u ω => by
          haveI := hμ u ω
          have := (Q14.q14_covForm_trace hm2 hq (μ u ω)).2
          rw [measure_univ, ENNReal.toReal_one, mul_one] at this
          exact this
        have h2 := adjka_lintegral_trace_window P (a := s') (b := s' + h) (by linarith) hBm0
          (fun u ω => traceNormForm (covForm m β⁻¹ (μ u ω))) htr (r := (4 : ℝ) / 2) (by norm_num)
        rw [show s' + h - s' = h by ring, show (4 : ℝ) / 2 = ((2 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast] at h2
        refine (lintegral_mono h1).trans (hZ'bd.trans ?_)
        refine mul_le_mul_of_nonneg_left (le_trans (le_of_eq ?_) h2) bot_le
        congr 2
        norm_num
      calc ∫⁻ ω, ‖Z t' ω - Z s' ω‖ₑ ^ (4 : ℝ) ∂P
          ≤ ∫⁻ ω, 8 * (ENNReal.ofReal ((CA * h) ^ 4) * G ω ^ 2 + Y ω) ∂P := lintegral_mono_ae hpt
        _ = 8 * (ENNReal.ofReal ((CA * h) ^ 4) * ∫⁻ ω, G ω ^ 2 ∂P + ∫⁻ ω, Y ω ∂P) := by
            rw [lintegral_const_mul' _ _ (by simp), lintegral_add_left' ((hGm.pow_const 2).const_mul _),
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ 8 * (ENNReal.ofReal ((CA * h) ^ 4) * ENNReal.ofReal C₄ +
              ENNReal.ofReal CB4 * ENNReal.ofReal ((h * Bm) ^ 2)) := by
            gcongr
        _ = ENNReal.ofReal (8 * ((CA * h) ^ 4 * C₄ + CB4 * (h * Bm) ^ 2)) := by
            rw [show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by simp, ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        _ ≤ ENNReal.ofReal (C2 * h ^ 2) := by
            refine ENNReal.ofReal_le_ofReal ?_
            have h4 : h ^ 4 ≤ T ^ 2 * h ^ 2 := by
              have : h ^ 2 ≤ T ^ 2 := by nlinarith
              nlinarith [sq_nonneg h]
            have h5 : 0 ≤ CA ^ 4 * C₄ := by positivity
            calc 8 * ((CA * h) ^ 4 * C₄ + CB4 * (h * Bm) ^ 2)
                = 8 * (CA ^ 4 * C₄ * h ^ 4 + CB4 * Bm ^ 2 * h ^ 2) := by ring
              _ ≤ 8 * (CA ^ 4 * C₄ * (T ^ 2 * h ^ 2) + CB4 * Bm ^ 2 * h ^ 2) := by
                  gcongr
              _ = C2 * h ^ 2 := by rw [hC2]; ring
    intro s' hs' t' ht'
    refine (le_total s' t').elim (fun hle => ?_) (fun hle => ?_)
    · refine (key s' t' hs' ht' hle).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [sq_abs]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
    · have := key t' s' ht' hs' hle
      have e : ∀ ω, ‖Z t' ω - Z s' ω‖ₑ = ‖Z s' ω - Z t' ω‖ₑ := fun ω => by rw [enorm_sub_rev]
      simp_rw [e]
      refine this.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [sq_abs, show (s' - t') ^ 2 = (t' - s') ^ 2 by ring]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)

end HRS.AdjK
