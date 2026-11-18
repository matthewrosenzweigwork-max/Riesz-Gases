import HRS.MS.MovEntAux22

/-!
# S6.6, packet P5 (part 6): the window bound

`s66_window`: with a uniform bound on `E m_t` and on `E Pp(X_t)` (`t ≥ 0`), `E sup_{t∈[b,b+T]} m_t ≤ C_T`, `C_T` independent of `b, N`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovEnt

open HRS.Whole HRS.MH.DualityRd

variable {d : ℕ}

theorem s66_sigma_nonneg {s : ℝ} (hs0 : 0 ≤ s) : 0 ≤ movtr_sigma s := by
  unfold movtr_sigma; split_ifs <;> linarith

theorem s66_window {s : ℝ} (q β : ℝ) (hβ : 0 < β) (hq : 0 < q) (hs0 : 0 ≤ s) (Cm CP T : ℝ) (hCm : 0 ≤ Cm)
    (hCP : 0 ≤ CP) (hT : 0 < T) :
    ∃ CT : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
      MovParticleSetup P d s q β N X₀ W X →
      (∀ t : ℝ, 0 ≤ t → ∫⁻ ζ, ENNReal.ofReal (movSecondMoment (X t.toNNReal ζ)) ∂P ≤ ENNReal.ofReal Cm) →
      (∀ t : ℝ, 0 ≤ t → ∫⁻ ζ, ENNReal.ofReal (s66Pp s (X t.toNNReal ζ)) ∂P ≤ ENNReal.ofReal CP) →
      ∀ b : ℝ, 0 ≤ b →
        ∫⁻ ζ, ⨆ t ∈ Set.Icc b (b + T), ENNReal.ofReal (movSecondMoment (X t.toNNReal ζ)) ∂P ≤
          ENNReal.ofReal CT := by
  set σ : ℝ := movtr_sigma s with hσ
  have hσ0 : 0 ≤ σ := s66_sigma_nonneg hs0
  refine ⟨Cm + T * (σ * CP + 2 * β⁻¹ * d) + 1 + 4 * (T * (8 * β⁻¹ * Cm)), ?_⟩
  intro N hN Ω _ P _ X₀ W X hset hmom hPp b hb
  have hN0 : 0 < N := by omega
  obtain ⟨ℱ, W', hF⟩ := hset.filtered
  set D : WholeDyn d := quadraticGradientDyn d s q β with hD
  have hinv : 0 ≤ D.invβ := (inv_pos.2 hβ).le
  set T' : ℝ := b + T with hT'
  have hT'0 : 0 ≤ T' := by linarith
  have hbT : b ≤ T' := by linarith
  have hXs := hset.sol T'
  have hprog : IsProgressive ℱ (ofNNRealTime X) := hF.progressive
  have hXm : ∀ t : ℝ≥0, Measurable (X t) := hXs.adapted
  have hVm : Measurable (gradient D.V) := by
    have : gradient D.V = fun x : Euc d => q • x := funext (movtr_gradient_confinement q)
    rw [this]; fun_prop
  have hito := s66_ito_m D hVm hT'0 hXs hF
  have hΦ2 := s66_Phi_L2 hN0 D hinv T' hprog hmom
  have hloc := HRS.localItoIntegral_eq_itoIntegral hF.brownian hΦ2
  set Φ := s66Phi D T' X with hΦ
  set e0 : ℝ := 2 * β⁻¹ * d with he0
  have he00 : 0 ≤ e0 := by positivity
  -- measurability of the pointwise functions
  have hmeasm : Measurable (fun Y : EucConfig d N => ENNReal.ofReal (movSecondMoment Y)) :=
    ENNReal.measurable_ofReal.comp s66_measurable_secondMoment
  have hGdb : Measurable (fun Y : EucConfig d N => ENNReal.ofReal (σ * s66Pp s Y + e0)) :=
    ENNReal.measurable_ofReal.comp ((measurable_const.mul (s66_Pp_measurable s)).add measurable_const)
  -- the pointwise estimate, almost surely
  have hpath : ∀ᵐ ζ ∂P, ⨆ t ∈ Set.Icc b T', ENNReal.ofReal (movSecondMoment (X t.toNNReal ζ)) ≤
      (ENNReal.ofReal (movSecondMoment (X b.toNNReal ζ)) +
        ∫⁻ s' in Set.Icc b T', ENNReal.ofReal (σ * s66Pp s (X s'.toNNReal ζ) + e0)) +
      ⨆ t ∈ Set.Icc b T', ‖HRS.itoIntegral P ℱ W' Φ t ζ - HRS.itoIntegral P ℱ W' Φ b ζ‖ₑ := by
    filter_upwards [hito, hXs.no_collision, hXs.cont, hloc] with ζ h1 h2 h3 h4
    obtain ⟨hI, hEq⟩ := h1
    -- the real functions
    set m : ℝ → ℝ := fun s' => movSecondMoment (X s'.toNNReal ζ) with hm
    set M : ℝ → ℝ := fun t => HRS.itoIntegral P ℱ W' Φ t ζ with hMdef
    set dr : ℝ → ℝ := fun s' => fderiv ℝ (HRS.sumLift N (fun x : Euc d => ‖x‖ ^ 2)) (X s'.toNNReal ζ)
            (particleDriftW D (X s'.toNNReal ζ)) +
          (1 / 2) * ∑ k : Fin N × Fin d,
            fderiv ℝ (fderiv ℝ (HRS.sumLift N (fun x : Euc d => ‖x‖ ^ 2))) (X s'.toNNReal ζ)
              (noiseDir D k) (noiseDir D k) with hdr
    set dbar : ℝ → ℝ := fun s' => σ * s66Pp s (X s'.toNNReal ζ) + e0 with hdbar
    have hnc : ∀ s' ∈ Set.Icc (0 : ℝ) T', X s'.toNNReal ζ ∉ eucCollisionSet d N := by
      intro s' hs'
      refine h2 s'.toNNReal ?_
      rw [Real.coe_toNNReal s' hs'.1]; exact hs'.2
    have hdreq : ∀ s' ∈ Set.Icc (0 : ℝ) T', dr s' = -2 * q * m s' + dbar s' := by
      intro s' hs'
      have := s66_drift_eq hN0 s q β hβ (X s'.toNNReal ζ) (hnc s' hs')
      simp only [hdr, hm, hdbar]
      rw [this]; ring
    have hmcont : Continuous m := by
      have hc : ∀ i, Continuous fun t : ℝ≥0 => X t ζ i := h3
      simp only [hm, movSecondMoment]
      refine continuous_const.mul (continuous_finset_sum _ fun i _ => ?_)
      exact ((hc i).comp continuous_real_toNNReal).norm.pow 2
    have hmI : IntegrableOn m (Set.Icc 0 T') := hmcont.integrableOn_Icc
    have hdbI : IntegrableOn dbar (Set.Icc 0 T') := by
      have : IntegrableOn (fun s' => dr s' + 2 * q * m s') (Set.Icc 0 T') := hI.add (hmI.const_mul _)
      refine this.congr_fun (fun s' hs' => ?_) measurableSet_Icc
      simp only
      rw [hdreq s' hs']; ring
    have hdb0 : ∀ s' ∈ Set.Icc (0 : ℝ) T', 0 ≤ dbar s' := fun s' _ => by
      have := s66_Pp_nonneg (d := d) s (X s'.toNNReal ζ)
      simp only [hdbar]; positivity
    have hle : ∀ s' ∈ Set.Icc (0 : ℝ) T', dr s' ≤ dbar s' := by
      intro s' hs'
      rw [hdreq s' hs']
      have := s66_m_nonneg (X s'.toNNReal ζ)
      have h5 : 0 ≤ q * m s' := mul_nonneg hq.le this
      linarith
    have hmeq : ∀ t ∈ Set.Icc (0 : ℝ) T', m t = m 0 + (∫ s' in Set.Icc (0 : ℝ) t, dr s') + M t := by
      intro t ht
      have hτ : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht.1
      have h5 := hEq t.toNNReal (by rw [hτ]; exact ht.2)
      rw [hτ] at h5
      simp only [hm, hMdef, hdr]
      rw [s66_m_eq, s66_m_eq, h5, ← h4 t]
      rw [Real.toNNReal_zero]
      rfl
    have key := s66_path_est (m := m) (M := M) (dr := dr) (dbar := dbar) hb hbT hI hdbI hdb0 hle hmeq
    refine iSup₂_le fun t ht => ?_
    refine (key t ht).trans ?_
    have hJ : ∫⁻ s' in Set.Ioc b T', ENNReal.ofReal (dbar s') ≤ ∫⁻ s' in Set.Icc b T', ENNReal.ofReal (dbar s') :=
      lintegral_mono_set Set.Ioc_subset_Icc_self
    have hS : ENNReal.ofReal |M t - M b| ≤ ⨆ t' ∈ Set.Icc b T', ‖M t' - M b‖ₑ := by
      rw [← Real.enorm_eq_ofReal_abs]
      exact le_iSup₂ (f := fun t' (_ : t' ∈ Set.Icc b T') => ‖M t' - M b‖ₑ) t ht
    exact add_le_add (add_le_add le_rfl hJ) hS
  -- expectations
  set S : Ω → ℝ≥0∞ := fun ζ => ⨆ t ∈ Set.Icc b T',
    ‖HRS.itoIntegral P ℱ W' Φ t ζ - HRS.itoIntegral P ℱ W' Φ b ζ‖ₑ with hS
  set J : Ω → ℝ≥0∞ := fun ζ => ∫⁻ s' in Set.Icc b T', ENNReal.ofReal (σ * s66Pp s (X s'.toNNReal ζ) + e0)
    with hJ
  have hJm : Measurable J := s66_lintegral_measurable hprog _ hGdb b T'
  have hmb : Measurable (fun ζ => ENNReal.ofReal (movSecondMoment (X b.toNNReal ζ))) :=
    hmeasm.comp (hXm _)
  have hf1m : Measurable (fun ζ => ENNReal.ofReal (movSecondMoment (X b.toNNReal ζ)) + J ζ) := hmb.add hJm
  -- term 1: the moment at time `b`
  have T1 : ∫⁻ ζ, ENNReal.ofReal (movSecondMoment (X b.toNNReal ζ)) ∂P ≤ ENNReal.ofReal Cm := hmom b hb
  -- term 2: the pair term
  have T2 : ∫⁻ ζ, J ζ ∂P ≤ ENNReal.ofReal (T * (σ * CP + e0)) := by
    have hsw := s66_swap_bound hprog (fun Y => ENNReal.ofReal (σ * s66Pp s Y + e0)) hGdb b T'
      (ENNReal.ofReal (σ * CP + e0)) (fun s' hs' => by
        have hs'0 : 0 ≤ s' := hb.trans hs'.1
        have hpt : ∀ ζ, ENNReal.ofReal (σ * s66Pp s (X s'.toNNReal ζ) + e0) ≤
            ENNReal.ofReal σ * ENNReal.ofReal (s66Pp s (X s'.toNNReal ζ)) + ENNReal.ofReal e0 := by
          intro ζ
          refine ENNReal.ofReal_add_le.trans ?_
          rw [ENNReal.ofReal_mul hσ0]
        calc ∫⁻ ζ, ENNReal.ofReal (σ * s66Pp s (X s'.toNNReal ζ) + e0) ∂P
            ≤ ∫⁻ ζ, (ENNReal.ofReal σ * ENNReal.ofReal (s66Pp s (X s'.toNNReal ζ)) + ENNReal.ofReal e0) ∂P :=
              lintegral_mono hpt
          _ = ENNReal.ofReal σ * ∫⁻ ζ, ENNReal.ofReal (s66Pp s (X s'.toNNReal ζ)) ∂P + ENNReal.ofReal e0 := by
              rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
                lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          _ ≤ ENNReal.ofReal σ * ENNReal.ofReal CP + ENNReal.ofReal e0 :=
              add_le_add (mul_le_mul' le_rfl (hPp s' hs'0)) le_rfl
          _ = ENNReal.ofReal (σ * CP + e0) := by
              rw [ENNReal.ofReal_add (mul_nonneg hσ0 hCP) he00, ENNReal.ofReal_mul hσ0])
    refine hsw.trans ?_
    have : T' - b = T := by rw [hT']; ring
    rw [this, ← ENNReal.ofReal_mul hT.le]
  -- term 3: the martingale increment
  have T3 : ∫⁻ ζ, S ζ ∂P ≤ 1 + 4 * ENNReal.ofReal (T * (8 * β⁻¹ * Cm)) := by
    have hbdg := HRS.bdg_two_incr hF.brownian hΦ2 hb hbT
    set c : ℝ := 8 * D.invβ / N with hc
    have hc0 : 0 ≤ c := by positivity
    have hcle : c ≤ 8 * β⁻¹ := by
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN0
      have : D.invβ = β⁻¹ := rfl
      rw [hc, this]
      have h8 : 0 ≤ 8 * β⁻¹ := by positivity
      calc 8 * β⁻¹ / N ≤ 8 * β⁻¹ / 1 := div_le_div_of_nonneg_left h8 one_pos hN1
        _ = 8 * β⁻¹ := div_one _
    have hΦb : ∀ ζ, ∫⁻ r in Set.Ioc b T', ∑ k, ‖Φ r ζ k‖ₑ ^ 2 ≤
        ∫⁻ r in Set.Icc b T', ENNReal.ofReal (c * movSecondMoment (X r.toNNReal ζ)) := by
      intro ζ
      refine (lintegral_mono_set Set.Ioc_subset_Icc_self).trans ?_
      refine setLIntegral_mono' measurableSet_Icc fun r hr => ?_
      rw [hΦ, s66_Phi_sqsum hN0 D hinv T' X r ζ, if_pos ⟨hb.trans hr.1, hr.2⟩]
    have hsw := s66_swap_bound hprog (fun Y => ENNReal.ofReal (c * movSecondMoment Y))
      (ENNReal.measurable_ofReal.comp (measurable_const.mul s66_measurable_secondMoment)) b T'
      (ENNReal.ofReal c * ENNReal.ofReal Cm) (fun s' hs' => by
        have hs'0 : 0 ≤ s' := hb.trans hs'.1
        calc ∫⁻ ζ, ENNReal.ofReal (c * movSecondMoment (X s'.toNNReal ζ)) ∂P
            = ∫⁻ ζ, ENNReal.ofReal c * ENNReal.ofReal (movSecondMoment (X s'.toNNReal ζ)) ∂P := by
              refine lintegral_congr fun ζ => ?_
              rw [ENNReal.ofReal_mul hc0]
          _ = ENNReal.ofReal c * ∫⁻ ζ, ENNReal.ofReal (movSecondMoment (X s'.toNNReal ζ)) ∂P :=
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
          _ ≤ ENNReal.ofReal c * ENNReal.ofReal Cm := mul_le_mul' le_rfl (hmom s' hs'0))
    have hS2 : ∫⁻ ζ, (S ζ) ^ 2 ∂P ≤ 4 * ENNReal.ofReal (T * (8 * β⁻¹ * Cm)) := by
      refine hbdg.trans (mul_le_mul' le_rfl ?_)
      refine (lintegral_mono hΦb).trans (hsw.trans ?_)
      have : T' - b = T := by rw [hT']; ring
      rw [this, ← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_mul hT.le]
      refine ENNReal.ofReal_le_ofReal ?_
      have := mul_le_mul_of_nonneg_right hcle hCm
      nlinarith
    calc ∫⁻ ζ, S ζ ∂P ≤ ∫⁻ ζ, (1 + (S ζ) ^ 2) ∂P := lintegral_mono fun ζ => s66_le_one_add_sq _
      _ = 1 + ∫⁻ ζ, (S ζ) ^ 2 ∂P := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ 1 + 4 * ENNReal.ofReal (T * (8 * β⁻¹ * Cm)) := add_le_add le_rfl hS2
  -- assemble
  have hpath' : ∀ᵐ ζ ∂P, ⨆ t ∈ Set.Icc b T', ENNReal.ofReal (movSecondMoment (X t.toNNReal ζ)) ≤
      (ENNReal.ofReal (movSecondMoment (X b.toNNReal ζ)) + J ζ) + S ζ := hpath
  calc ∫⁻ ζ, ⨆ t ∈ Set.Icc b T', ENNReal.ofReal (movSecondMoment (X t.toNNReal ζ)) ∂P
      ≤ ∫⁻ ζ, ((ENNReal.ofReal (movSecondMoment (X b.toNNReal ζ)) + J ζ) + S ζ) ∂P :=
        lintegral_mono_ae hpath'
    _ = ∫⁻ ζ, (ENNReal.ofReal (movSecondMoment (X b.toNNReal ζ)) + J ζ) ∂P + ∫⁻ ζ, S ζ ∂P :=
        lintegral_add_left hf1m _
    _ = (∫⁻ ζ, ENNReal.ofReal (movSecondMoment (X b.toNNReal ζ)) ∂P + ∫⁻ ζ, J ζ ∂P) + ∫⁻ ζ, S ζ ∂P := by
        rw [lintegral_add_left hmb]
    _ ≤ (ENNReal.ofReal Cm + ENNReal.ofReal (T * (σ * CP + e0))) +
          (1 + 4 * ENNReal.ofReal (T * (8 * β⁻¹ * Cm))) :=
        add_le_add (add_le_add T1 T2) T3
    _ = ENNReal.ofReal (Cm + T * (σ * CP + 2 * β⁻¹ * d) + 1 + 4 * (T * (8 * β⁻¹ * Cm))) := by
        have h1 : 0 ≤ T * (σ * CP + e0) := by positivity
        have h2 : 0 ≤ T * (8 * β⁻¹ * Cm) := by positivity
        have e4 : (4 : ℝ≥0∞) = ENNReal.ofReal 4 := by simp
        have e1 : (1 : ℝ≥0∞) = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
        rw [e4, e1, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
          ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) (by positivity),
          ← ENNReal.ofReal_add hCm h1, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end HRS.MS.MovEnt

end
