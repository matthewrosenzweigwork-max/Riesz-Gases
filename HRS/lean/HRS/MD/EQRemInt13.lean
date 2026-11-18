import HRS.MD.EQRemInt12
import HRS.MD.EQRemStatic
import HRS.MD.Stat

/-!
# EQ-REM (b): `eq_rem_integrated_proof`

The final assembly: joint measurability of the flow from the filtration, stationarity, the static bound `eq_rem_static_proof`,
and the abstract Minkowski / second-moment bound of `EQRemInt12`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MD.EQRem

open HRS HRS.MD.EQ29 HRS.Quad
open HRS.LZ HRS.Uniform HRS.Main

variable {d : ℕ}

theorem eqrem_joint_meas {N : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ mΩ) (b : ℝ)
    (X : ℝ≥0 → Ω → Config d N) (hprog : IsProgressive ℱ (ofNNRealTime X)) :
    Measurable (fun p : ℝ × Ω => X (min b p.1).toNNReal p.2) := by
  have h1 := hprog b
  have h2 : Measurable (fun q : Set.Iic b × Ω => ofNNRealTime X q.1 q.2) :=
    h1.mono (sup_le_sup le_rfl (MeasurableSpace.comap_mono (ℱ.le b))) le_rfl
  have h3 : Measurable (fun p : ℝ × Ω =>
      ((⟨min b p.1, Set.mem_Iic.2 (min_le_left _ _)⟩ : Set.Iic b), p.2)) :=
    (Measurable.subtype_mk (measurable_const.min measurable_fst)).prodMk measurable_snd
  exact h2.comp h3

/-- (Packet EQ-REM (b), TeX L4045-4047.)  The time-integrated stationary remainder. -/
theorem eq_rem_integrated_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (M : ℝ) (hM : (d : ℝ) / 2 + 2 < M) (T : ℝ) (hT : 0 ≤ T) (K c : ℝ) (hK : 0 ≤ K) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d s) V β ρβ → ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStationaryGibbsFlow P s hs0 hsd V β (hβm.trans_le hβ.1) (a + T) X₀ W X →
      ∀ Vev : ℝ → ℝ → NegSobolev d M →L[ℝ] NegSobolev d M,
        IsDualEvolution (PDE.mfData d s hs0 hsd V β (hβm.trans_le hβ.1)) (fun _ => ρβ) M Vev →
        (∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ K * Real.exp (-c * (t - u))) →
        (∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) (a + T), ∀ k : NonzeroLattice d,
          IntervalIntegrable (fun r => statRemainder d s V β ρβ (N := N)
            (propagator (PDE.mfData d s hs0 hsd V β (hβm.trans_le hβ.1)) (fun _ => ρβ) r t
              (Torus.realMode k)) (X r.toNNReal ω)) volume 0 t) ∧
        ∫⁻ ω, ⨆ t ∈ ratTimes a T,
            (coordEnergy M (fun k => statForcingCoord d hs0 hsd V (hβm.trans_le hβ.1) ρβ X k t ω)) ^
              (1 / 2 : ℝ) ∂P ≤ ENNReal.ofReal (C * Real.sqrt (deltaN d s N)) ∧
        ∫⁻ ω, (⨆ t ∈ ratTimes a T,
            (coordEnergy M (fun k => statForcingCoord d hs0 hsd V (hβm.trans_le hβ.1) ρβ X k t ω)) ^
              (1 / 2 : ℝ)) ^ 2 ∂P ≤ ENNReal.ofReal (C * deltaN d s N) := by

  obtain ⟨Ca, hCa0, hCa⟩ := eq_rem_static_proof hd hs0 hsd V hV βm βp hβm hββ M hM
  set C₃ : ℝ := ((K + 1) * (1 / c + T)) ^ 2 * Ca with hC₃
  have hC₃0 : 0 < C₃ := by
    have : 0 < (K + 1) * (1 / c + T) := mul_pos (by linarith) (by positivity)
    exact mul_pos (pow_pos this 2) hCa0
  refine ⟨C₃ + Real.sqrt C₃ + 1, by positivity, ?_⟩
  intro β hβ ρβ hρ a ha N hN Ω _ P _ X₀ W X hflow Vev hdual hdec
  have hβ0 : 0 < β := hβm.trans_le hβ.1
  have hb : 0 ≤ a + T := add_nonneg ha hT
  set D : DynData d := PDE.mfData d s hs0 hsd V β hβ0 with hD
  set ρ : ℝ → Torus d → ℝ := fun _ => ρβ with hρdef
  obtain ⟨ℱ, W', hfs⟩ := hflow.filtered
  set Y : ℝ × Ω → Config d N := fun p => X (min (a + T) p.1).toNNReal p.2 with hYdef
  have hYm : Measurable Y := eqrem_joint_meas ℱ (a + T) X hfs.progressive
  have hYr : ∀ r ω, r ≤ a + T → Y (r, ω) = X r.toNNReal ω := by
    intro r ω hr; simp only [hYdef, min_eq_right hr]
  have hdeltaN : 0 ≤ deltaN d s N := deltaN_nonneg s (by omega)
  -- the energy functional
  set E : Config d N → ℝ≥0∞ := fun x =>
    coordEnergy M (fun j => statRemainder d s V β ρβ (N := N) (Torus.realMode j) x) with hEdef
  have hRm : ∀ j : NonzeroLattice d, Measurable (statRemainder d s V β ρβ (N := N) (Torus.realMode j)) :=
    fun j => eqrem_statRemainder_meas hd hs0 hsd V hV hβ0 hρ hN (by
      have := Uniform.Q54c.isCk_realMode j 2
      exact_mod_cast this)
  have hE : Measurable E := by
    refine Measurable.ennreal_tsum fun k => ?_
    exact ENNReal.measurable_ofReal.comp (measurable_const.mul ((hRm k).pow_const 2))
  -- stationarity
  have hB : ∀ r ∈ Set.Ioc (0 : ℝ) (a + T),
      ∫⁻ ω, E (Y (r, ω)) ∂P ≤ ENNReal.ofReal (Ca * deltaN d s N) := by
    intro r hr
    have hst := HRS.MD.Stat.md_stat_gibbs_flow_stationary_proof hd hs0 hsd V hV β hβ0 (a + T) hN P X₀ W X
      hflow r.toNNReal (by rw [Real.coe_toNNReal _ hr.1.le]; exact hr.2)
    have hXm : Measurable (X r.toNNReal) := by
      have : X r.toNNReal = fun ω => Y (r, ω) := by
        funext ω; exact (hYr r ω hr.2).symm
      rw [this]
      exact hYm.comp (measurable_const.prodMk measurable_id)
    have e1 : ∫⁻ ω, E (Y (r, ω)) ∂P = ∫⁻ x, E x ∂(canonicalGibbs (periodicRiesz d s) V N β) := by
      rw [← hst, lintegral_map hE hXm]
      exact lintegral_congr fun ω => by rw [hYr r ω hr.2]
    rw [e1]
    exact (hCa β hβ ρβ hρ N hN).2
  obtain ⟨Φ, hΦm, hi, hm, hΦ⟩ := eqrem_abstract P Y hYm E hE (Gam d s V β ρβ (N := N) D ρ)
    (fun t k => eqrem_Gam_meas hd hs0 hsd V hV hβ0 hρ hN hM D ρ Vev hdual hK hdec t k) hK hc
    (fun t r x => eqrem_Gam_energy hd hs0 hsd V hV hβ0 hρ hN hM D ρ Vev hdual hK hdec t r x)
    a T ha hT _ ENNReal.ofReal_ne_top hB
  -- conversion of the interval integral
  have hfg : ∀ ω t k, t ∈ Set.Icc (0 : ℝ) (a + T) → ∀ r ∈ Set.Ioo 0 t,
      statRemainder d s V β ρβ (N := N) (propagator D ρ r t (Torus.realMode k)) (X r.toNNReal ω) =
        Gam d s V β ρβ (N := N) D ρ t k r (Y (r, ω)) := by
    intro ω t k ht r hr
    rw [hYr r ω (hr.2.le.trans ht.2)]
    simp only [Gam, hr, ↓reduceIte]
  have hconv : ∀ ω t k, t ∈ Set.Icc (0 : ℝ) (a + T) →
      statForcingCoord d hs0 hsd V hβ0 ρβ X k t ω =
        ∫ r in Set.Ioc 0 t, Gam d s V β ρβ (N := N) D ρ t k r (Y (r, ω)) := by
    intro ω t k ht
    unfold statForcingCoord
    rw [intervalIntegral.integral_of_le ht.1, integral_Ioc_eq_integral_Ioo,
      integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo fun r hr => hfg ω t k ht r hr
  have hZ : ∀ᵐ ω ∂P, (⨆ t ∈ ratTimes a T,
      (coordEnergy M (fun k => statForcingCoord d hs0 hsd V hβ0 ρβ X k t ω)) ^ (1 / 2 : ℝ)) ≤ Φ ω := by
    filter_upwards [hm] with ω hω
    refine iSup₂_le fun t ht => ?_
    have ht' : t ∈ Set.Icc a (a + T) := ht.1
    have ht0 : t ∈ Set.Icc (0 : ℝ) (a + T) := ⟨ha.trans ht'.1, ht'.2⟩
    have : (fun k => statForcingCoord d hs0 hsd V hβ0 ρβ X k t ω) =
        fun k => ∫ r in Set.Ioc 0 t, Gam d s V β ρβ (N := N) D ρ t k r (Y (r, ω)) :=
      funext fun k => hconv ω t k ht0
    rw [this]
    exact hω t ht'
  -- the second moment bound for `Φ`
  have hδ : ENNReal.ofReal ((K + 1) * (1 / c + T)) ^ 2 * ENNReal.ofReal (Ca * deltaN d s N) =
      ENNReal.ofReal (C₃ * deltaN d s N) := by
    have h0 : 0 ≤ (K + 1) * (1 / c + T) := by
      have : 0 < (K + 1) * (1 / c + T) := mul_pos (by linarith) (by positivity)
      exact this.le
    rw [← ENNReal.ofReal_pow h0, ← ENNReal.ofReal_mul (pow_nonneg h0 2)]
    congr 1; rw [hC₃]; ring
  have hΦ2 : ∫⁻ ω, Φ ω ^ 2 ∂P ≤ ENNReal.ofReal (C₃ * deltaN d s N) := hδ ▸ hΦ
  have hCle : C₃ * deltaN d s N ≤ (C₃ + Real.sqrt C₃ + 1) * deltaN d s N := by
    refine mul_le_mul_of_nonneg_right ?_ hdeltaN
    have := Real.sqrt_nonneg C₃
    linarith
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hi] with ω hω t ht k
    have hg := hω t ht k
    have hg' := ((integrableOn_Ioc_iff_integrableOn_Ioo enorm_ne_top).1 hg)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1, (integrableOn_Ioc_iff_integrableOn_Ioo enorm_ne_top)]
    exact hg'.congr_fun (fun r hr => (hfg ω t k ht r hr).symm) measurableSet_Ioo
  · -- (ii)
    have h1 : ∫⁻ ω, (⨆ t ∈ ratTimes a T,
        (coordEnergy M (fun k => statForcingCoord d hs0 hsd V hβ0 ρβ X k t ω)) ^ (1 / 2 : ℝ)) ∂P ≤
        ∫⁻ ω, Φ ω ∂P := lintegral_mono_ae hZ
    refine h1.trans ?_
    have hcs := eqrem_cs P Φ hΦm.aemeasurable
    rw [measure_univ, one_mul] at hcs
    have h2 : (∫⁻ ω, Φ ω ∂P) ^ 2 ≤ (ENNReal.ofReal (Real.sqrt (C₃ * deltaN d s N))) ^ 2 := by
      rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (mul_nonneg hC₃0.le hdeltaN)]
      exact hcs.trans hΦ2
    refine (eqrem_ennreal_le_of_sq_le h2).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [Real.sqrt_mul hC₃0.le]
    refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    have h1 : Real.sqrt C₃ ≤ C₃ + Real.sqrt C₃ + 1 := by linarith
    exact h1
  · -- (iii)
    refine le_trans ?_ ((ENNReal.ofReal_le_ofReal hCle))
    refine le_trans ?_ hΦ2
    exact lintegral_mono_ae (hZ.mono fun ω hω => pow_le_pow_left' hω 2)


end HRS.MD.EQRem

end
