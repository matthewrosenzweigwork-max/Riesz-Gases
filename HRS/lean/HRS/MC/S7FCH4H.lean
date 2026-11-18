import HRS.MC.S7FCH4G
import HRS.MC.S7FCF5RE3b

/-!
# S7FCH4H: the core of H4 (conditional on the FC-D conclusion `hD`)

`S7FCH4_core`: the statement of `s7_FC_H4_finite_rank_W` with the extra hypothesis `hD`
(`W_q(law ζ_N, law η|[0,T]) → 0` for all `q ≥ 1`, the conclusion of FC-D).
-/
open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace HRS.MC.Sec7.S7FCH4
open Classical
variable {d : ℕ}

theorem S7FCH4_core (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T)
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → Config d N)
    (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hreal : ∀ N, 1 ≤ N → PreparedRealization R.D (P N)
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) (X₀ N) (W N) (X N))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η : ℝ → Ω' → NegSobolev d r)
    (hη : IsGaussianLimitField R.D R.ρ (withDensityReal R.ρ₀) R.β₀ r P' η)
    (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d) (q : ℝ) (hq : 1 ≤ q)
    (hD : ∀ q : ℝ, 1 ≤ q → Tendsto (fun N : ℕ => wassersteinE q (law (P N) (zetaWin r T 0 (P N) (X N)))
        (law P' (procWin r T 0 η))) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => wassersteinE q
        (law (P N) (fun ω => (zetaWin r T 0 (P N) (X N) ω,
          toL2 r T (fun t => fcPartAt r S K (fun t => withDensityReal (R.ρ t)) (P N) (X N) (0 + t) ω))))
        (law P' (fun ω => (procWin r T 0 η ω, toL2 r T (fun t => fcGaussAt r S K P' η (0 + t) ω)))))
      atTop (𝓝 0) := by
  have hq0 : 0 < q := by linarith
  have hq2 : 1 ≤ 2 * q := by linarith
  obtain ⟨m, hm0, hmz⟩ := HRS.MC.Sec7.S7FCD5.s7_FC_D5_mean_proof R r hr T hT P X₀ W X hreal P' η hη
  obtain ⟨C, hC⟩ := HRS.MC.Sec7.S7FCF5R.fcf5_E3b_F5_zeta_moments_proof R r hr T hT (2 * q) hq2
  have hF5 : ∀ N : ℕ, 2 ≤ N → Integrable (fun ω => ‖zetaWin r T 0 (P N) (X N) ω‖ ^ (2 * q)) (P N) ∧
      ∫ ω, ‖zetaWin r T 0 (P N) (X N) ω‖ ^ (2 * q) ∂(P N) ≤ C := fun N hN =>
    (hC 0 le_rfl N hN (P N) (X₀ N) (W N) (X N) (hreal N (by omega))).1
  have hη' := hη
  obtain ⟨Y₀, hY, hLin⟩ := hη'
  have hmη : ∀ t, Measurable (η t) := fun t => (hLin T).meas t
  have hcη : ∀ᵐ ω ∂P', ContinuousOn (fun t => η t ω) (Set.Icc 0 T) := (hLin T).cont
  have hpm : AEMeasurable (procWin r T 0 η) P' :=
    HRS.MC.Sec7.S7FCD5B.S7FCD5B_procWin_aemeasurable P' r T hT η hmη hcη
  have hzm : ∀ N : ℕ, 2 ≤ N → AEMeasurable (zetaWin r T 0 (P N) (X N)) (P N) := fun N hN =>
    (HRS.MC.Sec7.S7FCF5I.fcf5_E2_window_aemeasurable_proof R r hr T hT (by omega) (P N) (X₀ N) (W N) (X N)
      (hreal N (by omega)) 0 le_rfl).2
  set ν : Measure (PathSpace d r T) := law P' (procWin r T 0 η) with hν
  have hνprob : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff hpm).2 inferInstance
  set μ : ℕ → Measure (PathSpace d r T) :=
    fun N => if 2 ≤ N then law (P N) (zetaWin r T 0 (P N) (X N)) else ν with hμdef
  have hμN : ∀ N : ℕ, 2 ≤ N → μ N = law (P N) (zetaWin r T 0 (P N) (X N)) := fun N hN => if_pos hN
  have hμprob : ∀ N, IsProbabilityMeasure (μ N) := by
    intro N
    by_cases h : 2 ≤ N
    · rw [hμN N h]
      exact (Measure.isProbabilityMeasure_map_iff (hzm N h)).2 inferInstance
    · show IsProbabilityMeasure (if 2 ≤ N then _ else ν)
      rw [if_neg h]
      exact hνprob
  -- moment bounds
  set c : ℝ≥0∞ := ENNReal.ofReal C ^ (1 / (2 * q)) with hcdef
  have hctop : c ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have hnorm : Measurable (fun u : PathSpace d r T => ENNReal.ofReal ‖u‖) :=
    ENNReal.measurable_ofReal.comp measurable_norm
  have hLz : ∀ N : ℕ, 2 ≤ N →
      S7FCH4_Lp (2 * q) (P N) (fun ω => ENNReal.ofReal ‖zetaWin r T 0 (P N) (X N) ω‖) ≤ c :=
    fun N hN => S7FCH4_zeta_Lp hq (hzm N hN) (hF5 N hN).1 (hF5 N hN).2
  have hLμ : ∀ N : ℕ, 2 ≤ N → S7FCH4_Lp (2 * q) (μ N) (fun u => ENNReal.ofReal ‖u‖) ≤ c := by
    intro N hN
    rw [hμN N hN, S7FCH4_Lp_law (hzm N hN) _ hnorm]
    exact hLz N hN
  have hw : Tendsto (fun N : ℕ => wassersteinE (2 * q) (μ N) ν) atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ (hD (2 * q) hq2)
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [hμN N hN]
  -- the limit window has finite moments
  obtain ⟨N₀, hN₀, hW₀⟩ := ((eventually_ge_atTop 2).and (hw.eventually (gt_mem_nhds zero_lt_one))).exists
  have hLν := S7FCH4_nu_moment hq (μ N₀) ν hW₀ (hLμ N₀ hN₀)
  have hLν' : S7FCH4_Lp (2 * q) P' (fun ω => ENNReal.ofReal ‖procWin r T 0 η ω‖) ≠ ⊤ := by
    have := S7FCH4_Lp_law hpm (2 * q) hnorm
    rw [← this]
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hctop, ENNReal.ofNat_ne_top⟩) hLν
  have hνsq : Integrable (fun ω => ‖procWin r T 0 η ω‖ ^ 2) P' := S7FCH4_sq_integrable hq hpm hLν'
  have hint0 : Integrable (fun ω => S7FCH4_Y S K 0 (0 : PathSpace d r T) (procWin r T 0 η ω)) P' :=
    S7FCH4_Y_integrable S K le_rfl (by simp) hpm hνsq
  have hY0i : Integrable (S7FCH4_Y S K 0 (0 : PathSpace d r T)) ν :=
    (integrable_map_measure (S7FCH4_Y_continuous S K 0 0).aestronglyMeasurable hpm).2 hint0
  -- the particle side
  have hyi : ∀ N : ℕ, 2 ≤ N → ‖m N‖ ≤ 1 →
      Integrable (fun ω => S7FCH4_Y S K (Real.sqrt N)⁻¹ (m N) (zetaWin r T 0 (P N) (X N) ω)) (P N) := by
    intro N hN hm1
    have hzsq := S7FCH4_sq_integrable hq (hzm N hN)
      (ne_top_of_le_ne_top hctop (hLz N hN))
    exact S7FCH4_Y_integrable S K (by positivity) hm1 (hzm N hN) hzsq
  have hlim := S7FCH4_limit hT.le hq S K μ ν m hctop
    ((eventually_ge_atTop 2).mono hLμ) hw hm0
    (((eventually_ge_atTop 2).and (hm0.eventually (ge_mem_nhds zero_lt_one))).mono fun N hN => by
      rw [hμN N hN.1]
      exact (integrable_map_measure (S7FCH4_Y_continuous S K _ _).aestronglyMeasurable (hzm N hN.1)).2
        (hyi N hN.1 hN.2)) hY0i
  refine Tendsto.congr' ?_ hlim
  filter_upwards [eventually_ge_atTop 2, hm0.eventually (ge_mem_nhds zero_lt_one)] with N hN hm1
  have hint := hyi N hN hm1
  have hΨ : Measurable (fun u : PathSpace d r T => (u, S7FCH4_iota hT.le
      (S7FCH4_Y S K (Real.sqrt N)⁻¹ (m N) u - ∫ x, S7FCH4_Y S K (Real.sqrt N)⁻¹ (m N) x ∂(μ N)))) :=
    measurable_id.prodMk ((S7FCH4_iota_continuous hT.le).measurable.comp
      ((S7FCH4_Y_continuous S K _ _).measurable.sub_const _))
  have hΨ0 : Measurable (fun u : PathSpace d r T => (u, S7FCH4_iota hT.le
      (S7FCH4_Y S K 0 (0 : PathSpace d r T) u - ∫ x, S7FCH4_Y S K 0 (0 : PathSpace d r T) x ∂ν))) :=
    measurable_id.prodMk ((S7FCH4_iota_continuous hT.le).measurable.comp
      ((S7FCH4_Y_continuous S K _ _).measurable.sub_const _))
  have hcen : ∫ x, S7FCH4_Y S K (Real.sqrt N)⁻¹ (m N) x ∂(μ N) =
      ∫ ω, S7FCH4_Y S K (Real.sqrt N)⁻¹ (m N) (zetaWin r T 0 (P N) (X N) ω) ∂(P N) := by
    rw [hμN N hN]
    exact integral_map (hzm N hN) (S7FCH4_Y_continuous S K _ _).aestronglyMeasurable
  have hcen0 : ∫ x, S7FCH4_Y S K 0 (0 : PathSpace d r T) x ∂ν =
      ∫ ω, S7FCH4_Y S K 0 (0 : PathSpace d r T) (procWin r T 0 η ω) ∂P' :=
    integral_map hpm (S7FCH4_Y_continuous S K _ _).aestronglyMeasurable
  have hid := S7FCH4_particle_id R r hr T hT hN (P N) (X₀ N) (W N) (X N) (hreal N (by omega)) S K (m N)
    (hmz N hN) hint
  have hgid := S7FCH4_gauss_id hT P' η S K hmη hcη hνsq hint0
  have hL : law (P N) (fun ω => (zetaWin r T 0 (P N) (X N) ω,
      toL2 r T (fun t => fcPartAt r S K (fun t => withDensityReal (R.ρ t)) (P N) (X N) (0 + t) ω))) =
      (μ N).map (fun u => (u, S7FCH4_iota hT.le
        (S7FCH4_Y S K (Real.sqrt N)⁻¹ (m N) u - ∫ x, S7FCH4_Y S K (Real.sqrt N)⁻¹ (m N) x ∂(μ N)))) := by
    have e : (μ N).map (fun u => (u, S7FCH4_iota hT.le
        (S7FCH4_Y S K (Real.sqrt N)⁻¹ (m N) u - ∫ x, S7FCH4_Y S K (Real.sqrt N)⁻¹ (m N) x ∂(μ N)))) =
        (law (P N) (zetaWin r T 0 (P N) (X N))).map (fun u => (u, S7FCH4_iota hT.le
        (S7FCH4_Y S K (Real.sqrt N)⁻¹ (m N) u - ∫ x, S7FCH4_Y S K (Real.sqrt N)⁻¹ (m N) x ∂(μ N)))) := by
      rw [← hμN N hN]
    rw [e, AEMeasurable.map_map_of_aemeasurable hΨ.aemeasurable (hzm N hN)]
    refine Measure.map_congr (hid.mono fun ω h => ?_)
    simp only [Function.comp]
    rw [h, hcen]
  have hR : law P' (fun ω => (procWin r T 0 η ω, toL2 r T (fun t => fcGaussAt r S K P' η (0 + t) ω))) =
      ν.map (fun u => (u, S7FCH4_iota hT.le
        (S7FCH4_Y S K 0 (0 : PathSpace d r T) u - ∫ x, S7FCH4_Y S K 0 (0 : PathSpace d r T) x ∂ν))) := by
    refine Eq.trans ?_ (AEMeasurable.map_map_of_aemeasurable hΨ0.aemeasurable hpm).symm
    refine Measure.map_congr (hgid.mono fun ω h => ?_)
    simp only [Function.comp]
    rw [h, hcen0]
  rw [hL, hR]

end HRS.MC.Sec7.S7FCH4
