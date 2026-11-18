import HRS.MC.S7UCWA
import HRS.MC.S7UCU
import HRS.MC.S7UCHB
import HRS.MC.S7FCF5RE3b
import HRS.MC.S7FCD4

/-!
# Packet ucW (UC-H4): `s7_UC_H4_finite_rank_W_unif_proof`

Statement copied verbatim from `HRS/MC/S7UCPlan.lean` (checked in `HRS/MC/S7UCWTie.lean`); imports no sorried module.

Route (the proof of `S7FCH4_core` with the supremum over the window start `a`):
* `m N a` from UC-D5 (`‖m N a‖ ≤ W_2(Law windowFluc^a, Law procWin^a) ≤ ε_N := ⨆_a W_2(..) → 0` by D4);
* `⨆_a W_{2q}(Law ζ_N^a, Law procWin^a) → 0` from UC-D at order `2q`;
* `L^{2q}` moments of `ζ_N^a` from F5, uniform in `a` and `N ≥ 2`; the moments of `procWin^a` from `S7FCH4_nu_moment`
  once the supremum is `< 1`;
* identification of the laws of the pair by UC-H4a/b (`S7UCWA.lean`), and the limit by UC-H4c.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7UCW

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.S7FCH4

variable {d : ℕ}

/-- **UC-H4 (finite-rank pair, `W_q` uniformly in the window)**: proof of `s7_UC_H4_finite_rank_W_unif`. -/
theorem s7_UC_H4_finite_rank_W_unif_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T)
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → Config d N)
    (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hreal : ∀ N, 1 ≤ N → PreparedRealization R.D (P N)
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) (X₀ N) (W N) (X N))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η : ℝ → Ω' → NegSobolev d r)
    (hη : IsGaussianLimitField R.D R.ρ (withDensityReal R.ρ₀) R.β₀ r P' η)
    (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d) (q : ℝ) (hq : 1 ≤ q) :
    Tendsto (fun N : ℕ => ⨆ a : {a : ℝ // 0 ≤ a}, wassersteinE q
        (law (P N) (fun ω => (zetaWin r T a.1 (P N) (X N) ω,
          toL2 r T (fun t => fcPartAt r S K (fun t => withDensityReal (R.ρ t)) (P N) (X N) (a.1 + t) ω))))
        (law P' (fun ω => (procWin r T a.1 η ω, toL2 r T (fun t => fcGaussAt r S K P' η (a.1 + t) ω)))))
      atTop (𝓝 0) := by
  classical
  have hq0 : 0 < q := by linarith
  have hq2 : 1 ≤ 2 * q := by linarith
  -- D5 at window `a`: the mean paths
  have hD5 := HRS.MC.Sec7.S7UCD.s7_UC_D5_mean_window_proof R r hr T hT P X₀ W X hreal P' η hη
  choose! mf hmf0 hmfz using hD5
  -- D4 gives `m → 0` uniformly
  have hD4 := HRS.MC.Sec7.S7FCD4.s7_FC_D4_eta_W2_proof R r hr T hT P X₀ W X hreal P' η hη
  have hm : Tendsto (fun N : ℕ => ⨆ a : {a : ℝ // 0 ≤ a}, ENNReal.ofReal ‖mf a.1 N‖) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hD4
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact iSup_mono fun a => hmf0 a.1 a.2 N hN
  -- D at order `2q`
  have hDq := HRS.MC.Sec7.S7UCU.s7_UC_D_unif_proof R r hr T hT P X₀ W X hreal P' η hη (2 * q) hq2
  -- measurability
  have hη' := hη
  obtain ⟨Y₀, hY, hLin⟩ := hη'
  have hmη : ∀ t, Measurable (η t) := fun t => (hLin T).meas t
  have hpm : ∀ a : ℝ, 0 ≤ a → AEMeasurable (procWin r T a η) P' := fun a ha =>
    HRS.MC.Sec7.S7UCU.S7UCU_procWin_aemeasurable P' r T hT η a ha hmη (hLin (a + T)).cont
  have hcη : ∀ a : ℝ, 0 ≤ a → ∀ᵐ ω ∂P', ContinuousOn (fun t => η t ω) (Set.Icc a (a + T)) := fun a ha =>
    (hLin (a + T)).cont.mono fun ω h => h.mono (Set.Icc_subset_Icc_left ha)
  have hzm : ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N → AEMeasurable (zetaWin r T a (P N) (X N)) (P N) :=
    fun a ha N hN =>
    (HRS.MC.Sec7.S7FCF5I.fcf5_E2_window_aemeasurable_proof R r hr T hT (by omega) (P N) (X₀ N) (W N) (X N)
      (hreal N (by omega)) a ha).2
  -- moments of `ζ_N^a`
  obtain ⟨C, hC⟩ := HRS.MC.Sec7.S7FCF5R.fcf5_E3b_F5_zeta_moments_proof R r hr T hT (2 * q) hq2
  set c : ℝ≥0∞ := ENNReal.ofReal C ^ (1 / (2 * q)) with hcdef
  have hctop : c ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have hnorm : Measurable (fun u : PathSpace d r T => ENNReal.ofReal ‖u‖) :=
    ENNReal.measurable_ofReal.comp measurable_norm
  have hLz : ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
      S7FCH4_Lp (2 * q) (P N) (fun ω => ENNReal.ofReal ‖zetaWin r T a (P N) (X N) ω‖) ≤ c :=
    fun a ha N hN =>
      S7FCH4_zeta_Lp hq (hzm a ha N hN)
        (hC a ha N hN (P N) (X₀ N) (W N) (X N) (hreal N (by omega))).1.1
        (hC a ha N hN (P N) (X₀ N) (W N) (X N) (hreal N (by omega))).1.2
  -- the families of laws
  set ν : {a : ℝ // 0 ≤ a} → Measure (PathSpace d r T) := fun a => law P' (procWin r T a.1 η) with hνdef
  set μ : ℕ → {a : ℝ // 0 ≤ a} → Measure (PathSpace d r T) :=
    fun N a => if 2 ≤ N then law (P N) (zetaWin r T a.1 (P N) (X N)) else ν a with hμdef
  have hμN : ∀ N : ℕ, 2 ≤ N → ∀ a : {a : ℝ // 0 ≤ a},
      μ N a = law (P N) (zetaWin r T a.1 (P N) (X N)) := fun N hN a => if_pos hN
  haveI hνprob : ∀ a, IsProbabilityMeasure (ν a) := fun a =>
    (Measure.isProbabilityMeasure_map_iff (hpm a.1 a.2)).2 inferInstance
  haveI hμprob : ∀ N a, IsProbabilityMeasure (μ N a) := by
    intro N a
    by_cases h : 2 ≤ N
    · rw [hμN N h a]
      exact (Measure.isProbabilityMeasure_map_iff (hzm a.1 a.2 N h)).2 inferInstance
    · show IsProbabilityMeasure (if 2 ≤ N then _ else ν a)
      rw [if_neg h]
      exact hνprob a
  have hLμ : ∀ N : ℕ, 2 ≤ N → ∀ a : {a : ℝ // 0 ≤ a},
      S7FCH4_Lp (2 * q) (μ N a) (fun u => ENNReal.ofReal ‖u‖) ≤ c := by
    intro N hN a
    rw [hμN N hN a, S7FCH4_Lp_law (hzm a.1 a.2 N hN) _ hnorm]
    exact hLz a.1 a.2 N hN
  have hw : Tendsto (fun N : ℕ => ⨆ a, wassersteinE (2 * q) (μ N a) (ν a)) atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ hDq
    filter_upwards [eventually_ge_atTop 2] with N hN
    refine iSup_congr fun a => ?_
    rw [hμN N hN a]
  -- the limit windows have finite moments
  obtain ⟨N₀, hN₀, hW₀⟩ := ((eventually_ge_atTop 2).and (hw.eventually (gt_mem_nhds zero_lt_one))).exists
  have hLν : ∀ a : {a : ℝ // 0 ≤ a}, S7FCH4_Lp (2 * q) P' (fun ω => ENNReal.ofReal ‖procWin r T a.1 η ω‖) ≠ ⊤ := by
    intro a
    have hWa : wassersteinE (2 * q) (μ N₀ a) (ν a) < 1 :=
      lt_of_le_of_lt (le_iSup (fun a => wassersteinE (2 * q) (μ N₀ a) (ν a)) a) hW₀
    have h1 := S7FCH4_nu_moment hq (μ N₀ a) (ν a) hWa (hLμ N₀ hN₀ a)
    have h2 := S7FCH4_Lp_law (hpm a.1 a.2) (2 * q) hnorm
    rw [← h2]
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hctop, ENNReal.ofNat_ne_top⟩) h1
  have hνsq : ∀ a : {a : ℝ // 0 ≤ a}, Integrable (fun ω => ‖procWin r T a.1 η ω‖ ^ 2) P' := fun a =>
    S7FCH4_sq_integrable hq (hpm a.1 a.2) (hLν a)
  have hint0 : ∀ a : {a : ℝ // 0 ≤ a},
      Integrable (fun ω => S7FCH4_Y S K 0 (0 : PathSpace d r T) (procWin r T a.1 η ω)) P' := fun a =>
    S7FCH4_Y_integrable S K le_rfl (by simp) (hpm a.1 a.2) (hνsq a)
  have hY0i : ∀ a : {a : ℝ // 0 ≤ a}, Integrable (S7FCH4_Y S K 0 (0 : PathSpace d r T)) (ν a) := fun a =>
    (integrable_map_measure (S7FCH4_Y_continuous S K 0 0).aestronglyMeasurable (hpm a.1 a.2)).2 (hint0 a)
  -- the particle side
  have hm1 : ∀ᶠ N : ℕ in atTop, ∀ a : {a : ℝ // 0 ≤ a}, ‖mf a.1 N‖ ≤ 1 := by
    filter_upwards [hm.eventually (ge_mem_nhds zero_lt_one)] with N hN a
    exact ENNReal.ofReal_le_one.1
      ((le_iSup (fun a : {a : ℝ // 0 ≤ a} => ENNReal.ofReal ‖mf a.1 N‖) a).trans hN)
  have hyi : ∀ N : ℕ, 2 ≤ N → ∀ a : {a : ℝ // 0 ≤ a}, ‖mf a.1 N‖ ≤ 1 →
      Integrable (fun ω => S7FCH4_Y S K (Real.sqrt N)⁻¹ (mf a.1 N) (zetaWin r T a.1 (P N) (X N) ω)) (P N) := by
    intro N hN a hm1
    have hzsq := S7FCH4_sq_integrable hq (hzm a.1 a.2 N hN)
      (ne_top_of_le_ne_top hctop (hLz a.1 a.2 N hN))
    exact S7FCH4_Y_integrable S K (by positivity) hm1 (hzm a.1 a.2 N hN) hzsq
  have hlim := HRS.MC.Sec7.S7UCH.s7_UC_H4_limit_unif_proof hT.le hq S K μ ν (fun N a => mf a.1 N) hctop
    ((eventually_ge_atTop 2).mono fun N hN a => hLμ N hN a) hw hm
    ((((eventually_ge_atTop 2).and hm1)).mono fun N hN a => by
      rw [hμN N hN.1 a]
      exact (integrable_map_measure (S7FCH4_Y_continuous S K _ _).aestronglyMeasurable
        (hzm a.1 a.2 N hN.1)).2 (hyi N hN.1 a (hN.2 a))) hY0i
  refine Tendsto.congr' ?_ hlim
  filter_upwards [eventually_ge_atTop 2, hm1] with N hN hm1N
  refine iSup_congr fun a => ?_
  have hνa : ν a = law P' (procWin r T a.1 η) := rfl
  rw [hμN N hN a, hνa,
    S7UCW_particle_law R r hr T hT hN (P N) (X₀ N) (W N) (X N) (hreal N (by omega)) a.1 a.2 S K (mf a.1 N)
      (hmfz a.1 a.2 N hN) (hzm a.1 a.2 N hN) (hyi N hN a (hm1N a)),
    S7UCW_gauss_law hT P' η S K a.1 a.2 hmη (hcη a.1 a.2) (hpm a.1 a.2) (hνsq a) (hint0 a)]

end HRS.MC.Sec7.S7UCW

end
