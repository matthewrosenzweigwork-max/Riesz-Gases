import HRS.MC.S7UCD5
import HRS.MC.S7FCDA1

/-!
# Packet ucU, UC-D: proof of `s7_UC_D_unif` (`S7UCPlan.lean`), item (i) of `uniform_chaos`

Statement copied verbatim from `HRS/MC/S7UCPlan.lean` (checked in `HRS/MC/S7UCUTie.lean`); imports no sorried module.

Route (the proof of `S7FCDA.s7_FC_D_leading_path_clt_route_proof` with the supremum over the window start `a`):
* D4: `ε_N := ⨆_a W_2(Law windowFluc^a, Law procWin^a) → 0`;
* D5 (window `a`, `S7UCD5.lean`): `ζ_N^a = windowFluc^a - m` a.s. with `‖m‖ ≤ W_2(..)`, so
  `W_1(Law ζ_N^a, Law procWin^a) ≤ 2 ε_N` for every `a` and `N ≥ 2`;
* moments: F5 at order `p + 1` (constant independent of `a`, `N ≥ 2`), transferred for each fixed `a` to `Law procWin^a` by Fatou (D7b);
* D6 with `δ = 1`: `W_p^p ≤ W_1^{1/p} (2^{p+1} C)^{(p-1)/p} ≤ (2 ε_N)^{1/p} K`, uniformly in `a`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7UCU

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.FCF5Plan

variable {d : ℕ}

/-- The pushforward law of an a.e.-measurable map is a probability measure. -/
theorem S7UCU_prob {B : Type*} [MeasurableSpace B] {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (f : Ω → B) (hf : AEMeasurable f P) : IsProbabilityMeasure (law P f) :=
  (Measure.isProbabilityMeasure_map_iff hf).2 inferInstance

/-- The Gaussian window `procWin r T a η` is a.e. measurable for every window start `a ≥ 0`
(translation of the window-`0` case to the field `t ↦ η (a + t)`). -/
theorem S7UCU_procWin_aemeasurable {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (r T : ℝ) (hT : 0 < T) (η : ℝ → Ω' → NegSobolev d r) (a : ℝ) (ha : 0 ≤ a)
    (hm : ∀ t, Measurable (η t))
    (hc : ∀ᵐ ω ∂P', ContinuousOn (fun t => η t ω) (Set.Icc 0 (a + T))) :
    AEMeasurable (procWin r T a η) P' := by
  have h := HRS.MC.Sec7.S7FCD5B.S7FCD5B_procWin_aemeasurable P' r T hT (fun t ω => η (a + t) ω)
    (fun t => hm (a + t)) (by
      filter_upwards [hc] with ω hω
      refine hω.comp (continuousOn_const.add continuousOn_id) ?_
      intro t ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hfun : procWin r T a η = procWin r T 0 (fun t ω => η (a + t) ω) := by
    funext ω
    simp only [procWin, zero_add]
  rw [hfun]
  exact h

/-- **UC-D (item (i) of `uniform_chaos`)**: proof of `s7_UC_D_unif`. -/
theorem s7_UC_D_unif_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T)
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → Config d N)
    (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hreal : ∀ N, 1 ≤ N → PreparedRealization R.D (P N)
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) (X₀ N) (W N) (X N))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η : ℝ → Ω' → NegSobolev d r)
    (hη : IsGaussianLimitField R.D R.ρ (withDensityReal R.ρ₀) R.β₀ r P' η) (p : ℝ) (hp : 1 ≤ p) :
    Tendsto (fun N : ℕ => ⨆ a : {a : ℝ // 0 ≤ a},
        wassersteinE p (law (P N) (zetaWin r T a.1 (P N) (X N))) (law P' (procWin r T a.1 η)))
      atTop (𝓝 0) := by
  have hp0 : 0 < p := by linarith
  -- measurability of the three random paths, for every window start
  have hmE : ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 1 ≤ N →
      AEMeasurable (HRS.Main.windowFluc r T a (Real.sqrt N) (X N) R.ρ) (P N) ∧
      AEMeasurable (zetaWin r T a (P N) (X N)) (P N) := fun a ha N hN =>
    HRS.MC.Sec7.S7FCF5I.fcf5_E2_window_aemeasurable_proof R r hr T hT hN (P N) (X₀ N) (W N) (X N)
      (hreal N hN) a ha
  have hν : ∀ a : ℝ, 0 ≤ a → AEMeasurable (procWin r T a η) P' := fun a ha => by
    obtain ⟨Y₀, hY, hLin⟩ := hη
    exact S7UCU_procWin_aemeasurable P' r T hT η a ha (fun t => (hLin (a + T)).meas t) (hLin (a + T)).cont
  -- D4 and the sup bound
  have hD4 := HRS.MC.Sec7.S7FCD4.s7_FC_D4_eta_W2_proof R r hr T hT P X₀ W X hreal P' η hη
  obtain ⟨ε, hε⟩ : ∃ ε : ℕ → ℝ≥0∞, ε = fun N : ℕ => ⨆ a : {a : ℝ // 0 ≤ a},
      wassersteinE 2 (law (P N) (HRS.Main.windowFluc r T a.1 (Real.sqrt N) (X N) R.ρ))
        (law P' (procWin r T a.1 η)) := ⟨_, rfl⟩
  rw [← hε] at hD4
  have hεle : ∀ (a : ℝ) (ha : 0 ≤ a) (N : ℕ), wassersteinE 2
      (law (P N) (HRS.Main.windowFluc r T a (Real.sqrt N) (X N) R.ρ)) (law P' (procWin r T a η)) ≤ ε N :=
    fun a ha N => by
      rw [hε]
      exact le_iSup (fun a : {a : ℝ // 0 ≤ a} => wassersteinE 2
        (law (P N) (HRS.Main.windowFluc r T a.1 (Real.sqrt N) (X N) R.ρ)) (law P' (procWin r T a.1 η))) ⟨a, ha⟩
  -- D5 at window `a`
  have hD5 := HRS.MC.Sec7.S7UCD.s7_UC_D5_mean_window_proof R r hr T hT P X₀ W X hreal P' η hη
  -- `W_1(Law ζ_N^a, Law procWin^a) ≤ 2 ε_N`
  have hW1 : ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
      wassersteinE 1 (law (P N) (zetaWin r T a (P N) (X N))) (law P' (procWin r T a η)) ≤ 2 * ε N := by
    intro a ha N hN
    obtain ⟨m, hm0, hm⟩ := hD5 a ha N hN
    haveI := S7UCU_prob (P N) _ (hmE a ha N (by omega)).1
    haveI := S7UCU_prob (P N) _ (hmE a ha N (by omega)).2
    haveI := S7UCU_prob P' _ (hν a ha)
    have hX := (hmE a ha N (by omega)).1
    have hlaw : law (P N) (zetaWin r T a (P N) (X N)) =
        law (P N) (fun ω => HRS.Main.windowFluc r T a (Real.sqrt N) (X N) R.ρ ω + (-m)) := by
      refine Measure.map_congr ?_
      filter_upwards [hm] with ω hω
      rw [hω, sub_eq_add_neg]
    have hZE := wassersteinE_translate (P N) 1 le_rfl _ hX (-m) 0
    simp only [add_zero, sub_zero, norm_neg] at hZE
    rw [← hlaw] at hZE
    have h2 := hεle a ha N
    calc wassersteinE 1 (law (P N) (zetaWin r T a (P N) (X N))) (law P' (procWin r T a η))
        ≤ wassersteinE 1 (law (P N) (zetaWin r T a (P N) (X N)))
            (law (P N) (HRS.Main.windowFluc r T a (Real.sqrt N) (X N) R.ρ)) +
          wassersteinE 1 (law (P N) (HRS.Main.windowFluc r T a (Real.sqrt N) (X N) R.ρ))
            (law P' (procWin r T a η)) := by
          haveI := S7UCU_prob (P N) _ hX
          exact wassersteinE_triangle 1 le_rfl _ _ _
      _ ≤ ε N + ε N := by
          refine add_le_add (hZE.trans (hm0.trans h2)) ((wassersteinE_one_le_two _ _).trans h2)
      _ = 2 * ε N := (two_mul _).symm
  have h2ε : Tendsto (fun N => 2 * ε N) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul hD4 (Or.inr (by simp : (2 : ℝ≥0∞) ≠ ⊤))
    simpa using this
  -- moments (F5 at order `p + 1`, constant uniform in `a` and `N ≥ 2`)
  obtain ⟨C, hC⟩ := HRS.MC.Sec7.S7FCF5R.fcf5_E3b_F5_zeta_moments_proof R r hr T hT (p + 1) (by linarith)
  have hmomZ : ∀ a : ℝ, 0 ≤ a → ∀ N, 2 ≤ N →
      ∫⁻ x, ‖x‖ₑ ^ (p + 1) ∂(law (P N) (zetaWin r T a (P N) (X N))) ≤ ENNReal.ofReal C := by
    intro a ha N hN
    obtain ⟨⟨hI, hb⟩, _⟩ := hC a ha N hN (P N) (X₀ N) (W N) (X N) (hreal N (by omega))
    rw [HRS.MC.Sec7.S7FCDA.S7FCDA_lintegral_law _ _ (hmE a ha N (by omega)).2]
    exact HRS.MC.Sec7.S7FCDA.S7FCDA_lintegral_le _ _ _ _ (by linarith) hI hb
  -- Fatou transfer to the Gaussian window, for each fixed `a`
  have hmomν : ∀ a : ℝ, 0 ≤ a → ∫⁻ x, ‖x‖ₑ ^ (p + 1) ∂(law P' (procWin r T a η)) ≤ ENNReal.ofReal C := by
    intro a ha
    haveI := S7UCU_prob P' _ (hν a ha)
    haveI : ∀ n : ℕ, IsProbabilityMeasure (law (P (n + 2)) (zetaWin r T a (P (n + 2)) (X (n + 2)))) :=
      fun n => S7UCU_prob (P (n + 2)) _ (hmE a ha (n + 2) (by omega)).2
    have hW1' : Tendsto (fun n : ℕ => wassersteinE 1
        (law (P (n + 2)) (zetaWin r T a (P (n + 2)) (X (n + 2)))) (law P' (procWin r T a η))) atTop (𝓝 0) := by
      have h2' : Tendsto (fun n : ℕ => 2 * ε (n + 2)) atTop (𝓝 0) :=
        (tendsto_add_atTop_iff_nat (f := fun N => 2 * ε N) 2).2 h2ε
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2' (fun _ => zero_le)
        (fun n => hW1 a ha (n + 2) (by omega))
    have h7 := HRS.MC.Sec7.S7FCW1.s7_FC_D7b_fatou_proof
      (fun n => law (P (n + 2)) (zetaWin r T a (P (n + 2)) (X (n + 2)))) (law P' (procWin r T a η))
      hW1' (p + 1) (by linarith)
    refine h7.trans ?_
    calc _ ≤ liminf (fun _ : ℕ => ENNReal.ofReal C) atTop :=
          liminf_le_liminf (Eventually.of_forall fun n => hmomZ a ha (n + 2) (by omega))
      _ = _ := liminf_const _
  -- D6 and the supremum
  have hMfin : ENNReal.ofReal C ≠ ⊤ := ENNReal.ofReal_ne_top
  have hconst : ((2 : ℝ≥0∞) ^ (p + 1) * ENNReal.ofReal C) ^ ((p - 1) / (p + 1 - 1)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (div_nonneg (by linarith) (by linarith))
      (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top) hMfin)
  set K : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ (p + 1) * ENNReal.ofReal C) ^ ((p - 1) / (p + 1 - 1)) with hK
  have hexp : (0 : ℝ) ≤ 1 / (p + 1 - 1) := by
    rw [show p + 1 - 1 = p by ring]; positivity
  have hg : Tendsto (fun N => (2 * ε N) ^ (1 / (p + 1 - 1)) * K) atTop (𝓝 0) := by
    have hA : Tendsto (fun N => (2 * ε N) ^ (1 / (p + 1 - 1))) atTop (𝓝 0) := by
      have h := ((ENNReal.continuous_rpow_const (y := 1 / (p + 1 - 1))).tendsto 0).comp h2ε
      rwa [ENNReal.zero_rpow_of_pos (by rw [show p + 1 - 1 = p by ring]; positivity)] at h
    have hB := ENNReal.Tendsto.mul_const hA (Or.inr hconst)
    rwa [zero_mul] at hB
  have hg' : Tendsto (fun N => ((2 * ε N) ^ (1 / (p + 1 - 1)) * K) ^ p⁻¹) atTop (𝓝 0) := by
    have h := ((ENNReal.continuous_rpow_const (y := p⁻¹)).tendsto 0).comp hg
    rwa [ENNReal.zero_rpow_of_pos (inv_pos.2 hp0)] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg'
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  refine iSup_le fun a => ?_
  obtain ⟨a, ha⟩ := a
  haveI := S7UCU_prob (P N) _ (hmE a ha N (by omega)).2
  haveI := S7UCU_prob P' _ (hν a ha)
  have hD6 := HRS.MC.Sec7.S7FCW1.s7_FC_D6_interp_proof
    (law (P N) (zetaWin r T a (P N) (X N))) (law P' (procWin r T a η)) p 1 hp one_pos (ENNReal.ofReal C) hMfin
    (hmomZ a ha N hN) (hmomν a ha)
  have h1 : wassersteinE p (law (P N) (zetaWin r T a (P N) (X N))) (law P' (procWin r T a η)) ^ p ≤
      (2 * ε N) ^ (1 / (p + 1 - 1)) * K := by
    refine hD6.trans ?_
    rw [show (1 : ℝ) / (p + 1 - 1) = 1 / (p + 1 - 1) from rfl]
    exact mul_le_mul' (ENNReal.rpow_le_rpow (hW1 a ha N hN) hexp) le_rfl
  have h3 := ENNReal.rpow_le_rpow h1 (inv_nonneg.2 hp0.le)
  rwa [ENNReal.rpow_rpow_inv hp0.ne'] at h3

end HRS.MC.Sec7.S7UCU

end
