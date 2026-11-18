import HRS.Main.ThermLin2Fu21
import HRS.Main.ThermLin2E1c

/-!
# THERMLIN2 E1d: `tl2_zero_start_comparison_proof`

USES THE PLAN STATEMENT `tl2_remainder_bound` (B5) AS A BLACK BOX (marked below; to be swapped for
`tl2_remainder_bound_proof` at integration).  See `ThermLin2E1c` for the route.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P

variable {d : ℕ}

open Classical in
/-- `windowPath` at `ω` only depends on the values of the process at `ω`. -/
lemma tl2E1_window_congr {a T : ℝ} {Ω : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X Y : ℝ → Ω → E} {ω : Ω} (h : ∀ t, Y t ω = X t ω) :
    Uniform.windowPath a T X ω = Uniform.windowPath a T Y ω := by
  have e : (fun t : Set.Icc (0 : ℝ) T => X (a + (t : ℝ)) ω) = fun t : Set.Icc (0 : ℝ) T => Y (a + (t : ℝ)) ω :=
    funext fun t => (h _).symm
  have key : ∀ (f g : Set.Icc (0 : ℝ) T → E), f = g →
      (if hf : Continuous f then (⟨f, hf⟩ : C(Set.Icc (0 : ℝ) T, E)) else 0) =
        (if hg : Continuous g then (⟨g, hg⟩ : C(Set.Icc (0 : ℝ) T, E)) else 0) := by
    rintro f g rfl
    rfl
  unfold Uniform.windowPath
  exact key _ _ e

/-- E1 (proof).  Uses the plan statement `tl2_remainder_bound` (B5) as a black box. -/
theorem tl2_zero_start_comparison_proof (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ) (hT : 0 < T) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ a : ℝ, 0 ≤ a → ∀ (p : ℝ), (p = 1 ∨ p = 2) →
      ∀ {Ωg : Type} [mΩg : MeasurableSpace Ωg] (Pg : Measure Ωg) [IsProbabilityMeasure Pg] {ℱ : Filtration ℝ mΩg}
        (G Zs : ℝ → Ωg → NegSobolev d m) (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m),
        IsDualEvolution S.dyn S.ρ m Vev → (∀ T' : ℝ, 0 ≤ T' → IsPlainEvolution Vev T') →
        IsHilbertMartingaleWithCovariation Pg ℱ (a + T) G (fun r _ => covDensT m S.β⁻¹ (a + T) S.ρ r) →
        (∀ ω, Continuous fun s => G s ω) → (∀ ω, G 0 ω = 0) →
        (∀ t ∈ Set.Icc (0 : ℝ) (a + T),
          IsStochConv Pg Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zs t)) →
        (∀ t, Measurable (Zs t)) → (∀ᵐ ω ∂Pg, ContinuousOn (fun t => Zs t ω) (Set.Icc 0 (a + T))) →
      ∀ (Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m), IsDualEvolution S.dyn (fun _ => ρβ) m Wev →
      (∀ T' : ℝ, 0 ≤ T' → IsPlainEvolution Wev T') →
      ∀ {Ω₂ : Type} [mΩ₂ : MeasurableSpace Ω₂] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂] {ℱ₂ : Filtration ℝ mΩ₂}
        (Ĝ Zb : ℝ → Ω₂ → NegSobolev d m),
        IsHilbertMartingaleWithCovariation P₂ ℱ₂ (a + T) Ĝ (fun r _ => tl2CbDens S ρβ m (a + T) r) →
        (∀ t ∈ Set.Icc (0 : ℝ) (a + T),
          IsStochConv P₂ Wev (ContinuousLinearMap.id ℝ (NegSobolev d m)) Ĝ 0 t (Zb t)) →
        (∀ t, Measurable (Zb t)) → (∀ᵐ ω ∂P₂, ContinuousOn (fun t => Zb t ω) (Set.Icc 0 (a + T))) →
        wassersteinE p (law Pg (Uniform.windowPath a T Zs)) (law P₂ (Uniform.windowPath a T Zb)) ≤
          ENNReal.ofReal (C * Real.exp (-c * a)) := by
  classical
  obtain ⟨Cw, cw, hCw, hcw, W₀, hW₀d, hW₀ev⟩ := tl2_Wpkg_proof S h m
  obtain ⟨Cmax, hCmax, hEv⟩ := hW₀ev T hT
  obtain ⟨K₀, c₀, hK₀, hc₀, hVdec⟩ := tl2_Vev_decay_proof S m hm
  -- BLACK BOX: plan statement `tl2_remainder_bound` (B5)
  obtain ⟨CR, κ, hCR, hκ, hRem⟩ := tl2_remainder_bound_proof S h m hm
  obtain ⟨M, hM0, hMom⟩ := tl2_Zw_moment_proof S h m hm
  obtain ⟨Cn, cn, hCn, hcn, hNoise⟩ := tl2_noise_cost_proof S h m hm T hT cw hcw
  obtain ⟨Cφ, cφ, hCφ, hcφ, hΦ⟩ := tl2E1_phi (c := c₀) (κ := κ) (T := T) hc₀ hκ hT
  obtain ⟨A, hA, hStage⟩ := t25p_stage2 (K := Cw) (c := cw) hCw.le hcw.le hT W₀ hEv
  set K : ℝ := max K₀ Cw with hKdef
  have hKnn : 0 ≤ K := (le_max_right _ _).trans' hCw.le
  set A2 : ℝ := 2 * (Cw ^ 2 + Real.sqrt Cmax) + Cw + 1 with hA2
  have hA2nn : 0 ≤ A2 := by positivity
  set c : ℝ := min cφ (cn / 2) with hcdef
  have hc0 : 0 < c := lt_min hcφ (half_pos hcn)
  set C : ℝ := CR * K * Cφ * Real.sqrt M + A2 * Real.sqrt Cn + 1 with hCdef
  have hC0 : 0 < C := by positivity
  refine ⟨C, c, hC0, hc0, ?_⟩
  intro a ha p hp Ωg _ Pg _ ℱ G Zs Vev hVd hVp hG hGc hGz hZs hZsm hZsc Wev hWd hWp Ω₂ _ P₂ _ ℱ₂ Ĝ Zb hĜ hZb hZbm hZbc
  have hpos : 0 < a + T := by linarith
  -- bounds of `W₀`
  have hWb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ a + T → ‖W₀ t r‖ ≤ Cw := by
    intro r t hr hrt _
    refine (hEv.decay r t hr hrt).trans ?_
    have : Real.exp (-cw * (t - r)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    nlinarith
  have hWbK : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ a + T → ‖W₀ t r‖ ≤ K := fun r t hr hrt ht =>
    (hWb r t hr hrt ht).trans (le_max_right _ _)
  have hVbK : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ a + T → ‖Vev t u‖ ≤ K * Real.exp (-c₀ * (t - u)) := by
    intro u t hu hut _
    refine (hVdec Vev hVd hVp u t hu hut).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  -- the convolution `Zw`
  obtain ⟨Zw₀, hZw₀c, hZw₀cont, hZw₀m⟩ := hEv.exists_conv (a + T) hpos Ωg Pg ℱ G
    (fun r _ => covDensT m S.β⁻¹ (a + T) S.ρ r) hG
  obtain ⟨Zw, hZwm, hZwc, hZwae⟩ := gf_measurable_modification_proof Pg (a + T) Zw₀ hZw₀cont hZw₀m
  have hZwconv : ∀ t ∈ Set.Icc (0 : ℝ) (a + T),
      IsStochConv Pg W₀ (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zw t) := fun t ht =>
    tl2E1_sc_ae_congr Pg W₀ _ (hZwae t ht) (hZw₀c t ht)
  -- Bm
  set Bm : Ωg → ℝ≥0∞ := tl2E1_Bm m (PDE.MFAdjoint.aExp d S.s) a T c₀ κ (CR * K) Zw with hBm
  have hBmm : Measurable Bm :=
    tl2E1_Bm_measurable m (PDE.MFAdjoint.aExp d S.s) a T c₀ κ (CR * K) hpos.le Zw hZwm hZwc
  have hmom := fun r (hr : r ∈ Set.Icc (0 : ℝ) (a + T)) =>
    hMom hpos W₀ hW₀d (hEv.plain _ hpos.le) Pg G hG hGc hGz Zw hZwconv hZwm r hr
  have hBmsq := tl2E1_Bm_sq (b := PDE.MFAdjoint.aExp d S.s) (c₀ := c₀) (κ := κ) (mul_nonneg hCR hKnn) hM0 hCφ hpos.le
    Pg Zw hZwm hZwc ha hT hmom (hΦ a ha)
  -- the pathwise bound
  have hrem := hRem hpos hKnn hc₀ Vev W₀ hVd (hVp _ hpos.le) hVbK hW₀d (hEv.plain _ hpos.le) hWbK Pg G hG hGc hGz Zs Zw
    hZs hZwconv hZsm hZwm hZsc (Filter.Eventually.of_forall hZwc)
  have hbd : ∀ᵐ ω ∂Pg, ∀ t ∈ Set.Icc a (a + T), ‖(Zs t ω - Zw t ω)‖ₑ ≤ Bm ω := by
    filter_upwards [hrem] with ω hω t ht
    exact (hω t ⟨ha.trans ht.1, ht.2⟩).trans (tl2E1_Bm_ge (mul_nonneg hCR hKnn) hc₀.le ha hT ht Zw ω)
  -- the target and `hid`
  have hCb := tl2_CbDens_det_proof S h m hm hpos
  have hCb0 : ∀ σ : ℝ, σ ∉ Set.Icc 0 (a + T) → tl2CbDens S ρβ m (a + T) σ = 0 := by
    intro σ hσ
    unfold tl2CbDens covDensT
    rw [if_neg hσ]
  have hZb' : ∀ t ∈ Set.Icc (0 : ℝ) (a + T),
      IsStochConv P₂ W₀ (ContinuousLinearMap.id ℝ (NegSobolev d m)) Ĝ 0 t (Zb t) := fun t ht =>
    tl2E1_sc_evo_congr P₂ Wev W₀ _ ht.1 (fun s hs hst => t25p_dual_unique hWd hW₀d hs hst) (hZb t ht)
  have hid : ∀ (Ω₃ : Type) [mΩ₃ : MeasurableSpace Ω₃] (P₃ : Measure Ω₃) [IsProbabilityMeasure P₃]
      (ℱ₃ : Filtration ℝ mΩ₃) (ξ : Ω₃ → NegSobolev d m) (G₃ : ℝ → Ω₃ → NegSobolev d m),
      Measurable ξ →
      IsHilbertMartingaleWithCovariation P₃ ℱ₃ (a + T) G₃ (fun r _ => tl2CbDens S ρβ m (a + T) r) →
      Indep (MeasurableSpace.comap ξ inferInstance)
        (⨆ τ ∈ Set.Icc (0 : ℝ) (a + T), MeasurableSpace.comap (G₃ τ) inferInstance) P₃ →
      P₃.map ξ = Pg.map (fun _ => (0 : NegSobolev d m)) →
      ∀ Zb₃ : ℝ → Ω₃ → NegSobolev d m,
        (∀ t ∈ Set.Icc (0 : ℝ) (a + T),
          IsStochConv P₃ W₀ (ContinuousLinearMap.id ℝ (NegSobolev d m)) G₃ 0 t (Zb₃ t)) →
        (∀ᵐ ω ∂P₃, ContinuousOn (fun t => Zb₃ t ω) (Set.Icc 0 (a + T))) →
        (∀ t, Measurable (Zb₃ t)) →
        law P₂ (Uniform.windowPath a T Zb) =
          law P₃ (Uniform.windowPath a T (fun t ω => W₀ t 0 (ξ ω) + Zb₃ t ω)) := by
    intro Ω₃ _ P₃ _ ℱ₃ ξ G₃ hξm hG₃ _ hmap Zb₃ hZ₃ hZ₃c hZ₃m
    have hξ0 : ∀ᵐ ω ∂P₃, ξ ω = 0 := by
      have h1 : P₃.map ξ = Measure.dirac 0 := by
        rw [hmap, Measure.map_const, measure_univ, one_smul]
      have h2 : ∀ᵐ x ∂(P₃.map ξ), x ∈ ({0} : Set (NegSobolev d m)) := by
        rw [h1]
        exact (ae_dirac_iff (measurableSet_singleton 0)).2 rfl
      exact (ae_map_iff hξm.aemeasurable (measurableSet_singleton 0)).1 h2
    have hlaw := tl2_zero_start_law_unique_proof hT ha hCw.le W₀ (hEv.plain _ hpos.le) hWb
      (tl2CbDens S ρβ m (a + T)) P₂ P₃ Ĝ Zb G₃ Zb₃ hĜ hG₃ hCb0 hZb' hZ₃ hZbm hZ₃m hZbc hZ₃c
    rw [hlaw]
    refine Measure.map_congr ?_
    filter_upwards [hξ0] with ω hω
    exact tl2E1_window_congr (fun t => by simp [hω])
  have key := (hStage a ha Ωg Pg ℱ (fun _ => 0) (fun _ => 0) measurable_const measurable_const G
    (fun r _ => covDensT m S.β⁻¹ (a + T) S.ρ r) hG (tl2CbDens S ρβ m (a + T)) hCb.1 hCb.2 Zw
    (fun t ω => Zs t ω - Zw t ω) Zs hZwconv (Filter.Eventually.of_forall hZwc) hZwm
    (by
      filter_upwards [hZsc] with ω hω
      exact hω.sub (hZwc ω))
    (fun t => (hZsm t).sub (hZwm t))
    (fun t _ ω => by simp)
    Bm hBmm.aemeasurable hbd (law P₂ (Uniform.windowPath a T Zb)) hid).2 p hp
  have hp0 : 0 < p := by rcases hp with rfl | rfl <;> norm_num
  have t2 : (∫⁻ ω, Bm ω ^ p ∂Pg) ^ (1 / p) ≤
      ENNReal.ofReal (CR * K * (Cφ * Real.exp (-cφ * a)) * Real.sqrt M) :=
    tl2E1_p_le Pg hBmm.aemeasurable hBmsq hp
  refine key.trans ?_
  have hq0 : 0 ≤ Real.sqrt Cn * Real.exp (-(cn / 2) * a) := by positivity
  have hX1 : 0 ≤ CR * K * (Cφ * Real.exp (-cφ * a)) * Real.sqrt M := by positivity
  have hE1 : Real.exp (-cφ * a) ≤ Real.exp (-c * a) := Real.exp_le_exp.2 (by
    nlinarith [min_le_left cφ (cn / 2)])
  have hE2 : Real.exp (-(cn / 2) * a) ≤ Real.exp (-c * a) := Real.exp_le_exp.2 (by
    nlinarith [min_le_right cφ (cn / 2)])
  calc _ ≤ (0 : ℝ≥0∞) + ENNReal.ofReal (CR * K * (Cφ * Real.exp (-cφ * a)) * Real.sqrt M) +
        ENNReal.ofReal A2 * ENNReal.ofReal (Real.sqrt Cn * Real.exp (-(cn / 2) * a)) := by
        refine add_le_add (add_le_add ?_ t2) (mul_le_mul' le_rfl ?_)
        · refine le_of_eq ?_
          simp [ENNReal.zero_rpow_of_pos hp0, hp0]
        · refine tl2E1_sqrt_le hCn ?_
          rw [lintegral_const, measure_univ, mul_one]
          exact hNoise a ha
    _ = ENNReal.ofReal (CR * K * (Cφ * Real.exp (-cφ * a)) * Real.sqrt M + A2 * (Real.sqrt Cn * Real.exp (-(cn / 2) * a))) := by
        rw [zero_add, ← ENNReal.ofReal_mul hA2nn, ← ENNReal.ofReal_add hX1 (mul_nonneg hA2nn hq0)]
    _ ≤ ENNReal.ofReal (C * Real.exp (-c * a)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hs1 : 0 ≤ CR * K * Cφ * Real.sqrt M := by positivity
        have hs2 : 0 ≤ A2 * Real.sqrt Cn := by positivity
        have hEp : 0 < Real.exp (-c * a) := Real.exp_pos _
        calc CR * K * (Cφ * Real.exp (-cφ * a)) * Real.sqrt M + A2 * (Real.sqrt Cn * Real.exp (-(cn / 2) * a))
            = (CR * K * Cφ * Real.sqrt M) * Real.exp (-cφ * a) + (A2 * Real.sqrt Cn) * Real.exp (-(cn / 2) * a) := by ring
          _ ≤ (CR * K * Cφ * Real.sqrt M) * Real.exp (-c * a) + (A2 * Real.sqrt Cn) * Real.exp (-c * a) :=
              add_le_add (mul_le_mul_of_nonneg_left hE1 hs1) (mul_le_mul_of_nonneg_left hE2 hs2)
          _ ≤ C * Real.exp (-c * a) := by
              rw [hCdef]; nlinarith

example := (@tl2_zero_start_comparison_proof : type_of% @tl2_zero_start_comparison)

end HRS.ThermLin.Plan2
