import HRS.MC.S7FCDefs
import HRS.MC.S7FCD5
import HRS.MC.S7FCD4
import HRS.MC.S7FCF5RE3b
import HRS.MC.S7FCW1D6
import HRS.MC.S7FCW1W

/-!
# Packet fcf5u, FC-D assembly: proof of `s7_FC_D_leading_path_clt_route` (`S7FCPlan.lean`)

Statement copied verbatim from `HRS/MC/S7FCPlan.lean` (checked in `HRS/MC/S7FCDATie.lean`); imports no sorried module.

Route:
* `η_N` window (`windowFluc`, `a = 0`) converges to the Gaussian window in `W_2` (D4, term `a = 0`), hence in `W_1`;
* `ζ_N = η_N - m_N` a.s. with `‖m_N‖ → 0` (D5), so `W_1(Law ζ_N, Law η_N) ≤ ‖m_N‖` (`wassersteinE_translate`) and
  `W_1(Law ζ_N, Law η) → 0` (`wassersteinE_triangle`); weak convergence is D7a on the shifted sequence `N ↦ N + 2`;
* `W_q` convergence: D6 with `δ = 1`, the moment bound for `Law ζ_N` from F5 at exponent `q + 1`, and for the Gaussian
  path law from D7b (Fatou) and the same F5 bound.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCDA

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan

variable {d : ℕ}

/-- `∫⁻ ‖x‖ₑ^p` against a pushforward by an a.e.-measurable map. -/
theorem S7FCDA_lintegral_law {B : Type*} [NormedAddCommGroup B] [MeasurableSpace B] [BorelSpace B]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z : Ω → B) (hZ : AEMeasurable Z P) (p : ℝ) :
    ∫⁻ x, ‖x‖ₑ ^ p ∂(law P Z) = ∫⁻ ω, ‖Z ω‖ₑ ^ p ∂P :=
  lintegral_map' (measurable_enorm.pow_const p).aemeasurable hZ

/-- An integrable real moment bounded by `C` bounds the `lintegral` moment by `ofReal C`. -/
theorem S7FCDA_lintegral_le {B : Type*} [NormedAddCommGroup B] {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → B) (p C : ℝ) (hp : 0 ≤ p)
    (hI : Integrable (fun ω => ‖Z ω‖ ^ p) P) (hC : ∫ ω, ‖Z ω‖ ^ p ∂P ≤ C) :
    ∫⁻ ω, ‖Z ω‖ₑ ^ p ∂P ≤ ENNReal.ofReal C := by
  have hof : ∀ ω, ‖Z ω‖ₑ ^ p = ENNReal.ofReal (‖Z ω‖ ^ p) := fun ω => by
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp]
  simp only [hof]
  rw [← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun ω => Real.rpow_nonneg (norm_nonneg _) p)]
  exact ENNReal.ofReal_le_ofReal hC

/-- Passing from `W_p → 0` through `(·)^q`: if `x_N ^ q → 0` for `q > 0` then `x_N → 0`. -/
theorem S7FCDA_tendsto_of_rpow {x : ℕ → ℝ≥0∞} {q : ℝ} (hq : 0 < q)
    (h : Tendsto (fun N => x N ^ q) atTop (𝓝 0)) : Tendsto x atTop (𝓝 0) := by
  have h2 : Tendsto (fun N => (x N ^ q) ^ q⁻¹) atTop (𝓝 (0 ^ q⁻¹)) :=
    (ENNReal.continuous_rpow_const.tendsto 0).comp h
  rw [ENNReal.zero_rpow_of_pos (inv_pos.2 hq)] at h2
  refine h2.congr fun N => ?_
  exact ENNReal.rpow_rpow_inv hq.ne' (x N)

/-- **FC-D with the corrected route**, proof of `s7_FC_D_leading_path_clt_route`. -/
theorem s7_FC_D_leading_path_clt_route_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T)
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → Config d N)
    (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hreal : ∀ N, 1 ≤ N → PreparedRealization R.D (P N)
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) (X₀ N) (W N) (X N))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η : ℝ → Ω' → NegSobolev d r) (hη : IsGaussianLimitField R.D R.ρ (withDensityReal R.ρ₀) R.β₀ r P' η) :
    (∀ G : PathSpace d r T → ℝ, Continuous G → (∃ M, ∀ z, |G z| ≤ M) →
      Tendsto (fun N : ℕ => ∫ ω, G (zetaWin r T 0 (P N) (X N) ω) ∂(P N)) atTop
        (𝓝 (∫ ω, G (procWin r T 0 η ω) ∂P'))) ∧
    (∀ q : ℝ, 1 ≤ q → Tendsto (fun N : ℕ => wassersteinE q (law (P N) (zetaWin r T 0 (P N) (X N)))
        (law P' (procWin r T 0 η))) atTop (𝓝 0)) := by
  -- measurability of the three random paths
  have hmE : ∀ N : ℕ, 1 ≤ N → AEMeasurable (HRS.Main.windowFluc r T 0 (Real.sqrt N) (X N) R.ρ) (P N) ∧
      AEMeasurable (zetaWin r T 0 (P N) (X N)) (P N) := fun N hN =>
    HRS.MC.Sec7.S7FCF5I.fcf5_E2_window_aemeasurable_proof R r hr T hT hN (P N) (X₀ N) (W N) (X N)
      (hreal N hN) 0 le_rfl
  have hν : AEMeasurable (procWin r T 0 η) P' := by
    obtain ⟨Y₀, hY, hLin⟩ := hη
    exact HRS.MC.Sec7.S7FCD5B.S7FCD5B_procWin_aemeasurable P' r T hT η (fun t => (hLin T).meas t) (hLin T).cont
  -- the three families of laws
  obtain ⟨μE, hμE⟩ : ∃ μE : ℕ → Measure (PathSpace d r T), ∀ N,
      μE N = law (P N) (HRS.Main.windowFluc r T 0 (Real.sqrt N) (X N) R.ρ) := ⟨_, fun _ => rfl⟩
  obtain ⟨μZ, hμZ⟩ : ∃ μZ : ℕ → Measure (PathSpace d r T), ∀ N,
      μZ N = law (P N) (zetaWin r T 0 (P N) (X N)) := ⟨_, fun _ => rfl⟩
  obtain ⟨ν, hνd⟩ : ∃ ν : Measure (PathSpace d r T), ν = law P' (procWin r T 0 η) := ⟨_, rfl⟩
  have hpE : ∀ N, 1 ≤ N → IsProbabilityMeasure (μE N) := fun N hN => by
    rw [hμE]; exact (Measure.isProbabilityMeasure_map_iff (hmE N hN).1).2 inferInstance
  have hpZ : ∀ N, 1 ≤ N → IsProbabilityMeasure (μZ N) := fun N hN => by
    rw [hμZ]; exact (Measure.isProbabilityMeasure_map_iff (hmE N hN).2).2 inferInstance
  have hpν : IsProbabilityMeasure ν := by
    rw [hνd]; exact (Measure.isProbabilityMeasure_map_iff hν).2 inferInstance
  -- D5 and D4
  obtain ⟨m, hm0, hm⟩ := HRS.MC.Sec7.S7FCD5.s7_FC_D5_mean_proof R r hr T hT P X₀ W X hreal P' η hη
  have hD4 := HRS.MC.Sec7.S7FCD4.s7_FC_D4_eta_W2_proof R r hr T hT P X₀ W X hreal P' η hη
  have hW2 : Tendsto (fun N : ℕ => wassersteinE 2 (μE N) ν) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hD4 (fun _ => zero_le) (fun N => ?_)
    rw [hμE, hνd]
    exact le_iSup (fun a : {a : ℝ // 0 ≤ a} =>
      wassersteinE 2 (law (P N) (HRS.Main.windowFluc r T a.1 (Real.sqrt N) (X N) R.ρ))
        (law P' (procWin r T a.1 η))) ⟨0, le_rfl⟩
  -- `W_1(Law ζ_N, Law η_N) ≤ ‖m_N‖`
  have hZE : ∀ N : ℕ, 2 ≤ N → wassersteinE 1 (μZ N) (μE N) ≤ ENNReal.ofReal ‖m N‖ := by
    intro N hN
    haveI := hpE N (by omega)
    have hX := (hmE N (by omega)).1
    have hlaw : μZ N = law (P N) (fun ω => HRS.Main.windowFluc r T 0 (Real.sqrt N) (X N) R.ρ ω + (-m N)) := by
      rw [hμZ]
      refine Measure.map_congr ?_
      filter_upwards [hm N hN] with ω hω
      rw [hω, sub_eq_add_neg]
    have h := wassersteinE_translate (P N) 1 le_rfl _ hX (-m N) 0
    simp only [add_zero, sub_zero, norm_neg] at h
    rw [hlaw, hμE]
    exact h
  -- `W_1(Law ζ_N, Law η) → 0`
  have hW1 : Tendsto (fun N : ℕ => wassersteinE 1 (μZ N) ν) atTop (𝓝 0) := by
    have hsum : Tendsto (fun N : ℕ => ENNReal.ofReal ‖m N‖ + wassersteinE 2 (μE N) ν) atTop (𝓝 0) := by
      have h1 : Tendsto (fun N : ℕ => ENNReal.ofReal ‖m N‖) atTop (𝓝 0) := by
        have := ENNReal.tendsto_ofReal hm0
        simpa using this
      simpa using h1.add hW2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    haveI := hpE N (by omega)
    haveI := hpZ N (by omega)
    haveI := hpν
    calc wassersteinE 1 (μZ N) ν ≤ wassersteinE 1 (μZ N) (μE N) + wassersteinE 1 (μE N) ν :=
          wassersteinE_triangle 1 le_rfl _ _ _
      _ ≤ ENNReal.ofReal ‖m N‖ + wassersteinE 2 (μE N) ν :=
          add_le_add (hZE N hN) (wassersteinE_one_le_two _ _)
  -- shifted sequence
  haveI hpZ' : ∀ n, IsProbabilityMeasure (μZ (n + 2)) := fun n => hpZ (n + 2) (by omega)
  haveI := hpν
  have hW1' : Tendsto (fun n : ℕ => wassersteinE 1 (μZ (n + 2)) ν) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat (f := fun N => wassersteinE 1 (μZ N) ν) 2).2 hW1
  refine ⟨?_, ?_⟩
  · intro G hG hGb
    have h := HRS.MC.Sec7.S7FCW1.s7_FC_D7a_weak_proof (fun n => μZ (n + 2)) ν hW1' G hG hGb
    have hint : ∀ N, 1 ≤ N → ∫ z, G z ∂(μZ N) = ∫ ω, G (zetaWin r T 0 (P N) (X N) ω) ∂(P N) := fun N hN => by
      rw [hμZ]; exact integral_map (hmE N hN).2 hG.aestronglyMeasurable
    have hintν : ∫ z, G z ∂ν = ∫ ω, G (procWin r T 0 η ω) ∂P' := by
      rw [hνd]; exact integral_map hν hG.aestronglyMeasurable
    rw [← hintν]
    refine (tendsto_add_atTop_iff_nat (f := fun N : ℕ => ∫ ω, G (zetaWin r T 0 (P N) (X N) ω) ∂(P N)) 2).1 ?_
    exact h.congr fun n => hint (n + 2) (by omega)
  · intro q hq
    have hq0 : 0 < q := by linarith
    obtain ⟨C, hC⟩ := HRS.MC.Sec7.S7FCF5R.fcf5_E3b_F5_zeta_moments_proof R r hr T hT (q + 1) (by linarith)
    have hmomZ : ∀ N, 2 ≤ N → ∫⁻ x, ‖x‖ₑ ^ (q + 1) ∂(μZ N) ≤ ENNReal.ofReal C := by
      intro N hN
      obtain ⟨⟨hI, hb⟩, _⟩ := hC 0 le_rfl N hN (P N) (X₀ N) (W N) (X N) (hreal N (by omega))
      rw [hμZ, S7FCDA_lintegral_law _ _ (hmE N (by omega)).2]
      exact S7FCDA_lintegral_le _ _ _ _ (by linarith) hI hb
    have hmomν : ∫⁻ x, ‖x‖ₑ ^ (q + 1) ∂ν ≤ ENNReal.ofReal C := by
      have h7 := HRS.MC.Sec7.S7FCW1.s7_FC_D7b_fatou_proof (fun n => μZ (n + 2)) ν hW1' (q + 1) (by linarith)
      refine h7.trans ?_
      calc _ ≤ liminf (fun _ : ℕ => ENNReal.ofReal C) atTop :=
            liminf_le_liminf (Eventually.of_forall fun n => hmomZ (n + 2) (by omega))
        _ = _ := liminf_const _
    have hMfin : ENNReal.ofReal C ≠ ⊤ := ENNReal.ofReal_ne_top
    have hconst : ((2 : ℝ≥0∞) ^ (q + 1) * ENNReal.ofReal C) ^ ((q - 1) / (q + 1 - 1)) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (div_nonneg (by linarith) (by linarith))
        (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top) hMfin)
    have hA : Tendsto (fun N => wassersteinE 1 (μZ N) ν ^ (1 / (q + 1 - 1))) atTop (𝓝 0) := by
      have h := ((ENNReal.continuous_rpow_const (y := 1 / (q + 1 - 1))).tendsto 0).comp hW1
      rwa [ENNReal.zero_rpow_of_pos (by rw [show q + 1 - 1 = q by ring]; positivity)] at h
    have hB := ENNReal.Tendsto.mul_const hA (Or.inr hconst)
    rw [zero_mul] at hB
    have hq1 : Tendsto (fun N => wassersteinE q (μZ N) ν ^ q) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hB
        (Eventually.of_forall fun _ => zero_le) ?_
      filter_upwards [eventually_ge_atTop 2] with N hN
      haveI := hpZ N (by omega)
      exact HRS.MC.Sec7.S7FCW1.s7_FC_D6_interp_proof (μZ N) ν q 1 hq one_pos (ENNReal.ofReal C) hMfin
        (hmomZ N hN) hmomν
    have h := S7FCDA_tendsto_of_rpow hq0 hq1
    simpa only [hμZ, hνd] using h

end HRS.MC.Sec7.S7FCDA

end
