import HRS.MC.S7FCDefs
import HRS.MC.S7FCW4D1
import HRS.MC.S7FCW4D2
import HRS.MC.S7FCW14
import HRS.Main.T25PFinal
import HRS.Main.T25PAux24
import HRS.Main.T25PAux27

/-!
# `field_chaos` packet D4 (worker fcf5l): proof of `s7_FC_D4_eta_W2`

Statement copied verbatim from `HRS/MC/S7FCPlan.lean` (spec, sorry); proof here, no sorried module imported.
Route: `prepared_fluctuations_W2_proof` (Theorem 2.5, `W_2` bound) applied to `s7fcPrep R` with `m = r`, `p₀` from D2
(`s7_FC_D2_selected_proof`), initial law `ν = law (η 0)` and linear data from D1 (`s7_FC_D1_linear_proof`), and
`initW r 2 → 0` from D3 (`s7_FC_D3_initial_proof`).  The window identifications use that `ρ` enters the windows only on
`[0, ∞)`, where `(s7fcPrep R).ρ = R.ρ`.  The `J_N` and `B_N` bounds are upper bounds only (`J ≤ C₂`, `0 ≤ B ≤ C₂`),
so no lower bound on `J` is needed.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCD4

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec
open HRS.MC.Sec7.FCPlan

variable {d : ℕ}

/-- The fluctuation path depends on the density only through its values on `[0, T]`. -/
theorem S7FCD4_flucPath_congr {Ω : Type*} {N : ℕ} (γ T σ : ℝ) (X : ℝ≥0 → Ω → Config d N)
    (ρ ρ' : ℝ → Torus d → ℝ) (h : ∀ t : ℝ, 0 ≤ t → t ≤ T → ρ t = ρ' t) :
    HRS.flucPath γ T σ X ρ = HRS.flucPath γ T σ X ρ' := by
  funext ω
  have hfun : (fun t : Set.Icc (0 : ℝ) T => σ • NegSobolev.ofMeasureDiff γ
      (empirical (X (Real.toNNReal t) ω)) (withDensityReal (ρ t))) =
      (fun t : Set.Icc (0 : ℝ) T => σ • NegSobolev.ofMeasureDiff γ
      (empirical (X (Real.toNNReal t) ω)) (withDensityReal (ρ' t))) := by
    funext t
    rw [h t t.2.1 t.2.2]
  unfold HRS.flucPath
  rw [hfun]

/-- The window of the fluctuation process depends on the density only on `[a, ∞)`. -/
theorem S7FCD4_windowFluc_congr {Ω : Type*} {N : ℕ} (m T a σ : ℝ) (X : ℝ≥0 → Ω → Config d N)
    (ρ ρ' : ℝ → Torus d → ℝ) (ha : 0 ≤ a) (h : ∀ t : ℝ, 0 ≤ t → ρ t = ρ' t) :
    HRS.Main.windowFluc m T a σ X ρ = HRS.Main.windowFluc m T a σ X ρ' := by
  unfold HRS.Main.windowFluc
  exact S7FCD4_flucPath_congr m T σ _ _ _ (fun t ht0 _ => h (a + t) (by linarith))

theorem s7_FC_D4_eta_W2_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T)
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → Config d N)
    (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hreal : ∀ N, 1 ≤ N → PreparedRealization R.D (P N)
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) (X₀ N) (W N) (X N))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η : ℝ → Ω' → NegSobolev d r)
    (hη : IsGaussianLimitField R.D R.ρ (withDensityReal R.ρ₀) R.β₀ r P' η) :
    Tendsto (fun N : ℕ => ⨆ a : {a : ℝ // 0 ≤ a},
        wassersteinE 2 (law (P N) (HRS.Main.windowFluc r T a.1 (Real.sqrt N) (X N) R.ρ))
          (law P' (procWin r T a.1 η))) atTop (𝓝 0) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hdr : (d : ℝ) + 2 < r := by rw [hr]; linarith
  have hdr0 : (d : ℝ) / 2 < r := by rw [hr]; linarith
  obtain ⟨hνG, hlinS⟩ := HRS.MC.Sec7.S7FCW4.s7_FC_D1_linear_proof R r hdr P' η hη
  obtain ⟨p₀, C₂, hp₀, hD2⟩ := HRS.MC.Sec7.S7FCW4.s7_FC_D2_selected_proof R
  obtain ⟨C, c, hC, hc, hT25⟩ :=
    HRS.Main.prepared_fluctuations_W2_proof (s7fcPrep R) r hdr T hT p₀ hp₀
  have hD3 := HRS.MC.Sec7.S7FCW14.s7_FC_D3_initial_proof R r hr (law P' (η 0)) hνG 2 (by norm_num)
  -- the initial term is the D3 quantity
  have hinit_eq : ∀ N : ℕ, 2 ≤ N → (s7fcPrep R).initW r 2 (P N) (X N 0) (law P' (η 0)) =
      wassersteinE 2 (law (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀))
        (fun X => etaE r X (withDensityReal R.ρ₀))) (law P' (η 0)) := by
    intro N hN
    have hre := hreal N (by omega)
    have hX0 : Measurable (X N 0) := (hre.solution 0).adapted 0
    have hF : Measurable (fun x : Config d N => etaE r x (withDensityReal R.ρ₀)) :=
      HRS.T25P.t25p_etaE_measurable (s7fcPrep R) r hdr0 N
    have hinit : X N 0 =ᵐ[P N] X₀ N := (hre.solution 0).init
    show wassersteinE 2 (law (P N) (fun ω => etaE r (X N 0 ω) (withDensityReal R.ρ₀)))
      (law P' (η 0)) = _
    congr 1
    calc law (P N) (fun ω => etaE r (X N 0 ω) (withDensityReal R.ρ₀))
        = ((P N).map (X N 0)).map (fun x => etaE r x (withDensityReal R.ρ₀)) :=
          (AEMeasurable.map_map_of_aemeasurable hF.aemeasurable hX0.aemeasurable).symm
      _ = ((P N).map (X₀ N)).map (fun x => etaE r x (withDensityReal R.ρ₀)) := by
          rw [Measure.map_congr hinit]
      _ = (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)).map
            (fun x => etaE r x (withDensityReal R.ρ₀)) := by
          rw [hre.law_init]
  have hinit_lim : Tendsto (fun N : ℕ => (s7fcPrep R).initW r 2 (P N) (X N 0) (law P' (η 0)))
      atTop (𝓝 0) := by
    refine hD3.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact (hinit_eq N hN).symm
  have hfin_ev : ∀ᶠ N : ℕ in atTop, (s7fcPrep R).initW r 2 (P N) (X N 0) (law P' (η 0)) ≠ ⊤ :=
    (hinit_lim.eventually (Iio_mem_nhds ENNReal.zero_lt_top)).mono fun N hN => (Set.mem_Iio.1 hN).ne
  have hA : Tendsto (fun N : ℕ => ((s7fcPrep R).initW r 2 (P N) (X N 0) (law P' (η 0))).toReal)
      atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hinit_lim
    rw [ENNReal.toReal_zero] at h
    exact h
  -- the deterministic upper bound, uniform in the window start
  have hbound : ∀ N : ℕ, 2 ≤ N → (s7fcPrep R).initW r 2 (P N) (X N 0) (law P' (η 0)) ≠ ⊤ →
      (⨆ a : {a : ℝ // 0 ≤ a}, wassersteinE 2
          (law (P N) (HRS.Main.windowFluc r T a.1 (Real.sqrt N) (X N) R.ρ))
          (law P' (procWin r T a.1 η))) ≤
        ENNReal.ofReal (C * (((s7fcPrep R).initW r 2 (P N) (X N 0) (law P' (η 0))).toReal +
          C₂ / Real.sqrt N + (C₂ / (N : ℝ)) ^ ((1 : ℝ) / 4))) := by
    intro N hN hfinN
    refine iSup_le fun a => ?_
    obtain ⟨a, ha⟩ := a
    try dsimp only
    have hre := hreal N (by omega)
    have hSel := hD2 N hN (P N) (X₀ N) (W N) (X N) hre (a + T) (by linarith)
    have hWF : law (P N) (HRS.Main.windowFluc r T a (Real.sqrt N) (X N) R.ρ) =
        (s7fcPrep R).etaLaw r T a (P N) (X N) := by
      unfold HRS.Main.PreparedData.etaLaw
      congr 1
      exact S7FCD4_windowFluc_congr r T a (Real.sqrt N) (X N) R.ρ (s7fcPrep R).ρ ha
        (fun t ht => (HRS.MC.Sec7.S7FCW4.S7FCW4_rho_eq R ht).symm)
    have hpath : procWin r T a η = HRS.Main.windowPath r T a η := rfl
    have hT25a := hT25 a ha N hN (P N) (X N 0) (W N) (X N) hSel.1 hSel.2.1 hSel.2.2.1
      hSel.2.2.2.1 (law P' (η 0)) P' (η 0) η (hlinS (a + T)) hfinN
    rw [hWF, hpath]
    refine hT25a.trans (ENNReal.ofReal_le_ofReal ?_)
    have hA0 : 0 ≤ ((s7fcPrep R).initW r 2 (P N) (X N 0) (law P' (η 0))).toReal :=
      ENNReal.toReal_nonneg
    have hexp : Real.exp (-c * a) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have hJ : (s7fcPrep R).J N (law (P N) (X N 0)) p₀ ≤ C₂ := hSel.2.2.2.2.2
    have hBC : (s7fcPrep R).B N (law (P N) (X N 0)) ≤ C₂ := hSel.2.2.2.2.1
    have hB0 : 0 ≤ (s7fcPrep R).B N (law (P N) (X N 0)) :=
      HRS.T25P.t25p_B_nonneg (s7fcPrep R) hN _
    have t1 : Real.exp (-c * a) * ((s7fcPrep R).initW r 2 (P N) (X N 0) (law P' (η 0))).toReal ≤
        ((s7fcPrep R).initW r 2 (P N) (X N 0) (law P' (η 0))).toReal :=
      mul_le_of_le_one_left hA0 hexp
    have t2 : (s7fcPrep R).J N (law (P N) (X N 0)) p₀ / Real.sqrt N ≤ C₂ / Real.sqrt N := by
      gcongr
    have t3 : ((s7fcPrep R).B N (law (P N) (X N 0)) / N) ^ ((1 : ℝ) / 4) ≤
        (C₂ / (N : ℝ)) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (div_nonneg hB0 (Nat.cast_nonneg N)) (by gcongr) (by norm_num)
    exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add t1 t2) t3) hC.le
  -- the deterministic upper bound tends to zero
  have hk : Tendsto (fun N : ℕ => C * (((s7fcPrep R).initW r 2 (P N) (X N 0) (law P' (η 0))).toReal +
      C₂ / Real.sqrt N + (C₂ / (N : ℝ)) ^ ((1 : ℝ) / 4))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => C₂ / Real.sqrt N) atTop (𝓝 0) :=
      Tendsto.div_atTop (tendsto_const_nhds : Tendsto (fun _ : ℕ => C₂) atTop (𝓝 C₂))
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have hx : Tendsto (fun N : ℕ => C₂ / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat C₂
    have hr4 : Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / 4)) (𝓝 0) (𝓝 0) := by
      have h := (Real.continuousAt_rpow_const (0 : ℝ) ((1 : ℝ) / 4) (Or.inr (by norm_num))).tendsto
      rwa [Real.zero_rpow (by norm_num : (1 : ℝ) / 4 ≠ 0)] at h
    have h2 : Tendsto (fun N : ℕ => (C₂ / (N : ℝ)) ^ ((1 : ℝ) / 4)) atTop (𝓝 0) := hr4.comp hx
    have h := ((hA.add h1).add h2).const_mul C
    rw [show C * (0 + 0 + 0 : ℝ) = 0 by ring] at h
    exact h
  have hlim : Tendsto (fun N : ℕ => ENNReal.ofReal (C * (((s7fcPrep R).initW r 2 (P N) (X N 0)
      (law P' (η 0))).toReal + C₂ / Real.sqrt N + (C₂ / (N : ℝ)) ^ ((1 : ℝ) / 4)))) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal hk
    rw [ENNReal.ofReal_zero] at h
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · exact Eventually.of_forall fun N => zero_le
  · filter_upwards [eventually_ge_atTop 2, hfin_ev] with N hN2 hfinN
    exact hbound N hN2 hfinN

end HRS.MC.Sec7.S7FCD4

end
