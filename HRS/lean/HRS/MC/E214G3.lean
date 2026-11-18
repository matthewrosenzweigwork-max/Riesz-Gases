import HRS.Sections.AdjKAAux16
import HRS.Sections.AdjKAFinal2
import HRS.MC.E214D3

/-!
# E214G3: the increment estimate `E ‖η^t - η^s‖²_{E_m} ≤ (B₁ C₂ + B₂) |t-s|` for a field `η = V(·,0) Y + Z`

`field_increment`: `η^t = V(t,0) Y + Z_t∘π`, `Z` the global stochastic convolution of the Gaussian martingale `G`
against the dual evolution `V` (`IsGlobalNoise`), `Y` any random initial datum.  If `E adjkEnergy_j(η^t) ≤ C₂` for all
`t ≥ 0` (a second-moment bound at the higher regularity level `E_j`, `j + 2 ≤ m`), then for `0 ≤ s ≤ t ≤ s + 1`

  `E ‖η^t - η^s‖²_{E_m} ≤ (B₁ C₂ + B₂) (t - s)`,

with `B₁, B₂` depending only on the trajectory (not on `s`, `Y`, the noise, or `C₂`).  Proof: restart at `s`:
`η^t - η^s = (V(t,s) - 1) η^s + Z'_t` with `Z'` the window convolution from `s` (`adjka_splitting`,
`adjk_evolution_moment_proof`), the drift term by `adjk_evolution_increment_proof` (`adjka_drift_bound` with square).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E214G

open HRS HRS.Uniform HRS.AdjK HRS.MC.E213N HRS.MC.E214D

variable {d : ℕ}

/-- `‖(V^{t,u} - 1) F‖²_{E_m} ≤ (C_A (t-u))² ‖F‖²_{E_j}` for `F ∈ E_m` of finite `E_j`-energy (square version of
`adjka_drift_bound`). -/
theorem drift_sq {D : DynData d} {ρ : ℝ → Torus d → ℝ} {j m : ℝ} (hjm : j + 2 ≤ m)
    {Vj : ℝ → ℝ → NegSobolev d j →L[ℝ] NegSobolev d j}
    {Vm : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
    (hVj : IsDualEvolution D ρ j Vj) (hVm : IsDualEvolution D ρ m Vm) {CA : ℝ} (hCA : 0 ≤ CA)
    (hA2 : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ∀ z : NegSobolev d j,
      ‖NegSobolev.embed (j + 2) (Vj t u z - z)‖ ≤ CA * (t - u) * ‖z‖)
    {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (F : NegSobolev d m) (hF : adjkEnergy j m F ≠ ⊤) :
    ‖Vm t u F - F‖ₑ ^ 2 ≤ ENNReal.ofReal ((CA * (t - u)) ^ 2) * adjkEnergy j m F := by
  have hjm' : j ≤ m := by linarith
  obtain ⟨z, rfl⟩ := adjka_lift hjm' F hF
  have e1 : Vm t u (NegSobolev.embed m z) - NegSobolev.embed m z =
      NegSobolev.embed m (Vj t u z - z) := by
    rw [adjka_dual_embed hjm' hVj hVm hu hut z]
    have := (adjkEmb d hjm').map_sub (Vj t u z) z
    simpa [adjkEmb_apply] using this.symm
  rw [e1, adjka_energy_embed' hjm']
  have hn : ‖NegSobolev.embed m (Vj t u z - z)‖ ≤ CA * (t - u) * ‖z‖ :=
    (adjka_norm_embed_mono (by linarith : j ≤ j + 2) hjm _).trans (hA2 u t hu hut z)
  have hτ : 0 ≤ t - u := by linarith
  calc ‖NegSobolev.embed m (Vj t u z - z)‖ₑ ^ 2
      ≤ (ENNReal.ofReal (CA * (t - u)) * ‖z‖ₑ) ^ 2 := by
        refine pow_le_pow_left₀ bot_le ?_ 2
        rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm z, ← ENNReal.ofReal_mul (mul_nonneg hCA hτ)]
        exact ENNReal.ofReal_le_ofReal hn
    _ = ENNReal.ofReal ((CA * (t - u)) ^ 2) * ‖z‖ₑ ^ 2 := by
        rw [mul_pow, ENNReal.ofReal_pow (mul_nonneg hCA hτ)]

/-- The trace of the noise covariation density is bounded uniformly in time. -/
theorem noiseDens_trace_le (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {m : ℝ} (hm : (d : ℝ) / 2 + 2 < m) (u : ℝ) :
    traceNormForm (noiseDens m β⁻¹ ρ u) ≤ 4 * β⁻¹ * d * Q14.q14S d (m - 1) := by
  have hq : 0 ≤ β⁻¹ := (inv_pos.2 htr.hβ).le
  have hB0 : 0 ≤ 4 * β⁻¹ * d * Q14.q14S d (m - 1) := by
    have := Q14.q14S_nonneg d (m - 1)
    positivity
  by_cases hu : 0 ≤ u
  · obtain ⟨hprob, -, -⟩ := traj_facts hd htr
    haveI : IsProbabilityMeasure (withDensityReal (ρ u)) := isProb_withDensityReal (hprob u hu)
    have := (Q14.q14_covForm_trace hm hq (withDensityReal (ρ u))).2
    rw [measure_univ, ENNReal.toReal_one, mul_one] at this
    simpa [noiseDens, hu] using this
  · simp only [noiseDens, if_neg hu]
    rw [HRS.Uniform.Q07c.traceNormForm_zero']
    exact hB0

/-- **The restart estimate.** -/
theorem field_increment (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (j : ℕ) (hj : (d : ℝ) + 2 ≤ j) {m : ℝ}
    (hjm : (j : ℝ) + 2 ≤ m) :
    ∃ B₁ B₂ : ℝ, 0 ≤ B₁ ∧ 0 ≤ B₂ ∧
      ∀ (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m), IsDualEvolution htr.dyn ρ m Vev →
      (∀ T : ℝ, 0 ≤ T → IsPlainEvolution Vev T) →
      ∀ {Ωg : Type} {mΩg : MeasurableSpace Ωg} (Pg : Measure Ωg) [IsProbabilityMeasure Pg]
        (ℱ : Filtration ℝ mΩg) (G Zs : ℝ → Ωg → NegSobolev d m),
      IsGlobalNoise m β⁻¹ ρ Vev Pg ℱ G Zs →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (π : Ω → Ωg),
        Measurable π → P.map π = Pg → ∀ Y : Ω → NegSobolev d m, Measurable Y →
      ∀ C₂ : ℝ, 0 ≤ C₂ → (∀ t : ℝ, 0 ≤ t →
        ∫⁻ ω, adjkEnergy (j : ℝ) m (Vev t 0 (Y ω) + Zs t (π ω)) ∂P ≤ ENNReal.ofReal C₂) →
      ∀ s' t' : ℝ, 0 ≤ s' → s' ≤ t' → t' ≤ s' + 1 →
        ∫⁻ ω, ‖(Vev t' 0 (Y ω) + Zs t' (π ω)) - (Vev s' 0 (Y ω) + Zs s' (π ω))‖ₑ ^ 2 ∂P ≤
          ENNReal.ofReal ((B₁ * C₂ + B₂) * (t' - s')) := by
  have hd1 : 1 ≤ d := by omega
  have hm2 : (d : ℝ) / 2 + 2 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨CA, hCA, hA2⟩ := adjk_evolution_increment_proof hd htr j hj
  obtain ⟨Vj, hVj, -, -, -⟩ := adjka_levelInput_traj hd htr (j : ℝ)
  obtain ⟨Vm', hVm', hVmp', hB1⟩ := adjk_evolution_moment_proof hd htr m 2 le_rfl
  obtain ⟨CB2, hCB2, hB1'⟩ := hB1 1 one_pos
  set Bm : ℝ := 4 * β⁻¹ * d * Q14.q14S d (m - 1) with hBm
  have hBm0 : 0 ≤ Bm := by
    have := Q14.q14S_nonneg d (m - 1)
    have hq : 0 ≤ β⁻¹ := (inv_pos.2 htr.hβ).le
    positivity
  refine ⟨2 * CA ^ 2, 2 * CB2 * Bm, by positivity, by positivity, ?_⟩
  intro Vev hVev hplain Ωg mΩg Pg _ ℱ G Zs hN Ω _ P _ π hπm hπ Y hYm C₂ hC₂ hEn s' t' hs' hst ht1

  rcases hst.eq_or_lt with heq | hlt
  · subst heq
    simp
  set h : ℝ := t' - s' with hh
  have hh0 : 0 < h := sub_pos.2 hlt
  have hh1 : h ≤ 1 := by linarith
  have hst' : s' + h = t' := by rw [hh]; ring
  have ht0 : 0 ≤ t' := hs'.trans hst
  have hMt : IsHilbertMartingaleWithCovariation Pg ℱ (s' + h) G (fun r _ => noiseDens m β⁻¹ ρ r) :=
    hN.mart _ (by linarith)
  obtain ⟨Z', hZ'conv, -, hZ'meas, hZ'bd⟩ := hB1' Ωg Pg ℱ s' h hs' hh0 hh1 G _ hMt
  have ht'I : t' ∈ Icc s' (s' + h) := ⟨hst, hst'.symm.le⟩
  have hZ'c : IsStochConv Pg Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G s' t' (Z' t') := by
    refine adjka_isStochConv_congr_ev ?_ (hZ'conv t' ht'I)
    intro r hr1 hr2
    exact adjka_dual_unique hVm' hVev (hs'.trans hr1) hr2
  have hcoc := (hplain t' ht0).2.1
  have hMt' : ∀ τ ∈ Icc (0 : ℝ) t', AEStronglyMeasurable (G τ) Pg := fun τ hτ =>
    (((hN.mart t' ht0).sq_int τ hτ)).aestronglyMeasurable
  have hsplit := adjka_splitting hs' hst hcoc hMt' (hN.conv t' ht0) (hN.conv s' hs') hZ'c
    (hN.meas t').aemeasurable (hN.meas s').aemeasurable (hZ'meas t' ht'I)
  have hπ' : MeasurePreserving π P Pg := ⟨hπm, hπ⟩
  have hsplitP : ∀ᵐ ω ∂P, Zs t' (π ω) = Vev t' s' (Zs s' (π ω)) + Z' t' (π ω) :=
    hπ'.quasiMeasurePreserving.ae (p := fun x => Zs t' x = Vev t' s' (Zs s' x) + Z' t' x) hsplit
  have hVcoc : ∀ y : NegSobolev d m, Vev t' 0 y = Vev t' s' (Vev s' 0 y) := fun y => by
    have := hcoc 0 s' t' le_rfl hs' hst le_rfl
    rw [← this]; rfl
  -- finiteness of the energy
  have hηm : Measurable fun ω => Vev s' 0 (Y ω) + Zs s' (π ω) :=
    ((Vev s' 0).continuous.measurable.comp hYm).add ((hN.meas s').comp hπm)
  have hEm : Measurable fun ω => adjkEnergy (j : ℝ) m (Vev s' 0 (Y ω) + Zs s' (π ω)) :=
    (adjkEnergy_measurable (j : ℝ) m).comp hηm
  have hfin : ∀ᵐ ω ∂P, adjkEnergy (j : ℝ) m (Vev s' 0 (Y ω) + Zs s' (π ω)) ≠ ⊤ := by
    have := ae_lt_top' hEm.aemeasurable (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hEn s' hs'))
    exact this.mono fun ω h => h.ne
  -- the pointwise bound
  have hpt : ∀ᵐ ω ∂P, ‖(Vev t' 0 (Y ω) + Zs t' (π ω)) - (Vev s' 0 (Y ω) + Zs s' (π ω))‖ₑ ^ 2 ≤
      2 * (ENNReal.ofReal ((CA * h) ^ 2) * adjkEnergy (j : ℝ) m (Vev s' 0 (Y ω) + Zs s' (π ω)) +
        ‖Z' t' (π ω)‖ₑ ^ 2) := by
    filter_upwards [hsplitP, hfin] with ω h1 h2
    set F : NegSobolev d m := Vev s' 0 (Y ω) + Zs s' (π ω) with hF
    have e : (Vev t' 0 (Y ω) + Zs t' (π ω)) - (Vev s' 0 (Y ω) + Zs s' (π ω)) =
        (Vev t' s' F - F) + Z' t' (π ω) := by
      rw [hVcoc, h1, hF, map_add]; abel
    rw [e]
    refine le_trans (pow_le_pow_left₀ bot_le (enorm_add_le _ _) 2) (le_trans (adjka_sq_add_le _ _) ?_)
    gcongr
    exact drift_sq hjm hVj hVev hCA (hA2 Vj hVj) hs' hst F h2
  -- integrate
  have hZint : ∫⁻ ω, ‖Z' t' (π ω)‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (CB2 * (h * Bm)) := by
    have hae : AEMeasurable (fun x => ‖Z' t' x‖ₑ ^ 2) (P.map π) := by
      rw [hπ]; exact (hZ'meas t' ht'I).enorm.pow_const 2
    rw [← lintegral_map' hae hπm.aemeasurable, hπ]
    have h1 : ∀ x, ‖Z' t' x‖ₑ ^ 2 ≤ (⨆ t ∈ Icc s' (s' + h), ‖Z' t x‖ₑ) ^ (2 : ℝ) := fun x => by
      rw [ENNReal.rpow_two]
      exact pow_le_pow_left₀ bot_le (le_iSup₂ (f := fun t (_ : t ∈ Icc s' (s' + h)) => ‖Z' t x‖ₑ) t' ht'I) 2
    refine (lintegral_mono h1).trans (hZ'bd.trans ?_)
    have h2 := adjka_lintegral_trace_window Pg (a := s') (b := s' + h) (by linarith) hBm0
      (fun u (_ : Ωg) => traceNormForm (noiseDens m β⁻¹ ρ u))
      (fun u _ => noiseDens_trace_le hd htr hm2 u) (r := (2 : ℝ) / 2) (by norm_num)
    rw [show s' + h - s' = h by ring, show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one] at h2
    simp only [ENNReal.rpow_one, show (2 : ℝ) / 2 = 1 by norm_num] at h2 ⊢
    rw [ENNReal.ofReal_mul hCB2]
    gcongr
  have hEint : ∫⁻ ω, adjkEnergy (j : ℝ) m (Vev s' 0 (Y ω) + Zs s' (π ω)) ∂P ≤ ENNReal.ofReal C₂ :=
    hEn s' hs'
  calc ∫⁻ ω, ‖(Vev t' 0 (Y ω) + Zs t' (π ω)) - (Vev s' 0 (Y ω) + Zs s' (π ω))‖ₑ ^ 2 ∂P
      ≤ ∫⁻ ω, 2 * (ENNReal.ofReal ((CA * h) ^ 2) * adjkEnergy (j : ℝ) m (Vev s' 0 (Y ω) + Zs s' (π ω)) +
        ‖Z' t' (π ω)‖ₑ ^ 2) ∂P := lintegral_mono_ae hpt
    _ = 2 * (ENNReal.ofReal ((CA * h) ^ 2) *
          ∫⁻ ω, adjkEnergy (j : ℝ) m (Vev s' 0 (Y ω) + Zs s' (π ω)) ∂P +
          ∫⁻ ω, ‖Z' t' (π ω)‖ₑ ^ 2 ∂P) := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_add_left' (hEm.aemeasurable.const_mul _),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ 2 * (ENNReal.ofReal ((CA * h) ^ 2) * ENNReal.ofReal C₂ + ENNReal.ofReal (CB2 * (h * Bm))) := by
        gcongr
    _ = ENNReal.ofReal (2 * ((CA * h) ^ 2 * C₂ + CB2 * (h * Bm))) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by norm_num)]
    _ ≤ ENNReal.ofReal ((2 * CA ^ 2 * C₂ + 2 * CB2 * Bm) * (t' - s')) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have : (CA * h) ^ 2 * C₂ ≤ CA ^ 2 * C₂ * h := by
          have : h ^ 2 ≤ h := by nlinarith
          nlinarith [mul_nonneg (sq_nonneg CA) hC₂]
        have hh' : t' - s' = h := rfl
        rw [hh']
        nlinarith

end HRS.MC.E214G

end
