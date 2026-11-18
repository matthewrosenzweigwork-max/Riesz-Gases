import HRS.ME.FamUF3
import HRS.ME.FamUF4
import HRS.ME.FamUF7
import HRS.ME.CritForcingBridge
import HRS.ME.CritBurnin
import HRS.ME.CritPaths

/-!
# Chunk E, packet F11 (namespace `HRS.ME.FamU`): family forms of the critical 4.17 chain

Originals (copied with the convention of `docs/MAIN_E_FAMU_PLAN.md`: fixed data first, then the constants, then
`∀ V, Torus.IsSmooth V → (∀ j, Torus.cbNorm j V ≤ Bf j) → …`; the family hypotheses are inputs):
* (a) `crit_forcing_of_uniform417_unifV`: from `Uniform417Fam` to `CritForcingFam`; copy of
  `HRS.ME.CritForcingBridge.crit_forcing_of_uniform417_proof` (HRS/ME/CritForcingBridge.lean:197).
  The constant `C` passes through; `HRS.Q41.q41_thermal_regular` is used per `V` (needs only `IsSmooth V`).
* (b) `crit_burnin_of_evo_unifV`: from `EvoPkgFam` and `CritForcingFam` to `CritBurnConclFam`; copy of
  `HRS.ME.CritBurnin.crit_burnin_of_evo_proof` (HRS/ME/CritBurnin.lean:170; statement `HRS.ME.Crit.crit_burnin_of_evo`,
  HRS/ME/CritSpec.lean:142). `Cp, Cg, C0` come from `eq_init_particle_unifV`, `eq_init_gauss_unifV`,
  `crit_bures2_uniform_unifV` before `V`; `Cf` from `hforce` before `V`.
* (c) `crit_paths_of_burnin_unifV`: copy of `HRS.ME.CritPaths.crit_paths_of_burnin` (HRS/ME/CritPaths.lean:32). The constants
  `K c0 Cmax` come from `eqbw_evoPkg_unifV` before `V`; the burn-in constants `C, c` from (b) before `V` and `β`.
  The conclusion is the body of `HRS.Main.critical_centered_path` (HRS/Main/HeadlineEquilibrium.lean:146) with `V` bound after `C`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.FamU

/-! ### (a) The forcing bound from the family `Uniform417Fam` -/

section CritForcingPart

open HRS HRS.LZ HRS.MD.EQ29 HRS.MD.EQRem

variable {d : ℕ}

/-- (a) V-uniform copy of `HRS.ME.CritForcingBridge.crit_forcing_of_uniform417_proof`: the constant `C` of the family
`Uniform417Fam` is the constant of `CritForcingFam`; the potential `V` is bound inside the quantifier. -/
theorem crit_forcing_of_uniform417_unifV (hd : 2 ≤ d) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d)
    (βm βp : ℝ) (hβm : 0 < βm) (m T : ℝ) (Bf : ℕ → ℝ)
    (hu : Uniform417Fam d hs0 hsd βm βp hβm m T Bf) :
    CritForcingFam d hs0 hsd βm βp hβm m T Bf := by
  obtain ⟨C, hC0, hC⟩ := hu
  refine ⟨C, hC0, ?_⟩
  intro V hV hVB β hβ ρβ hρ N hN Ω _ P _ X₀ W X a ha hq hflow
  have hβ0 : 0 < β := hβm.trans_le hβ.1
  obtain ⟨hpos, hsm⟩ := HRS.Q41.q41_thermal_regular hd hs0 hsd hβ0 hV hρ
  have hu' := hC V hV hVB β hβ ρβ hρ hsm hpos N hN P X₀ W X a ha hflow
  refine le_trans (lintegral_mono fun ω => ?_) hu'
  obtain ⟨q0, hq0⟩ := hq
  set Y : ℝ≥0∞ := ⨆ t ∈ ratTimes 0 T, ∑' k : NonzeroLattice d,
    ENNReal.ofReal (integratedCenteredForcing (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β hβ0) ρβ P X m k
      (a + t) ω ^ 2) with hY
  have hle : (⨆ t ∈ ratTimes a T, (coordEnergy m (fun k => statForcingCoord d hs0 hsd V hβ0 ρβ X k t ω)) ^
      (1 / 2 : ℝ)) ≤ Y ^ (1 / 2 : ℝ) := by
    refine iSup₂_le fun t ht => ?_
    obtain ⟨⟨hta, htb⟩, q, hq'⟩ := ht
    have ht' : t - a ∈ ratTimes 0 T :=
      ⟨⟨by linarith, by linarith⟩, ⟨q - q0, by push_cast; rw [hq', hq0]⟩⟩
    have heq : coordEnergy m (fun k => statForcingCoord d hs0 hsd V hβ0 ρβ X k t ω) =
        ∑' k : NonzeroLattice d, ENNReal.ofReal (integratedCenteredForcing
          (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β hβ0) ρβ P X m k (a + (t - a)) ω ^ 2) := by
      unfold coordEnergy
      refine tsum_congr fun k => ?_
      beta_reduce
      rw [add_sub_cancel, HRS.ME.CritForcingBridge.cfb_coord_eq hd hs0 hsd V hV β hβ0 ρβ hρ hsm hpos hN P X₀ W X
        (a + T) hflow m k (ha.trans hta) (by linarith) ω]
      rw [HRS.ME.CritForcingBridge.cfb_sq_eq]
    rw [heq]
    exact ENNReal.rpow_le_rpow (le_iSup₂ (f := fun t (_ : t ∈ ratTimes 0 T) => ∑' k : NonzeroLattice d,
      ENNReal.ofReal (integratedCenteredForcing (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β hβ0) ρβ P X m k
        (a + t) ω ^ 2)) (t - a) ht') (by norm_num)
  calc (⨆ t ∈ ratTimes a T, (coordEnergy m (fun k => statForcingCoord d hs0 hsd V hβ0 ρβ X k t ω)) ^
      (1 / 2 : ℝ)) ^ 2 ≤ (Y ^ (1 / 2 : ℝ)) ^ 2 := pow_le_pow_left' hle 2
    _ = Y := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num

end CritForcingPart

/-! ### (b) The critical burn-in from the family hypotheses -/

section BurninPart

open HRS HRS.LZ HRS.Uniform HRS.Main HRS.T25P HRS.MD.EQ29 HRS.MD.EQBurnBurn

variable {d : ℕ}

/-- (b) V-uniform copy of `HRS.ME.CritBurnin.crit_burnin_of_evo_proof`. The fixed data are `d hd hs0 hsd βm βp hβm hββ m hm T hT`,
the constants `K c Cmax` and the bound sequence `Bf`; the family hypotheses `hevo` (`EvoPkgFam`) and `hforce` (`CritForcingFam`)
are inputs. The constants `Cp, Cg, C0, Cf` are chosen before `V`. -/
theorem crit_burnin_of_evo_unifV (hd : 2 ≤ d) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d)
    (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (m : ℝ) (hm : 24 * (d : ℝ) + 240 ≤ m) (T : ℝ) (hT : 0 < T)
    (K c Cmax : ℝ) (hK : 0 ≤ K) (hc : 0 < c) (hCmax : 0 ≤ Cmax) (Bf : ℕ → ℝ)
    (hevo : EvoPkgFam d ((d : ℝ) / 2) hs0 hsd Bf βm βp hβm m K c T Cmax)
    (hforce : CritForcingFam d hs0 hsd βm βp hβm m T Bf) :
    CritBurnConclFam d hs0 hsd βm βp hβm m T Bf := by
  classical
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdnn : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hmd : (d : ℝ) / 2 + 2 < m := by linarith
  have hm1 : (d : ℝ) + 1 < m := by linarith
  have hm3 : (d : ℝ) + 3 ≤ m := by linarith
  have hmh : (d : ℝ) / 2 < m := by linarith
  have hmd2 : (d : ℝ) < 2 * m := by linarith
  have hmcrit : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m := max_lt hm1 hmd
  have hK'0 : 0 < max K 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  -- the V-uniform constants (chosen before `V`)
  obtain ⟨Cp, hCp0, hinp⟩ := eq_init_particle_unifV hd hs0 hsd βm βp hβm hββ m hmh Bf
  obtain ⟨Cg, hCg0, hing⟩ := eq_init_gauss_unifV hd hs0 hsd βm βp hβm hββ m hmh Bf
  obtain ⟨C0, hC0, hbur⟩ := crit_bures2_uniform_unifV hd hs0 hsd βm βp hβm hββ m hm3 Bf
  obtain ⟨Cf, hCf0, hfor⟩ := hforce
  set S0 : ℝ := Real.sqrt Cp + Real.sqrt Cg with hS0def
  have hS00 : 0 ≤ S0 := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  set Q : ℝ := 2 * ((max K 1) ^ 2 + Real.sqrt Cmax) + max K 1 + 1 with hQdef
  have hQ0 : 0 ≤ Q := by
    have h1 := Real.sqrt_nonneg Cmax
    have h2 := sq_nonneg (max K 1)
    have h3 : 0 ≤ max K 1 := le_of_lt hK'0
    rw [hQdef]; linarith
  have hK0 : 0 ≤ 1 / (2 * c) + T := add_nonneg (div_nonneg zero_le_one (by linarith)) hT.le
  have hD1 : 0 ≤ (1 / (2 * c) + T) * C0 := mul_nonneg hK0 hC0.le
  set Kb : ℝ := Real.sqrt (5 * ((1 / (2 * c) + T) * C0)) with hKbdef
  have hKb0 : 0 ≤ Kb := Real.sqrt_nonneg _
  have hCc0 : 0 < Q * S0 + Cf + Q * Kb + 1 := by
    have h1 := mul_nonneg hQ0 hS00
    have h2 := mul_nonneg hQ0 hKb0
    linarith
  unfold CritBurnConclFam
  refine ⟨Q * S0 + Cf + Q * Kb + 1, c, hCc0, hc, ?_⟩
  intro V hV hVB β hβ ρβ hρβ a ha hqa N hN Ω _ P _ X₀ W X hX Ω' _ P' _ Z hZ
  have hβ0 : 0 < β := hβm.trans_le hβ.1
  have hq : 0 ≤ β⁻¹ := (inv_pos.2 hβ0).le
  obtain ⟨hρc, -, -⟩ := HRS.MD.EQTrace.eqtrace_setup hd hs0 hsd V hV βm βp hβm hββ β hβ ρβ hρβ N hN
  haveI : IsFiniteMeasure (withDensityReal ρβ) :=
    HRS.Uniform.Q48c.isFiniteMeasure_withDensityReal_of_cont hρc
  have hDtr : IsTraceClassCov (covForm m β⁻¹ (withDensityReal ρβ)) :=
    (HRS.Uniform.Q14.q14_covForm_trace hmd hq _).1
  obtain ⟨Vev, hEv, hdual⟩ := hevo V hV hVB β hβ ρβ hρβ
  obtain ⟨Ω₁, mΩ₁, P₁, hP₁, π, hπ, ℱ₁, W'', η', hX', hF', hη'm, hη'map, hW2⟩ :=
    HRS.ME.CritEngine.crit_engine_proof hd hs0 hsd V hV hβ0 ρβ hρβ m hmcrit hK'0 hc hT Vev
      (HRS.MD.EQBurnBurn.eqb_ev_max hEv) hdual ha hN P X₀ W X hX P' Z hZ
  have hN0 : 0 < N := by omega
  have hN0R : (0 : ℝ) < N := by exact_mod_cast hN0
  -- the rational notation of the normalized constant
  set u : ℝ := (N : ℝ) ^ (-(1 : ℝ) / 2) with hudef
  have hu0 : 0 ≤ u := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hu2 : u ^ 2 = (N : ℝ)⁻¹ := by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
    norm_num [Real.rpow_neg_one]
  -- stationarity on the enlarged space
  have hstat := HRS.MD.Stat.md_stat_gibbs_flow_stationary_proof hd hs0 hsd V hV β hβ0 (a + T) hN P₁ _ _ _ hX'
  have hYm : ∀ t : ℝ≥0, Measurable (fun ω' => X t (π ω')) := fun t =>
    (hF'.adapted t).mono (ℱ₁.le t) le_rfl
  -- the initial term
  have hGprob : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β) := by
    rw [← hstat 0 (by simp; linarith)]
    exact (Measure.isProbabilityMeasure_map_iff (hYm 0).aemeasurable).2 inferInstance
  have hzm : Measurable (zetaE m (canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β)) :=
    (HRS.MD.EQLawPath.eqlaw_continuous_zetaE hmd2 (by omega) _).measurable
  have hmap0 : P₁.map (fun ω'' => X (0 : ℝ≥0) (π ω'')) = canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β :=
    hstat 0 (by simp; linarith)
  have hζ0m : Measurable (fun ω => zetaE m (P₁.map (fun ω'' => X (0 : ℝ≥0) (π ω''))) (X (0 : ℝ≥0) (π ω))) := by
    rw [hmap0]; exact hzm.comp (hYm 0)
  have hI1 : ∫⁻ ω, ‖zetaE m (P₁.map (fun ω'' => X (0 : ℝ≥0) (π ω''))) (X (0 : ℝ≥0) (π ω))‖ₑ ^ 2 ∂P₁ ≤
      ENNReal.ofReal Cp := by
    rw [hmap0]
    have := lintegral_map (μ := P₁) (f := fun x => ‖zetaE m (canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β) x‖ₑ ^ 2)
      (g := fun ω' => X (0 : ℝ≥0) (π ω')) (hzm.enorm.pow_const 2) (hYm 0)
    rw [← this, hmap0]
    exact hinp V hV hVB β hβ ρβ hρβ N hN
  have hI2 : ∫⁻ ω, ‖η' ω‖ₑ ^ 2 ∂P₁ ≤ ENNReal.ofReal Cg := by
    have h1 := lintegral_map (μ := P₁) (f := fun y : NegSobolev d m => ‖y‖ₑ ^ 2) (g := η')
      (measurable_enorm.pow_const 2) hη'm
    have h2 := lintegral_map (μ := P') (f := fun y : NegSobolev d m => ‖y‖ₑ ^ 2) (g := Z 0)
      (measurable_enorm.pow_const 2) (hZ.meas 0)
    rw [← h1, hη'map, h2]
    exact hing V hV hVB β hβ ρβ hρβ P' Z hZ
  obtain ⟨-, hD2⟩ := eqb_init_diff P₁ _ η' hζ0m.aemeasurable hη'm.aemeasurable hCp0.le hCg0.le hI1 hI2
  -- the remainder term
  have hRem := hfor V hV hVB β hβ ρβ hρβ N hN P₁ (fun ω' => X₀ (π ω')) (fun t ω' => W t (π ω'))
    (fun t ω' => X t (π ω')) a ha hqa hX'
  have hRemB := eqb_l2_le P₁ (fun ω => (⨆ t ∈ ratTimes a T, (coordEnergy m (fun k => statForcingCoord d hs0 hsd V hβ0 ρβ
      (fun t ω' => X t (π ω')) k t ω)) ^ (1 / 2 : ℝ))) (A := Cf ^ 2 / N) (by positivity) hRem
  have hsqrtR : Real.sqrt (Cf ^ 2 / N) = Cf * u := by
    rw [show Cf ^ 2 / (N : ℝ) = (Cf * u) ^ 2 by rw [mul_pow, hu2, div_eq_mul_inv]]
    exact Real.sqrt_sq (mul_nonneg hCf0 hu0)
  -- the Bures term
  have hJ : Measurable fun p : ℝ × Ω₁ => X (min (a + T) p.1).toNNReal (π p.2) :=
    HRS.MD.EQRem.eqrem_joint_meas ℱ₁ (a + T) (fun t ω' => X t (π ω')) hF'.progressive
  have hν : ∀ t : ℝ, 0 ≤ t → t ≤ a + T → P₁.map (fun ω' => X t.toNNReal (π ω')) =
      canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β := fun t ht0 htS =>
    hstat t.toNNReal (by rw [Real.coe_toNNReal _ ht0]; exact htS)
  have hB0 := hbur V hV hVB β hβ ρβ hρβ N hN
  have hVnn : 0 ≤ (1 / (2 * c) + T) * (C0 * ((N : ℝ)⁻¹ + deltaN d ((d : ℝ) / 2) N ^ 2)) :=
    mul_nonneg hK0 (mul_nonneg hC0.le (add_nonneg (inv_nonneg.2 hN0R.le) (sq_nonneg _)))
  have hEB := HRS.ME.CritBurnin.crit_bu_tonelli hmd hq hN0 (covForm m β⁻¹ (withDensityReal ρβ)) hDtr P₁ hc ha hT.le
    (fun r ω => X r.toNNReal (π ω)) hJ (canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β) hν
    (B0 := C0 * ((N : ℝ)⁻¹ + deltaN d ((d : ℝ) / 2) N ^ 2))
    (mul_nonneg hC0.le (add_nonneg (inv_nonneg.2 hN0R.le) (sq_nonneg _))) hB0
  have hT3 : (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T), ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
      bures2 (covForm m β⁻¹ (empirical (X r.toNNReal (π ω)))) (covForm m β⁻¹ (withDensityReal ρβ)))) ∂P₁) ^
      (1 / (2 : ℝ)) ≤ ENNReal.ofReal (Kb * u) := by
    refine (ENNReal.rpow_le_rpow hEB (by norm_num)).trans ?_
    rw [ENNReal.ofReal_rpow_of_nonneg hVnn (by norm_num), ← Real.sqrt_eq_rpow]
    apply ENNReal.ofReal_le_ofReal
    have hδ := HRS.ME.CritBurnin.crit_bu_delta_sq (d := d) hN
    have h1 : (N : ℝ)⁻¹ + deltaN d ((d : ℝ) / 2) N ^ 2 ≤ 5 * (N : ℝ)⁻¹ := by linarith
    have h2 : C0 * ((N : ℝ)⁻¹ + deltaN d ((d : ℝ) / 2) N ^ 2) ≤ C0 * (5 * (N : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left h1 hC0.le
    have h3 : (1 / (2 * c) + T) * (C0 * ((N : ℝ)⁻¹ + deltaN d ((d : ℝ) / 2) N ^ 2)) ≤
        (1 / (2 * c) + T) * (C0 * (5 * (N : ℝ)⁻¹)) := mul_le_mul_of_nonneg_left h2 hK0
    have h4 : (1 / (2 * c) + T) * (C0 * (5 * (N : ℝ)⁻¹)) = 5 * ((1 / (2 * c) + T) * C0) * u ^ 2 := by
      rw [hu2]; ring
    have h5 : 0 ≤ 5 * ((1 / (2 * c) + T) * C0) := by linarith
    calc Real.sqrt ((1 / (2 * c) + T) * (C0 * ((N : ℝ)⁻¹ + deltaN d ((d : ℝ) / 2) N ^ 2)))
        ≤ Real.sqrt (5 * ((1 / (2 * c) + T) * C0) * u ^ 2) := Real.sqrt_le_sqrt (h3.trans_eq h4)
      _ = Kb * u := by
        rw [Real.sqrt_mul h5, Real.sqrt_sq hu0]
  -- assembling the three terms
  have hT1 : (∫⁻ ω, ‖zetaE m (P₁.map (fun ω'' => X (0 : ℝ≥0) (π ω''))) (X (0 : ℝ≥0) (π ω)) - η' ω‖ₑ ^ (2 : ℝ)
      ∂P₁) ^ (1 / (2 : ℝ)) ≤ ENNReal.ofReal S0 := hD2
  have hQe0 : 0 ≤ Q * Real.exp (-c * a) := mul_nonneg hQ0 (Real.exp_pos _).le
  have hT2 : (∫⁻ ω, (⨆ t ∈ ratTimes a T, (coordEnergy m (fun k => statForcingCoord d hs0 hsd V hβ0 ρβ
      (fun t ω' => X t (π ω')) k t ω)) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ∂P₁) ^ (1 / (2 : ℝ)) ≤ ENNReal.ofReal (Cf * u) := by
    refine hRemB.trans (le_of_eq ?_)
    rw [hsqrtR]
  have hfinal : ENNReal.ofReal (Q * Real.exp (-c * a)) * ENNReal.ofReal S0 + ENNReal.ofReal (Cf * u) +
      ENNReal.ofReal Q * ENNReal.ofReal (Kb * u) ≤
      ENNReal.ofReal ((Q * S0 + Cf + Q * Kb + 1) * (Real.exp (-c * a) + u)) := by
    have hE0 : 0 ≤ Real.exp (-c * a) := (Real.exp_pos _).le
    rw [← ENNReal.ofReal_mul hQe0, ← ENNReal.ofReal_mul hQ0,
      ← ENNReal.ofReal_add (mul_nonneg hQe0 hS00) (mul_nonneg hCf0 hu0),
      ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hQe0 hS00) (mul_nonneg hCf0 hu0))
        (mul_nonneg hQ0 (mul_nonneg hKb0 hu0))]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [mul_nonneg (mul_nonneg hQ0 hS00) hu0, mul_nonneg hCf0 hE0,
      mul_nonneg (mul_nonneg hQ0 hKb0) hE0, hE0, hu0]
  refine hW2.trans ?_
  have hA1 : ENNReal.ofReal (Q * Real.exp (-c * a)) * (∫⁻ ω, ‖zetaE m (P₁.map (fun ω'' => X (0 : ℝ≥0) (π ω''))) (X (0 : ℝ≥0) (π ω)) - η' ω‖ₑ ^ (2 : ℝ) ∂P₁) ^ (1 / (2 : ℝ)) ≤
      ENNReal.ofReal (Q * Real.exp (-c * a)) * ENNReal.ofReal S0 := by gcongr
  have hA3 : ENNReal.ofReal Q * (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T), ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
      bures2 (covForm m β⁻¹ (empirical (X r.toNNReal (π ω)))) (covForm m β⁻¹ (withDensityReal ρβ)))) ∂P₁) ^
      (1 / (2 : ℝ)) ≤ ENNReal.ofReal Q * ENNReal.ofReal (Kb * u) := by gcongr
  refine (add_le_add (add_le_add hA1 hT2) hA3).trans ?_
  exact hfinal

end BurninPart

/-! ### (c) The critical centered path from the family hypotheses -/

section PathsPart

open HRS HRS.LZ HRS.Uniform HRS.Main

variable {d : ℕ}

/-- (c) V-uniform copy of `HRS.ME.CritPaths.crit_paths_of_burnin`. The constant `C` (and the burn-in constant `c`) are chosen
before `V`, `β` and `ρβ`; the constant `K c0 Cmax` of the evolution package is chosen by `eqbw_evoPkg_unifV` before `V`.
The conclusion is the body of `HRS.Main.critical_centered_path` with `V` bound after `C`, under the bound `cbNorm j V ≤ Bf j`. -/
theorem crit_paths_of_burnin_unifV (hd : 2 ≤ d) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d)
    (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (m : ℝ) (hm : 24 * (d : ℝ) + 240 ≤ m) (T : ℝ) (hT : 0 < T) (Bf : ℕ → ℝ)
    (hforce : CritForcingFam d hs0 hsd βm βp hβm m T Bf) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Torus d → ℝ), Torus.IsSmooth V → (∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) →
      ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) V β ρβ →
      ∀ u : ℝ, 0 ≤ u → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β (hβm.trans_le hβ.1)) (u + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        law P X₀ = canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → NegSobolev d m),
        IsStationaryGaussianField P' ((d : ℝ) / 2) β hs0 hsd (hβm.trans_le hβ.1) V ρβ m Z →
        wassersteinE 2 (law P (windowZeta m T u P X)) (law P' (windowPath m T 0 Z)) ≤
          ENNReal.ofReal (C * (N : ℝ) ^ (-(1 : ℝ) / 2)) ∧
        (∀ p : ℝ, 1 ≤ p → p ≤ 2 →
          wassersteinE p (law P (windowZeta m T u P X)) (law P' (windowPath m T 0 Z)) ≤
            ENNReal.ofReal (C * (N : ℝ) ^ (-(1 : ℝ) / 2))) ∧
        (∀ k : ℕ, 1 ≤ k →
          smoothDist k (law P (windowZeta m T u P X)) (law P' (windowPath m T 0 Z)) ≤
            C * (N : ℝ) ^ (-(1 : ℝ) / 2)) := by
  obtain ⟨K, c0, Cmax, hK, hc0, hCmax, hevo⟩ :=
    eqbw_evoPkg_unifV hd hs0 hsd βm βp hβm hββ m T hT.le Bf
  obtain ⟨C, c, hC, hc, h⟩ :=
    crit_burnin_of_evo_unifV hd hs0 hsd βm βp hβm hββ m hm T hT K c0 Cmax hK hc0 hCmax Bf hevo hforce
  refine ⟨C, hC, ?_⟩
  intro V hV hVB β hβ ρβ hρ u hu N hN Ω _ P _ X₀ W X hSel hfilt hlawX Ω' _ P' _ Z hZ
  have hβ0 : 0 < β := hβm.trans_le hβ.1
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hT0 : (0 : ℝ) ≤ T := hT.le
  have hmd : (d : ℝ) / 2 < m := by linarith
  have hdm : (d : ℝ) < 2 * m := by linarith
  have hfl : HRS.LZ.IsStationaryGibbsFlow P ((d : ℝ) / 2) hs0 hsd V β hβ0 (u + T) X₀ W X :=
    ⟨hSel, hfilt, hlawX⟩
  -- the burn-in at the integer window starts `a = n`, transported to the window at `u`
  have key : ∀ n : ℕ, wassersteinE 2 (law P (HRS.Main.windowZeta m T u P X))
      (law P' (HRS.Main.windowPath m T 0 Z)) ≤
      ENNReal.ofReal (C * (Real.exp (-c * (n : ℝ)) + (N : ℝ) ^ (-(1 : ℝ) / 2))) := by
    intro n
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    obtain ⟨Ω'', _, P'', _, X₀', W', X', hX'⟩ :=
      HRS.MD.EQLawFlow.eq_flow_exists_proof hd hs0 hsd V hV hβ0 hN ((n : ℝ) + T) (by linarith)
    rw [HRS.MD.EQLawPath.eq_path_stationary_proof hd hs0 hsd V hV hβ0 m hmd T hT0 hN P X₀ W X u hu
      hfl P'' X₀' W' X' (n : ℝ) hn0 hX']
    exact h V hV hVB β hβ ρβ hρ (n : ℝ) hn0 ⟨(n : ℚ), by simp⟩ N hN P'' X₀' W' X' hX' P' Z hZ
  have hNpow : (0 : ℝ) ≤ (N : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hW2 : wassersteinE 2 (law P (HRS.Main.windowZeta m T u P X))
      (law P' (HRS.Main.windowPath m T 0 Z)) ≤
      ENNReal.ofReal (C * (N : ℝ) ^ (-(1 : ℝ) / 2)) := by
    have hexp : Tendsto (fun n : ℕ => Real.exp (-c * (n : ℝ))) atTop (𝓝 0) := by
      have h2 : Tendsto (fun n : ℕ => -c * (n : ℝ)) atTop atBot :=
        (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop_of_neg (by linarith)
      exact Real.tendsto_exp_atBot.comp h2
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (C * (Real.exp (-c * (n : ℝ)) +
        (N : ℝ) ^ (-(1 : ℝ) / 2)))) atTop
        (𝓝 (ENNReal.ofReal (C * (0 + (N : ℝ) ^ (-(1 : ℝ) / 2))))) :=
      ENNReal.tendsto_ofReal ((hexp.add_const ((N : ℝ) ^ (-(1 : ℝ) / 2))).const_mul C)
    have := ge_of_tendsto hlim (Eventually.of_forall key)
    simpa only [zero_add] using this
  -- probability laws of the two windows
  haveI : IsProbabilityMeasure (law P (HRS.Main.windowZeta m T u P X)) :=
    (Measure.isProbabilityMeasure_map_iff
      (HRS.MD.EQInterp.windowZeta_aemeasurable hd hs0 hsd V hV hβ0 hN hu hT0 P hfl hdm)).2 inferInstance
  haveI : IsProbabilityMeasure (law P' (HRS.Main.windowPath m T 0 Z)) :=
    (Measure.isProbabilityMeasure_map_iff
      (HRS.MD.EQGaussWindow.eqgw_fidi hd hs0 hsd V hβ0 ρβ m T P' Z hZ 0 le_rfl).1).2 inferInstance
  have hC0 : 0 ≤ C * (N : ℝ) ^ (-(1 : ℝ) / 2) := mul_nonneg hC.le hNpow
  refine ⟨hW2, ?_, ?_⟩
  · intro p hp1 hp2
    exact (HRS.wassersteinE_mono p 2 hp1 hp2 _ _).trans hW2
  · intro k hk
    have hsucc : ∀ j : ℕ,
        smoothDist (j + 1) (law P (HRS.Main.windowZeta m T u P X))
          (law P' (HRS.Main.windowPath m T 0 Z)) ≤
        smoothDist 1 (law P (HRS.Main.windowZeta m T u P X))
          (law P' (HRS.Main.windowPath m T 0 Z)) := by
      intro j
      induction j with
      | zero => exact le_rfl
      | succ j ih => exact (HRS.smoothDist_succ_le (j + 1) _ _).trans ih
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h1 : ENNReal.ofReal (smoothDist 1 (law P (HRS.Main.windowZeta m T u P X))
        (law P' (HRS.Main.windowPath m T 0 Z))) ≤ ENNReal.ofReal (C * (N : ℝ) ^ (-(1 : ℝ) / 2)) :=
      (HRS.smoothDist_one_le_wasserstein _ _).trans
        ((HRS.wassersteinE_one_le_two _ _).trans hW2)
    exact (hsucc j).trans ((ENNReal.ofReal_le_ofReal_iff hC0).1 h1)

end PathsPart

end HRS.ME.FamU

end
