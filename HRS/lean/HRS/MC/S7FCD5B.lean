import HRS.MC.S7FCD5A
import HRS.MC.S7FCF5IE2
import HRS.MC.S7FCD4
import HRS.MC.L2C0

/-!
# Packet fcf5p, D5: proof of `s7_FC_D5_mean` (statement copied verbatim from `HRS/MC/S7FCPlan.lean`)

Route.  Put `D_N^t := √N • ofMeasureDiff r (E μ_N^t) μ^t` (`S7FCD5B_D`).  Then

* pointwise (no a.s. needed): `η_N^t(ω) = ζ_N^t(ω) + D_N^t` (`S7FCD5B_identity`), since `ofMeasureDiff` is additive
  in the second slot on coordinates;
* the mean: `E η_N^t = D_N^t` (`S7FCD5B_mean`, from `E ζ_N^t = 0`);
* `m_N := D_N` is a continuous path (it is `η_N(ω₀) - ζ_N(ω₀)` for a good `ω₀`), and `ζ_N = η_N - m_N` a.s.
  (`S7FCD5B_identity_a_s`);
* `‖m_N‖ ≤ W_2(Law η_N^{0+·}, Law η^{0+·})` (the window `a = 0` of `D4`): for each coupling `π` of the path laws
  and each time `s`, `‖E η_N^s‖ = ‖∫ (x_s - y_s) dπ‖ ≤ (∫ ‖x_s - y_s‖² dπ)^{1/2}` (`S7FCD5A_coupling_bound`) and
  `E η^s = 0` (`S7FCD5A_eta_integral_zero`), then sup over `s`;
* `W_2 → 0` by `D4` (`s7_FC_D4_eta_W2_proof`, term `a = 0`).

Namespace `HRS.MC.Sec7.S7FCD5B`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCD5B

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.FCF5Plan

variable {d : ℕ}

/-- The deterministic mean window `D_N^t = √N • ofMeasureDiff r (E μ_N^t) (μ^t)`, `E μ_N^t` the mean empirical
measure of the law of `X_t`. -/
def S7FCD5B_D (R : Regime d) (r : ℝ) {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → Config d N) (t : ℝ) : NegSobolev d r :=
  Real.sqrt N • NegSobolev.ofMeasureDiff r (meanEmpirical (P.map (X t.toNNReal))) (withDensityReal (R.ρ t))

/-! ### Windows as `toPath` -/

theorem S7FCD5B_toPath_apply {Ω : Type} (r T : ℝ) (Y : ℝ → Ω → NegSobolev d r) (ω : Ω)
    (h : Continuous fun t : Set.Icc (0 : ℝ) T => Y t ω) (s : Set.Icc (0 : ℝ) T) :
    PathSpace.at' (toPath r T Y ω) s = Y s ω := by
  have hw : toPath r T Y ω = (⟨fun t => Y t ω, h⟩ : C(Set.Icc (0 : ℝ) T, NegSobolev d r)) := by
    unfold toPath
    exact dif_pos h
  rw [hw]
  rfl

theorem S7FCD5B_windowFluc_eq {Ω : Type} {N : ℕ} (R : Regime d) (r T : ℝ) (X : ℝ≥0 → Ω → Config d N)
    (ω : Ω) :
    HRS.Main.windowFluc r T 0 (Real.sqrt N) X R.ρ ω =
      toPath r T (fun t ω => etaE r (X t.toNNReal ω) (withDensityReal (R.ρ t))) ω := by
  unfold HRS.Main.windowFluc HRS.flucPath toPath etaE flucE
  refine HRS.MC.Sec7.S7FCF5I.S7FCF5I_dite_congr _ _ ?_
  funext t
  simp only [Real.toNNReal_zero, zero_add]

theorem S7FCD5B_procWin_eq {Ω' : Type} (r T : ℝ) (η : ℝ → Ω' → NegSobolev d r) (ω : Ω') :
    procWin r T 0 η ω = toPath r T (fun t ω => η t ω) ω := by
  unfold procWin
  simp only [zero_add]

theorem S7FCD5B_zetaWin_eq {Ω : Type} [MeasurableSpace Ω] {N : ℕ} (r T : ℝ) (P : Measure Ω)
    (X : ℝ≥0 → Ω → Config d N) (ω : Ω) :
    zetaWin r T 0 P X ω = toPath r T (fun t ω => zetaAt r P X t ω) ω := by
  unfold zetaWin
  simp only [zero_add]

/-! ### Honest windows and the pointwise identity -/

/-- The two windows are a.s. continuous (E1 at `a = 0`). -/
theorem S7FCD5B_honest {Ω : Type} [MeasurableSpace Ω] (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6)
    (T : ℝ) {N : ℕ} (hN : 1 ≤ N) (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hreal : FCPrepared R P X₀ W X) :
    (∀ᵐ ω ∂P, Continuous fun t : Set.Icc (0 : ℝ) T => etaE r (X (Real.toNNReal (t : ℝ)) ω) (withDensityReal (R.ρ (t : ℝ)))) ∧
    (∀ᵐ ω ∂P, Continuous fun t : Set.Icc (0 : ℝ) T => zetaAt r P X t ω) := by
  obtain ⟨h1, h2⟩ := HRS.MC.Sec7.S7FCF5G.fcf5_E1_window_cont_proof R r hr T hN P X₀ W X hreal 0 le_rfl
  refine ⟨?_, ?_⟩
  · filter_upwards [h1] with ω hω
    simpa only [zero_add] using hω
  · filter_upwards [h2] with ω hω
    simpa only [zero_add, zetaAt] using hω

theorem S7FCD5B_hdens (R : Regime d) (t : ℝ) (ht : 0 ≤ t) : IsProbDensity (R.ρ t) :=
  (R.mf (t + 1) (by linarith)).density t ⟨ht, by linarith⟩

/-- The pointwise decomposition `η_N^t = ζ_N^t + D_N^t` (no almost-sure qualifier). -/
theorem S7FCD5B_identity {Ω : Type} [MeasurableSpace Ω] {N : ℕ} (R : Regime d) (r : ℝ)
    (hr : (d : ℝ) < 2 * r) (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → Config d N)
    (hadapt : ∀ t : ℝ≥0, Measurable (X t)) (hN : 1 ≤ N) (t : ℝ) (ht : 0 ≤ t) (ω : Ω) :
    etaE r (X t.toNNReal ω) (withDensityReal (R.ρ t)) =
      zetaAt r P X t ω + S7FCD5B_D R r P X t := by
  haveI := isProb_withDensityReal (S7FCD5B_hdens R t ht)
  haveI := HRS.empirical_isProbabilityMeasure (show 0 < N by omega) (X t.toNNReal ω)
  haveI : IsProbabilityMeasure (P.map (X t.toNNReal)) :=
    (Measure.isProbabilityMeasure_map_iff (hadapt _).aemeasurable).2 inferInstance
  haveI := HRS.isProbabilityMeasure_meanEmpirical (P.map (X t.toNNReal)) hN
  unfold etaE flucE zetaAt zetaE S7FCD5B_D
  rw [S7FCD5A.S7FCD5A_ofMD_triangle hr (empirical (X t.toNNReal ω)) (withDensityReal (R.ρ t))
    (meanEmpirical (P.map (X t.toNNReal))), smul_add]

theorem S7FCD5B_path_ext {r T : ℝ} {w v : PathSpace d r T} (h : ∀ s : Set.Icc (0 : ℝ) T, PathSpace.at' w s = PathSpace.at' v s) :
    w = v :=
  ContinuousMap.ext h

/-! ### Bounds and means -/

theorem S7FCD5B_eta_norm_le {Ω : Type} [MeasurableSpace Ω] {N : ℕ} (R : Regime d) (r : ℝ)
    (hr : (d : ℝ) < 2 * r) (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → Config d N)
    (hN : 1 ≤ N) (t : ℝ) (ht : 0 ≤ t) (ω : Ω) :
    ‖etaE r (X t.toNNReal ω) (withDensityReal (R.ρ t))‖ ≤
      Real.sqrt N * Real.sqrt (8 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * r))) := by
  haveI := isProb_withDensityReal (S7FCD5B_hdens R t ht)
  haveI := HRS.empirical_isProbabilityMeasure (show 0 < N by omega) (X t.toNNReal ω)
  unfold etaE flucE
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (HRS.norm_ofMeasureDiff_le hr _ _) (Real.sqrt_nonneg _)

theorem S7FCD5B_zeta_integrable {Ω : Type} [MeasurableSpace Ω] {N : ℕ} (r : ℝ) (hr : (d : ℝ) < 2 * r)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → Config d N)
    (hadapt : ∀ t : ℝ≥0, Measurable (X t)) (hN : 1 ≤ N) (t : ℝ) :
    Integrable (fun ω => zetaAt r P X t ω) P :=
  (integrable_const _).mono' (HRS.MC.Sec7.S7FCW12.s7fcw12_zetaAt_measurable r P X hadapt (by omega) t).aestronglyMeasurable
    (Eventually.of_forall fun ω => S7FCD5A.S7FCD5A_zetaAt_norm_le r hr P X hadapt hN t ω)

/-- The mean of the window `η_N^t` is the deterministic path `D_N^t`. -/
theorem S7FCD5B_mean {Ω : Type} [MeasurableSpace Ω] {N : ℕ} (R : Regime d) (r : ℝ)
    (hr : (d : ℝ) < 2 * r) (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → Config d N)
    (hadapt : ∀ t : ℝ≥0, Measurable (X t)) (hN : 1 ≤ N) (t : ℝ) (ht : 0 ≤ t) :
    ∫ ω, etaE r (X t.toNNReal ω) (withDensityReal (R.ρ t)) ∂P = S7FCD5B_D R r P X t := by
  rw [integral_congr_ae (Eventually.of_forall fun ω => S7FCD5B_identity R r hr P X hadapt hN t ht ω)]
  rw [integral_add (S7FCD5B_zeta_integrable r hr P X hadapt hN t) (integrable_const _), integral_const,
    S7FCD5A.S7FCD5A_zeta_integral_zero r hr P X hadapt hN t]
  simp

/-- The window `η_N^{·}` (with `σ = √N`) is bounded by `√N K` at every time (deterministically). -/
theorem S7FCD5B_Y_bound {Ω : Type} [MeasurableSpace Ω] {N : ℕ} (R : Regime d) (r T : ℝ)
    (hr : (d : ℝ) < 2 * r) (X : ℝ≥0 → Ω → Config d N) (hN : 1 ≤ N) (P : Measure Ω) [IsProbabilityMeasure P]
    (ω : Ω) (s : Set.Icc (0 : ℝ) T) :
    ‖PathSpace.at' (HRS.Main.windowFluc r T 0 (Real.sqrt N) X R.ρ ω) s‖ ≤
      Real.sqrt N * Real.sqrt (8 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * r))) := by
  rw [S7FCD5B_windowFluc_eq]
  by_cases h : Continuous fun t : Set.Icc (0 : ℝ) T =>
      etaE r (X (Real.toNNReal (t : ℝ)) ω) (withDensityReal (R.ρ (t : ℝ)))
  · rw [S7FCD5B_toPath_apply r T _ ω h s]
    exact S7FCD5B_eta_norm_le R r hr P X hN s s.2.1 ω
  · have hw : toPath r T (fun t ω => etaE r (X (Real.toNNReal t) ω) (withDensityReal (R.ρ t))) ω =
        (0 : PathSpace d r T) := by
      unfold toPath
      exact dif_neg h
    rw [hw]
    have hz : PathSpace.at' (0 : PathSpace d r T) s = 0 := rfl
    rw [hz, norm_zero]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- The Gaussian window `η^{·}` (the `procWin` of the limit field) is AEMeasurable into `PathSpace`. -/
theorem S7FCD5B_procWin_aemeasurable {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (r T : ℝ) (hT : 0 < T) (η : ℝ → Ω' → NegSobolev d r) (hm : ∀ t, Measurable (η t))
    (hc : ∀ᵐ ω ∂P', ContinuousOn (fun t => η t ω) (Set.Icc 0 T)) :
    AEMeasurable (procWin r T 0 η) P' := by
  have h := HRS.Uniform.Q45.aemeasurable_windowPath' P' hT (fun t ω => η t ω)
    (fun t _ => (hm t).aemeasurable) hc
  have hfun : procWin r T 0 η = HRS.Uniform.windowPath 0 T (fun t ω => η t ω) := by
    funext ω
    rw [S7FCD5B_procWin_eq]
    unfold toPath HRS.Uniform.windowPath
    refine HRS.MC.Sec7.S7FCF5I.S7FCF5I_dite_congr _ _ ?_
    funext t
    simp only [zero_add]
  rw [hfun]
  exact h

theorem S7FCD5B_procWin_val {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (r T : ℝ)
    (η : ℝ → Ω' → NegSobolev d r) (hc : ∀ᵐ ω ∂P', ContinuousOn (fun t => η t ω) (Set.Icc 0 T)) :
    ∀ᵐ ω ∂P', ∀ s : Set.Icc (0 : ℝ) T, PathSpace.at' (procWin r T 0 η ω) s = η s ω := by
  filter_upwards [hc] with ω hω
  rw [S7FCD5B_procWin_eq]
  have hcont : Continuous fun t : Set.Icc (0 : ℝ) T => η (t : ℝ) ω :=
    continuousOn_iff_continuous_restrict.1 hω
  intro s
  exact S7FCD5B_toPath_apply r T (fun t ω => η t ω) ω hcont s

/-! ### The coupling bound on path space at a fixed time -/

theorem S7FCD5B_eval_coupling (r T : ℝ) (μ ν : Measure (PathSpace d r T)) [IsProbabilityMeasure μ]
    (s : Set.Icc (0 : ℝ) T) (hμ : Integrable (fun w : PathSpace d r T => PathSpace.at' w s) μ)
    (π : Measure (PathSpace d r T × PathSpace d r T)) (hπ : IsCoupling π μ ν) :
    ENNReal.ofReal ‖∫ w, PathSpace.at' w s ∂μ - ∫ w, PathSpace.at' w s ∂ν‖ ≤
      (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π) ^ (1 / (2 : ℝ)) := by
  set ev : PathSpace d r T → NegSobolev d r := fun w => PathSpace.at' w s with hev
  have hevc0 : Continuous (fun f : C(Set.Icc (0 : ℝ) T, NegSobolev d r) => f s) := continuous_eval_const s
  have hevc : Continuous ev := hevc0
  have hevm : Measurable ev := hevc.measurable
  have hgm : Measurable (Prod.map ev ev) := hevm.prodMap hevm
  haveI : IsProbabilityMeasure π := IsCoupling.isProbabilityMeasure hπ
  haveI : IsProbabilityMeasure (μ.map ev) := (Measure.isProbabilityMeasure_map_iff hevm.aemeasurable).2 inferInstance
  have hπ' : IsCoupling (π.map (Prod.map ev ev)) (μ.map ev) (ν.map ev) := by
    constructor
    · have h1 : (π.map (Prod.map ev ev)).map Prod.fst = (π.map Prod.fst).map ev := by
        rw [Measure.map_map measurable_fst (hevm.prodMap hevm), Measure.map_map hevm measurable_fst]
        rfl
      rw [h1, hπ.1]
    · have h1 : (π.map (Prod.map ev ev)).map Prod.snd = (π.map Prod.snd).map ev := by
        rw [Measure.map_map measurable_snd (hevm.prodMap hevm), Measure.map_map hevm measurable_snd]
        rfl
      rw [h1, hπ.2]
  have hint' : Integrable (fun x : NegSobolev d r => x) (μ.map ev) :=
    (integrable_map_measure aestronglyMeasurable_id hevm.aemeasurable).2 hμ
  have key := S7FCD5A.S7FCD5A_coupling_bound (μ.map ev) (ν.map ev) hint' (π.map (Prod.map ev ev)) hπ'
  have e1 : ∫ x, x ∂(μ.map ev) = ∫ w, PathSpace.at' w s ∂μ :=
    integral_map hevm.aemeasurable aestronglyMeasurable_id
  have e2 : ∫ x, x ∂(ν.map ev) = ∫ w, PathSpace.at' w s ∂ν :=
    integral_map hevm.aemeasurable aestronglyMeasurable_id
  rw [e1, e2] at key
  refine key.trans ?_
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  have hmeas : Measurable fun z : NegSobolev d r × NegSobolev d r =>
      ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) := by
    have : Measurable fun z : NegSobolev d r × NegSobolev d r => ‖z.1 - z.2‖ :=
      (measurable_fst.sub measurable_snd).norm
    exact (this.pow_const (2 : ℝ)).ennreal_ofReal
  rw [lintegral_map hmeas hgm]
  apply lintegral_mono
  intro z
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow (norm_nonneg _) _ (by norm_num)
  exact ContinuousMap.norm_coe_le_norm (z.1 - z.2) s

end HRS.MC.Sec7.S7FCD5B

end
