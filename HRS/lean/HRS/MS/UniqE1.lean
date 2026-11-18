import HRS.MS.UniqM1Fin
import HRS.MS.UniqT3
import HRS.MS.UniqC2c

/-!
# E1 of `UniqPlan.md`, part 1: the time representation of `z_ε(τ,x)` and two weighted mass bounds

For `ψ_x := fun y => η_ε(x - y)` and `f_ε(σ,x) := forwardPairing D ρ t σ (z σ) ψ_x` (`fEps`):

* `e1_time_rep` : for a forward solution `z` and every `τ ∈ [0,t]`, **every** `x`,
  `moll d ε (z τ) x = ∫_{σ ∈ [0,τ]} f_ε(σ,x)`.
* `e1_weighted_l1` : `LocMass B u` gives `∫ |u| ⟨y⟩^{-(d+2)} ≤ Kw B` with `Kw = Kw(d)`.
* `e1_local_bound`, `e1_weighted_bound` : the two integral estimates used for the bound of `f_ε`.
* `e1_rho_decay` : the `⟨y⟩^{-(d+3)}` decay of `ρ^r` and `∇ρ^r` (the decay of `CoeffHypRd`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqE1

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqT3

variable {d : ℕ}

/-- `f_ε(σ,x) = ⟨𝓛^σ z(σ), η_ε(x - ·)⟩`. -/
def fEps (D : WholeDyn d) (ρ : ℝ → Euc d → ℝ) (t : ℝ) (z : ℝ → Euc d → ℝ) (ε : ℝ) (σ : ℝ)
    (x : Euc d) : ℝ :=
  forwardPairing D ρ t σ (z σ) (fun y => eta d ε (x - y))

theorem fEps_def (D : WholeDyn d) (ρ : ℝ → Euc d → ℝ) (t : ℝ) (z : ℝ → Euc d → ℝ) (ε σ : ℝ)
    (x : Euc d) :
    fEps D ρ t z ε σ x = forwardPairing D ρ t σ (z σ) (fun y => eta d ε (x - y)) := rfl

/-! ### The test functions `ψ_x` -/

theorem psi_contDiff (ε : ℝ) (x : Euc d) : ContDiff ℝ ∞ (fun y : Euc d => eta d ε (x - y)) :=
  eta_contDiff.comp (contDiff_const.sub contDiff_id)

theorem psi_compact {ε : ℝ} (hε : 0 < ε) (x : Euc d) :
    HasCompactSupport (fun y : Euc d => eta d ε (x - y)) :=
  (eta_hasCompactSupport hε).comp_homeomorph (Homeomorph.subLeft x)

/-! ### (a) The time representation, for every `x` -/

/-- **(a)** For every `τ ∈ [0,t]` and **every** `x`: `z_ε(τ,x) = ∫_{σ ∈ [0,τ]} f_ε(σ,x) dσ`.
(No integrability of `z τ` is needed: both sides are the Bochner integrals of `hz.eq`.) -/
theorem e1_time_rep {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} {t : ℝ} {z : ℝ → Euc d → ℝ}
    (hz : IsForwardDistSolutionW D ρ t z) {ε : ℝ} (hε : 0 < ε) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) t) (x : Euc d) :
    moll d ε (z τ) x = ∫ σ in Set.Icc (0 : ℝ) τ, fEps D ρ t z ε σ x := by
  have h := hz.eq (fun y => eta d ε (x - y)) (psi_contDiff ε x) (psi_compact hε x) τ hτ
  have h0 : (∫ y, z 0 y * eta d ε (x - y)) = 0 := by
    have : (fun y => z 0 y * eta d ε (x - y)) =ᵐ[volume] fun _ => 0 := by
      filter_upwards [hz.init] with y hy
      simp [hy]
    rw [integral_congr_ae this]; simp
  rw [h0, zero_add] at h
  refine Eq.trans ?_ h
  unfold moll
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [mul_comm]

/-! ### The decay `⟨y⟩^{-(d+3)}` of the density and its gradient -/

open HRS.MP.RdGen in
theorem e1_rho_decay (hd : 1 ≤ d) {r : ℕ} {Λ : ℝ} {ρ : Euc d → ℝ}
    (hfin : weightedSupE r ((d : ℝ) + 3) ρ < ⊤)
    (hΛ : (weightedSupE r ((d : ℝ) + 3) ρ).toReal ≤ Λ) :
    ∀ l, l ≤ r → ∀ y : Euc d, ‖iteratedFDeriv ℝ l ρ y‖ ≤
      (d : ℝ) ^ r * Λ * 2 ^ ((d : ℝ) + 3) * (1 + ‖y‖) ^ (-((d : ℝ) + 3)) := by
  intro l hl y
  have hΛ0 : 0 ≤ Λ := (ENNReal.toReal_nonneg).trans hΛ
  have hjpos : 0 < jbracket y := by unfold jbracket; positivity
  have hpt : ∀ i : Fin l → Fin d,
      |iteratedFDeriv ℝ l ρ y (fun p => EuclideanSpace.single (i p) 1)| ≤
        Λ * jbracket y ^ (-((d : ℝ) + 3)) := by
    intro i
    have h := (rg_partial_weight_bound hfin hl i y).trans hΛ
    have e : |iteratedFDeriv ℝ l ρ y (fun p => EuclideanSpace.single (i p) 1)| =
        (jbracket y ^ ((d : ℝ) + 3) * |partialDeriv i ρ y|) * jbracket y ^ (-((d : ℝ) + 3)) := by
      have : jbracket y ^ ((d : ℝ) + 3) * jbracket y ^ (-((d : ℝ) + 3)) = 1 := by
        rw [← Real.rpow_add hjpos]; simp
      unfold partialDeriv
      calc _ = |iteratedFDeriv ℝ l ρ y (fun p => EuclideanSpace.single (i p) 1)| * 1 := by ring
        _ = _ := by rw [← this]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hjpos.le _)
  have hn := rg_norm_le_of_partial hd (iteratedFDeriv ℝ l ρ y) hpt
  have h1 := rg_jb_rpow_le y (p := (d : ℝ) + 3) (by positivity)
  have hdr : (d : ℝ) ^ l ≤ (d : ℝ) ^ r :=
    pow_le_pow_right₀ (by exact_mod_cast hd) hl
  calc ‖iteratedFDeriv ℝ l ρ y‖ ≤ (d : ℝ) ^ l * (Λ * jbracket y ^ (-((d : ℝ) + 3))) := hn
    _ ≤ (d : ℝ) ^ r * (Λ * (2 ^ ((d : ℝ) + 3) * (1 + ‖y‖) ^ (-((d : ℝ) + 3)))) := by
        apply mul_le_mul hdr _ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left h1 hΛ0
    _ = _ := by ring

/-- The decay constant `A = d^{m+3} Λ' 2^{d+3}` (the constant `c1A` of packet C1). -/
theorem e1_rho_decay01 (hd : 1 ≤ d) {s : ℝ} {m : ℕ} {Λ T : ℝ} {ρ : ℝ → Euc d → ℝ}
    (hcoef : CoeffHypRd s m Λ T ρ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) :
    (∀ y, |ρ r y| ≤ HRS.MS.UniqC1.c1A d m Λ * (1 + ‖y‖) ^ (-((d : ℝ) + 3))) ∧
    (∀ y, ‖fderiv ℝ (ρ r) y‖ ≤ HRS.MS.UniqC1.c1A d m Λ * (1 + ‖y‖) ^ (-((d : ℝ) + 3))) := by
  have hcb := hcoef.regular.1 r hr
  have hcb0 : 0 ≤ HRS.cbNorm (m + 3) (ρ r) :=
    Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hΛ : (weightedSupE (m + 3) ((d : ℝ) + 3) (ρ r)).toReal ≤ max Λ 0 :=
    (by linarith [hcb.2.2, hcb0] : (weightedSupE (m + 3) ((d : ℝ) + 3) (ρ r)).toReal ≤ Λ).trans
      (le_max_left _ _)
  have key := e1_rho_decay hd hcb.2.1 hΛ
  have hA : HRS.MS.UniqC1.c1A d m Λ = (d : ℝ) ^ (m + 3) * max Λ 0 * 2 ^ ((d : ℝ) + 3) := rfl
  rw [hA]
  refine ⟨fun y => ?_, fun y => ?_⟩
  · have := key 0 (by omega) y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  · have := key 1 (by omega) y
    rwa [norm_iteratedFDeriv_one] at this

/-! ### Weighted `L¹` mass -/

theorem e1_weighted_l1 (d : ℕ) : ∃ Kw : ℝ, 0 ≤ Kw ∧ ∀ (B : ℝ) (u : Euc d → ℝ), 0 ≤ B →
    LocMass B u → ∫ y, ‖u y‖ * wt d y ≤ Kw * B := by
  obtain ⟨K, hK0, hK⟩ := exists_ball_l1_bound d 1
  set V : ℝ≥0∞ := volume (ball (0 : Euc d) 1) with hV
  have hV0 : V ≠ 0 := (measure_ball_pos volume _ one_pos).ne'
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  set a : ℝ := (d : ℝ) + 2 with ha
  set J : ℝ := ∫ c, wt d c with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun c => (wt_pos c).le
  have hVr : 0 < V.toReal := ENNReal.toReal_pos hV0 hVt
  have h2a : 0 < (2 : ℝ) ^ (-a) := Real.rpow_pos_of_pos two_pos _
  refine ⟨K * J / (V.toReal * 2 ^ (-a)), by positivity, fun B u hB hu => ?_⟩
  set F : Euc d → Euc d → ℝ≥0∞ := fun y c =>
    if dist c y < 1 then ‖u y‖ₑ * ENNReal.ofReal (wt d c) else 0 with hF
  have hmeas : AEMeasurable (Function.uncurry F) (volume.prod volume) := by
    have h1 : AEMeasurable (fun p : Euc d × Euc d => ‖u p.1‖ₑ) (volume.prod volume) :=
      hu.1.enorm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    have h2 : Measurable (fun p : Euc d × Euc d => ENNReal.ofReal (wt d p.2)) := by
      unfold wt; fun_prop
    have h3 : MeasurableSet {p : Euc d × Euc d | dist p.2 p.1 < 1} :=
      measurableSet_lt (by fun_prop) measurable_const
    have := (h1.mul h2.aemeasurable).indicator h3
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    simp [hF, Set.indicator_apply, Function.uncurry]
  have hswap := lintegral_lintegral_swap hmeas
  have h1 : ∀ y, V * (ENNReal.ofReal ((2 : ℝ) ^ (-a)) * (‖u y‖ₑ * ENNReal.ofReal (wt d y))) ≤
      ∫⁻ c, F y c := by
    intro y
    have : ∫⁻ c, F y c = ∫⁻ c in ball y 1, ‖u y‖ₑ * ENNReal.ofReal (wt d c) := by
      rw [← lintegral_indicator measurableSet_ball]
      refine lintegral_congr fun c => ?_
      by_cases h : dist c y < 1
      · rw [Set.indicator_of_mem (mem_ball.2 h)]; simp [hF, h]
      · rw [Set.indicator_of_notMem (by rw [mem_ball]; exact h)]; simp [hF, h]
    rw [this]
    calc V * (ENNReal.ofReal ((2 : ℝ) ^ (-a)) * (‖u y‖ₑ * ENNReal.ofReal (wt d y)))
        = ∫⁻ c in ball y 1, ENNReal.ofReal ((2 : ℝ) ^ (-a)) * (‖u y‖ₑ * ENNReal.ofReal (wt d y)) := by
          rw [setLIntegral_const, Measure.addHaar_ball_center volume y, hV, mul_comm]
      _ ≤ _ := by
          refine setLIntegral_mono' measurableSet_ball fun c hc => ?_
          have := wt_ball_le y c (by rw [← dist_eq_norm]; exact mem_ball.1 hc)
          calc _ = ‖u y‖ₑ * ENNReal.ofReal ((2 : ℝ) ^ (-a) * wt d y) := by
                rw [ENNReal.ofReal_mul (by positivity)]; ring
            _ ≤ _ := by gcongr
  have h2 : ∀ c, ∫⁻ y, F y c ≤ ENNReal.ofReal (wt d c) * ENNReal.ofReal (K * B) := by
    intro c
    have : ∫⁻ y, F y c = ENNReal.ofReal (wt d c) * ∫⁻ y in ball c 1, ‖u y‖ₑ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator measurableSet_ball]
      refine lintegral_congr fun y => ?_
      by_cases h : dist c y < 1
      · rw [Set.indicator_of_mem (mem_ball.2 (by rwa [dist_comm]))]; simp [hF, h, mul_comm]
      · rw [Set.indicator_of_notMem (by rw [mem_ball, dist_comm]; exact h)]; simp [hF, h]
    rw [this]
    gcongr
    exact hK B u hB hu c
  set I : ℝ≥0∞ := ∫⁻ y, ‖u y‖ₑ * ENNReal.ofReal (wt d y) with hI
  have h3 : V * (ENNReal.ofReal ((2 : ℝ) ^ (-a)) * I) ≤
      ENNReal.ofReal (K * B) * ∫⁻ c, ENNReal.ofReal (wt d c) := by
    calc _ = ∫⁻ y, V * (ENNReal.ofReal ((2 : ℝ) ^ (-a)) * (‖u y‖ₑ * ENNReal.ofReal (wt d y))) := by
          rw [lintegral_const_mul' _ _ hVt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ∫⁻ y, ∫⁻ c, F y c := lintegral_mono h1
      _ = ∫⁻ c, ∫⁻ y, F y c := hswap
      _ ≤ ∫⁻ c, ENNReal.ofReal (wt d c) * ENNReal.ofReal (K * B) := lintegral_mono h2
      _ = _ := by rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]
  have hIfin : I ≠ ⊤ := (key_fin hu.1 (B ^ 2) hu.2).ne
  have hwl : ∫⁻ c, ENNReal.ofReal (wt d c) = ENNReal.ofReal J :=
    (ofReal_integral_eq_lintegral_ofReal wt_integrable
      (Filter.Eventually.of_forall fun c => (wt_pos c).le)).symm
  rw [hwl, ← ENNReal.ofReal_mul (by positivity)] at h3
  have h4 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h3
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal h2a.le,
    ENNReal.toReal_ofReal (by positivity)] at h4
  have hint : ∫ y, ‖u y‖ * wt d y = I.toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun y => mul_nonneg (norm_nonneg _) (wt_pos y).le)
      (hu.1.norm.mul wt_integrable.aestronglyMeasurable)]
    congr 1
    refine lintegral_congr fun y => ?_
    rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm_eq_enorm]
  rw [hint]
  have : I.toReal ≤ K * B * J / (V.toReal * 2 ^ (-a)) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [h4]
  calc I.toReal ≤ K * B * J / (V.toReal * 2 ^ (-a)) := this
    _ = _ := by ring

/-- `|∫ u h| ≤ C Kw B` whenever `|h| ≤ C wt`, `h` a.e.-strongly measurable. -/
theorem e1_weighted_bound (d : ℕ) : ∃ Kw : ℝ, 0 ≤ Kw ∧ ∀ (B : ℝ) (u : Euc d → ℝ) (h : Euc d → ℝ)
    (C : ℝ), 0 ≤ B → LocMass B u → AEStronglyMeasurable h volume →
    (∀ y, |h y| ≤ C * wt d y) → |∫ y, u y * h y| ≤ C * Kw * B := by
  obtain ⟨Kw, hKw0, hKw⟩ := e1_weighted_l1 d
  refine ⟨Kw, hKw0, fun B u h C hB hu hh hC => ?_⟩
  have hC0 : 0 ≤ C := by
    have := (abs_nonneg (h 0)).trans (hC 0)
    exact nonneg_of_mul_nonneg_left this (wt_pos 0)
  have hi : Integrable (fun y => ‖u y‖ * wt d y) volume := uw_int hu.1 (B ^ 2) hu.2
  rw [← Real.norm_eq_abs]
  calc ‖∫ y, u y * h y‖ ≤ ∫ y, C * (‖u y‖ * wt d y) :=
        norm_integral_le_of_norm_le (hi.const_mul C) (Filter.Eventually.of_forall fun y => by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          calc |u y| * |h y| ≤ |u y| * (C * wt d y) := by gcongr; exact hC y
            _ = _ := by ring)
    _ = C * ∫ y, ‖u y‖ * wt d y := integral_const_mul _ _
    _ ≤ C * (Kw * B) := by gcongr; exact hKw B u hB hu
    _ = _ := by ring

/-- `|∫ u h| ≤ H K_r B` whenever `h` is bounded by `H` and vanishes off `closedBall c r`. -/
theorem e1_local_bound (d : ℕ) (r : ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (B : ℝ) (u : Euc d → ℝ) (c : Euc d)
    (h : Euc d → ℝ) (H : ℝ), 0 ≤ B → LocMass B u → (∀ y, y ∉ closedBall c r → h y = 0) →
    (∀ y, |h y| ≤ H) → |∫ y, u y * h y| ≤ H * K * B := by
  obtain ⟨K, hK0, hK⟩ := exists_closedBall_l1_real d r
  refine ⟨K, hK0, fun B u c h H hB hu hz hH => ?_⟩
  have hH0 : 0 ≤ H := (abs_nonneg _).trans (hH 0)
  have hsub : closedBall c r ⊆ ball c (r + 1) := fun y hy => by
    rw [mem_closedBall] at hy; rw [mem_ball]; linarith
  have hint : IntegrableOn (fun y => ‖u y‖) (closedBall c r) volume :=
    ((hu.integrableOn_ball c (r + 1)).mono_set hsub).norm
  have hset : ∫ y, u y * h y = ∫ y in closedBall c r, u y * h y :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by simp [hz y hy])).symm
  rw [hset, ← Real.norm_eq_abs]
  calc ‖∫ y in closedBall c r, u y * h y‖ ≤ ∫ y in closedBall c r, H * ‖u y‖ :=
        norm_integral_le_of_norm_le (hint.const_mul H) (Filter.Eventually.of_forall fun y => by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          have := hH y
          calc |u y| * |h y| ≤ |u y| * H := by gcongr
            _ = _ := by ring)
    _ = H * ∫ y in closedBall c r, ‖u y‖ := integral_const_mul _ _
    _ ≤ H * (K * B) := by gcongr; exact hK B u hB hu c
    _ = _ := by ring

end HRS.MS.UniqE1
