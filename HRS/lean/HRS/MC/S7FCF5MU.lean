import HRS.MC.S7FCF5HC1a

/-!
# Utilities for the proof of block C1b of packet `fcf5` (`fcf5_C1b_mode_sup`, `S7FCF5Plan.lean`)

Lebesgue-integral inequalities and measurability facts used in `S7FCF5MC1b.lean`:

* `S7FCF5M_split3`: the `r`-th moment of a three-term bound with measurable summands;
* `S7FCF5M_lyap`: the Lyapunov inequality `E Y^q ≤ (E Y^p)^{q/p}` for measurable `Y`, `1 ≤ q ≤ p`;
* `S7FCF5M_realMode_moment`: uniform (in `k`, `N`, the realisation and `t ≥ 0`) moments of the mode statistic of `e_k`;
* measurability in `ω` of the mode statistic at a fixed time, of the drift on `[0,∞)` (joint, from A4a/A4b), and of its
  window integral (Tonelli);
* deterministic enorm bounds: the mode increment and the window integral of the drift.

Namespace `HRS.MC.Sec7.S7FCF5M`, helpers prefixed `S7FCF5M_`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCF5M

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.FCF5Plan

variable {d : ℕ}

/-- The `r`-th moment of a three-term pointwise bound (`r ≥ 1`), all three summands measurable. -/
theorem S7FCF5M_split3 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {r : ℝ} (hr : 1 ≤ r)
    {F A Y Z : Ω → ℝ≥0∞} (hA : Measurable A) (hY : Measurable Y) (hZ : Measurable Z)
    (hF : ∀ᵐ ω ∂P, F ω ≤ A ω + Y ω + Z ω) :
    ∫⁻ ω, F ω ^ r ∂P ≤
      2 ^ (r - 1) * (2 ^ (r - 1) * (∫⁻ ω, A ω ^ r ∂P + ∫⁻ ω, Y ω ^ r ∂P) + ∫⁻ ω, Z ω ^ r ∂P) := by
  have hA' : Measurable fun ω => A ω ^ r := hA.pow_const r
  have hY' : Measurable fun ω => Y ω ^ r := hY.pow_const r
  have hZ' : Measurable fun ω => Z ω ^ r := hZ.pow_const r
  have hs : Measurable fun ω => A ω ^ r + Y ω ^ r := hA'.add hY'
  have hpt : ∀ᵐ ω ∂P, F ω ^ r ≤ 2 ^ (r - 1) * (2 ^ (r - 1) * (A ω ^ r + Y ω ^ r) + Z ω ^ r) := by
    filter_upwards [hF] with ω hω
    calc F ω ^ r ≤ (A ω + Y ω + Z ω) ^ r := ENNReal.rpow_le_rpow hω (by linarith)
      _ ≤ 2 ^ (r - 1) * ((A ω + Y ω) ^ r + Z ω ^ r) :=
          ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hr
      _ ≤ 2 ^ (r - 1) * (2 ^ (r - 1) * (A ω ^ r + Y ω ^ r) + Z ω ^ r) := by
          gcongr
          exact ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hr
  have hm : Measurable fun ω => 2 ^ (r - 1) * (A ω ^ r + Y ω ^ r) + Z ω ^ r :=
    (measurable_const.mul hs).add hZ'
  calc ∫⁻ ω, F ω ^ r ∂P
      ≤ ∫⁻ ω, 2 ^ (r - 1) * (2 ^ (r - 1) * (A ω ^ r + Y ω ^ r) + Z ω ^ r) ∂P := lintegral_mono_ae hpt
    _ = 2 ^ (r - 1) * (2 ^ (r - 1) * (∫⁻ ω, A ω ^ r ∂P + ∫⁻ ω, Y ω ^ r ∂P) + ∫⁻ ω, Z ω ^ r ∂P) := by
        rw [lintegral_const_mul _ hm, lintegral_add_right _ hZ', lintegral_const_mul _ hs,
          lintegral_add_left hA']

/-- Lyapunov inequality for a measurable `Y` and `1 ≤ q ≤ p`, under a probability measure:
`E Y^q ≤ (E Y^p)^{q/p}`.  Hölder (`S7FCF5H_holder`) applied to `Y^q` with exponent `p/q`. -/
theorem S7FCF5M_lyap {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {q p : ℝ} (hq : 1 ≤ q) (hqp : q ≤ p) {Y : Ω → ℝ≥0∞} (hY : Measurable Y) :
    ∫⁻ ω, Y ω ^ q ∂P ≤ (∫⁻ ω, Y ω ^ p ∂P) ^ (q / p) := by
  have hq0 : 0 < q := by linarith
  have hp0 : 0 < p := by linarith
  have hr : 1 ≤ p / q := by
    rw [le_div_iff₀ hq0]
    linarith
  have hpq : (p / q) * (q / p) = 1 := by field_simp
  have hqp' : q * (p / q) = p := by field_simp
  have hmeas : Measurable fun ω => Y ω ^ q := hY.pow_const q
  have h := HRS.MC.Sec7.S7FCF5H.S7FCF5H_holder P hr hmeas
  have hpow : ∀ ω, (Y ω ^ q) ^ (p / q) = Y ω ^ p := fun ω => by
    rw [← ENNReal.rpow_mul, hqp']
  simp only [measure_univ, ENNReal.one_rpow, one_mul, hpow] at h
  calc ∫⁻ ω, Y ω ^ q ∂P
      = ((∫⁻ ω, Y ω ^ q ∂P) ^ (p / q)) ^ (q / p) := by
        rw [← ENNReal.rpow_mul, hpq, ENNReal.rpow_one]
    _ ≤ (∫⁻ ω, Y ω ^ p ∂P) ^ (q / p) := ENNReal.rpow_le_rpow h (div_nonneg hq0.le hp0.le)

/-- Uniform moments of the mode statistic of `e_k` at times `t ≥ 0`: the constant does not depend on `k`
(because `|e_k| ≤ √2`), on `N`, the realisation or `t`.  From F1 (`s7fcw3_core`) and `S7FCF5H_eta_Lq`. -/
theorem S7FCF5M_realMode_moment (R : Regime d) {r : ℝ} (hr : 1 ≤ r) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ (k : NonzeroLattice d) (N : ℕ), 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        FCPrepared R P X₀ W X → ∀ t : ℝ, 0 ≤ t →
          ∫⁻ ω, ‖fcf5Eta R X (Torus.realMode k) t ω‖ₑ ^ r ∂P ≤ ENNReal.ofReal C0 := by
  obtain ⟨C0', hC0', hcore⟩ := HRS.MC.Sec7.S7FCW3.s7fcw3_core R r hr
  refine ⟨Real.sqrt 2 ^ r * C0', mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) hC0', ?_⟩
  intro k N hN Ω _ P _ X₀ W X hprep t ht
  have hmeas : Measurable (Torus.realMode k : Torus d → ℝ) :=
    (HRS.FieldSingAux.continuous_realMode k).measurable
  have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  exact HRS.MC.Sec7.S7FCF5H.S7FCF5H_eta_Lq P R X t (q := r) (by linarith) (C0 := C0')
    (fun b hb1 hb2 => hcore N hN P X₀ W X hprep t ht b hb1 hb2) (Torus.realMode k) hmeas
    (M := Real.sqrt 2) hpos (fun x => Torus.abs_realMode_le k x)

/-- Measurability in `ω` of the mode statistic `η_N^t(f)` at a fixed time `t ≥ 0`, for a bounded measurable `f`
(from A4a with the constant-in-time family `G u = f`). -/
theorem S7FCF5M_fixed_meas (R : Regime d) {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hprep : FCPrepared R P X₀ W X) (f : Torus d → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B)
    {t : ℝ} (ht : 0 ≤ t) :
    Measurable fun ω => ‖fcf5Eta R X f t ω‖ₑ := by
  have hA := HRS.MC.Sec7.S7FCF5D.fcf5_A4a_eta_meas_proof R P X₀ W X hprep (fun _ x => f x)
    (hf.comp measurable_snd) B (fun _ x => hB x)
  have hc : Measurable fun ω : Ω => ((t, ω) : ℝ × Ω) := measurable_const.prodMk measurable_id
  have h := hA.comp hc
  have hmax : max t 0 = t := max_eq_left ht
  have h2 : (fun ω => ‖fcf5Eta R X f t ω‖ₑ) = fun ω => ‖fcf5Eta R X f (max t 0) ω‖ₑ := by
    rw [hmax]
  rw [h2]
  exact h.enorm

/-- Measurability of the drift `(u,ω) ↦ ‖fcf5Drift(max u 0)(ω)‖ₑ` for `f = e_k` (from A3, A2, A4a, A4b). -/
theorem S7FCF5M_drift_meas (R : Regime d) {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hprep : FCPrepared R P X₀ W X) (k : NonzeroLattice d) :
    Measurable fun p : ℝ × Ω => ‖fcf5Drift R X (Torus.realMode k) (max p.1 0) p.2‖ₑ := by
  have hA3 := HRS.MC.Sec7.S7FCF5A.fcf5_A3_gen_meas_proof R (HRS.FieldSingAux.isSmooth_realMode k)
  obtain ⟨Cg, hCg, hA2⟩ := HRS.MC.Sec7.S7FCF5A.fcf5_A2_gen_bound_proof R
  have hG : Measurable (Function.uncurry fun u x => fcGen R (max u 0) (Torus.realMode k) x) := hA3
  have hA4a := HRS.MC.Sec7.S7FCF5D.fcf5_A4a_eta_meas_proof R P X₀ W X hprep
    (fun u x => fcGen R (max u 0) (Torus.realMode k) x) hG (Cg * Lattice.jp k.1 ^ 2)
    (fun u x => hA2 (max u 0) (le_max_right _ _) k x)
  have hA4b := HRS.MC.Sec7.S7FCF5D.fcf5_A4b_comm_meas_proof R P X₀ W X hprep
    (HRS.FieldSingAux.isSmooth_realMode k)
  have hE : Measurable fun p : ℝ × Ω => fcf5Eta R X (fcGen R (max p.1 0) (Torus.realMode k)) (max p.1 0) p.2 := by
    have e : ∀ u : ℝ, max (max u 0) 0 = max u 0 := fun u => max_eq_left (le_max_right _ _)
    simpa only [e] using hA4a
  have hD : Measurable fun p : ℝ × Ω => fcf5Drift R X (Torus.realMode k) (max p.1 0) p.2 :=
    hE.sub (measurable_const.mul hA4b)
  exact hD.enorm

/-- Measurability in `ω` of the window integral `∫_{[a,a+T]} ‖drift_u‖ₑ du` (Tonelli). -/
theorem S7FCF5M_window_meas (R : Regime d) {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hprep : FCPrepared R P X₀ W X) (k : NonzeroLattice d) {a : ℝ} (ha : 0 ≤ a) (T : ℝ) :
    Measurable fun ω => ∫⁻ u in Set.Icc a (a + T), ‖fcf5Drift R X (Torus.realMode k) u ω‖ₑ := by
  have hm := S7FCF5M_drift_meas R P X₀ W X hprep k
  have heq : (fun ω => ∫⁻ u in Set.Icc a (a + T), ‖fcf5Drift R X (Torus.realMode k) u ω‖ₑ)
      = fun ω => ∫⁻ u in Set.Icc a (a + T), ‖fcf5Drift R X (Torus.realMode k) (max u 0) ω‖ₑ := by
    funext ω
    refine setLIntegral_congr_fun measurableSet_Icc (fun u hu => ?_)
    rw [max_eq_left (le_trans ha hu.1)]
  rw [heq]
  exact hm.lintegral_prod_left'

/-- Deterministic bound: `‖∫_τ^σ g‖ₑ ≤ ∫⁻_{[a,b]} ‖g‖ₑ` for `a ≤ τ ≤ b`, `τ ≤ σ` is not needed beyond `a ≤ τ`. -/
theorem S7FCF5M_int_enorm_le (g : ℝ → ℝ) {a τ b : ℝ} (haτ : a ≤ τ) (hτb : τ ≤ b) :
    ‖∫ u in a..τ, g u‖ₑ ≤ ∫⁻ u in Set.Icc a b, ‖g u‖ₑ := by
  rw [intervalIntegral.integral_of_le haτ]
  calc ‖∫ u in Set.Ioc a τ, g u‖ₑ ≤ ∫⁻ u in Set.Ioc a τ, ‖g u‖ₑ := enorm_integral_le_lintegral_enorm g
    _ ≤ ∫⁻ u in Set.Icc a b, ‖g u‖ₑ :=
        lintegral_mono_set (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl hτb))

/-- Triangle inequalities for one mode increment `e_τ - e_a = (m_τ - m_a) + I`. -/
theorem S7FCF5M_pt (ea et ma mt I : ℝ) (h : et - ea = (mt - ma) + I) :
    ‖et‖ₑ ≤ ‖ea‖ₑ + ‖mt - ma‖ₑ + ‖I‖ₑ ∧ ‖mt - ma‖ₑ ≤ ‖et‖ₑ + ‖ea‖ₑ + ‖I‖ₑ := by
  constructor
  · have e1 : et = ea + ((mt - ma) + I) := by linarith
    calc ‖et‖ₑ = ‖ea + ((mt - ma) + I)‖ₑ := by rw [← e1]
      _ ≤ ‖ea‖ₑ + ‖(mt - ma) + I‖ₑ := enorm_add_le _ _
      _ ≤ ‖ea‖ₑ + (‖mt - ma‖ₑ + ‖I‖ₑ) := by gcongr; exact enorm_add_le _ _
      _ = ‖ea‖ₑ + ‖mt - ma‖ₑ + ‖I‖ₑ := by ring
  · have e2 : mt - ma = (et - ea) - I := by linarith
    calc ‖mt - ma‖ₑ = ‖(et - ea) - I‖ₑ := by rw [← e2]
      _ ≤ ‖et - ea‖ₑ + ‖I‖ₑ := enorm_sub_le
      _ ≤ (‖et‖ₑ + ‖ea‖ₑ) + ‖I‖ₑ := by gcongr; exact enorm_sub_le
      _ = ‖et‖ₑ + ‖ea‖ₑ + ‖I‖ₑ := rfl

/-- A point of the countable window set lies in the window `[a, a+T]`. -/
theorem S7FCF5M_rat_mem {a T t : ℝ} (h : t ∈ fcf5Rat a T) : t ∈ Set.Icc a (a + T) := by
  obtain ⟨q, hq, rfl⟩ := h
  exact ⟨by linarith [hq.1], by linarith [hq.2]⟩

/-- The window set `fcf5Rat a T` is countable. -/
theorem S7FCF5M_rat_countable (a T : ℝ) : (fcf5Rat a T).Countable := by
  refine (Set.countable_range (fun q : ℚ => a + (q : ℝ))).mono ?_
  rintro t ⟨q, _, ht⟩
  exact ⟨q, ht.symm⟩

/-- `2 ^ r` in `ℝ≥0∞` as `ENNReal.ofReal (2 ^ r)`. -/
theorem S7FCF5M_two_rpow (r : ℝ) : (2 : ℝ≥0∞) ^ r = ENNReal.ofReal (2 ^ r) := by
  rw [← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
  simp

end HRS.MC.Sec7.S7FCF5M

end
