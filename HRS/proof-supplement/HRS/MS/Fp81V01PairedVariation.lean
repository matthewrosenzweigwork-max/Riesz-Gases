import HRS.MS.Fp81V01Cumulative

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.V01

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.S111T
open HRS.MS.ProClosureS111

variable {d r : ℕ}
variable {s a β γ T u c B Pw : ℝ}
variable {ρ : Euc d → ℝ}
variable {Ω : Type*} [MeasurableSpace Ω]
variable {E : r26t6_WeightedChart d r Pw}

local notation "X" => R2X d T
local notation "P2" => projTensor X 2
local notation "P3" => projTensor X 3
local notation "C" => r26t6_thermalCoeff d s a β ρ

private theorem fp81v01_insert_integral_sub (P : Measure Ω) (j : Fin 3)
    {A₀ A₁ Z : Ω → X}
    (hI₀ : Integrable (fun w => Insert j (A₀ w) (Z w) (Z w)) P)
    (hI₁ : Integrable (fun w => Insert j (A₁ w) (Z w) (Z w)) P) :
    (∫ w, Insert j (A₀ w) (Z w) (Z w) ∂P) -
      (∫ w, Insert j (A₁ w) (Z w) (Z w) ∂P) =
        ∫ w, Insert j (A₀ w - A₁ w) (Z w) (Z w) ∂P := by
  calc
    _ = ∫ w, Insert j (A₀ w) (Z w) (Z w) -
        Insert j (A₁ w) (Z w) (Z w) ∂P := (integral_sub hI₀ hI₁).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with w
      simp only [map_sub, sub_apply]

private theorem fp81v01_pairinsert_integral_sub (P : Measure Ω) (j : Fin 3)
    {Q₀ Q₁ : Ω → P2} {Z : Ω → X}
    (hI₀ : Integrable (fun w => PairInsert j (Q₀ w) (Z w)) P)
    (hI₁ : Integrable (fun w => PairInsert j (Q₁ w) (Z w)) P) :
    (∫ w, PairInsert j (Q₀ w) (Z w) ∂P) -
      (∫ w, PairInsert j (Q₁ w) (Z w) ∂P) =
        ∫ w, PairInsert j (Q₀ w - Q₁ w) (Z w) ∂P := by
  calc
    _ = ∫ w, PairInsert j (Q₀ w) (Z w) -
        PairInsert j (Q₁ w) (Z w) ∂P := (integral_sub hI₀ hI₁).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with w
      simp only [map_sub, sub_apply]

private theorem fp81v01_integral_add3 (P : Measure Ω) {F₁ F₂ F₃ : Ω → P3}
    (h₁ : Integrable F₁ P) (h₂ : Integrable F₂ P) (h₃ : Integrable F₃ P) :
    (∫ w, F₁ w + (F₂ w + F₃ w) ∂P) =
      (∫ w, F₁ w ∂P) + ((∫ w, F₂ w ∂P) + (∫ w, F₃ w ∂P)) := by
  calc
    _ = (∫ w, F₁ w ∂P) + (∫ w, F₂ w + F₃ w ∂P) :=
      integral_add h₁ (h₂.add h₃)
    _ = _ := congrArg (fun x : P3 => (∫ w, F₁ w ∂P) + x) (integral_add h₂ h₃)

private theorem fp81v01_insert_pair_integral_identity (P : Measure Ω) (j : Fin 3)
    {A₀ A₁ Z₀ Z₁ : Ω → X}
    (hI0 : Integrable (fun w => Insert j (A₀ w) (Z₀ w) (Z₀ w)) P)
    (hI1 : Integrable (fun w => Insert j (A₁ w) (Z₁ w) (Z₁ w)) P)
    (hIT1 : Integrable (fun w => Insert j (A₀ w - A₁ w) (Z₀ w) (Z₀ w)) P)
    (hIT2 : Integrable (fun w => Insert j (A₁ w) (Z₀ w - Z₁ w) (Z₀ w)) P)
    (hIT3 : Integrable (fun w => Insert j (A₁ w) (Z₁ w) (Z₀ w - Z₁ w)) P) :
    (∫ w, Insert j (A₀ w) (Z₀ w) (Z₀ w) ∂P) -
      (∫ w, Insert j (A₁ w) (Z₁ w) (Z₁ w) ∂P) =
        (∫ w, Insert j (A₀ w - A₁ w) (Z₀ w) (Z₀ w) ∂P) +
          ((∫ w, Insert j (A₁ w) (Z₀ w - Z₁ w) (Z₀ w) ∂P) +
            (∫ w, Insert j (A₁ w) (Z₁ w) (Z₀ w - Z₁ w) ∂P)) := by
  have hdecomp : ∀ w, Insert j (A₀ w) (Z₀ w) (Z₀ w) -
      Insert j (A₁ w) (Z₁ w) (Z₁ w) =
      Insert j (A₀ w - A₁ w) (Z₀ w) (Z₀ w) +
        (Insert j (A₁ w) (Z₀ w - Z₁ w) (Z₀ w) +
          Insert j (A₁ w) (Z₁ w) (Z₀ w - Z₁ w)) := by
    intro w
    simp only [map_sub, sub_apply]
    abel
  calc
    _ = ∫ w, Insert j (A₀ w) (Z₀ w) (Z₀ w) -
        Insert j (A₁ w) (Z₁ w) (Z₁ w) ∂P := (integral_sub hI0 hI1).symm
    _ = ∫ w, Insert j (A₀ w - A₁ w) (Z₀ w) (Z₀ w) +
        (Insert j (A₁ w) (Z₀ w - Z₁ w) (Z₀ w) +
          Insert j (A₁ w) (Z₁ w) (Z₀ w - Z₁ w)) ∂P := by
          apply integral_congr_ae
          filter_upwards with w
          exact hdecomp w
    _ = _ := fp81v01_integral_add3 P hIT1 hIT2 hIT3

private theorem fp81v01_insert_pair_integral_bound (P : Measure Ω) (j : Fin 3)
    {A₀ A₁ : Ω → X} {Z₀ Z₁ : Ω → X}
    (hA₀ : MemLp A₀ 2 P) (hA₁ : MemLp A₁ 2 P)
    (hZ₀ : MemLp Z₀ 4 P) (hZ₁ : MemLp Z₁ 4 P)
    {aΔ a₁ z₀ z₁ δ : ℝ}
    (haΔ : 0 ≤ aΔ) (ha₁ : 0 ≤ a₁) (hz₀ : 0 ≤ z₀) (hz₁ : 0 ≤ z₁) (hδ : 0 ≤ δ)
    (hAΔ : MemLp (fun w => A₀ w - A₁ w) 2 P)
    (hAΔ₀ : eLpNorm (fun w => A₀ w - A₁ w) 2 P ≤ ENNReal.ofReal aΔ)
    (hA₁₀ : eLpNorm A₁ 2 P ≤ ENNReal.ofReal a₁)
    (hZ₀₀ : eLpNorm Z₀ 4 P ≤ ENNReal.ofReal z₀)
    (hZ₁₀ : eLpNorm Z₁ 4 P ≤ ENNReal.ofReal z₁)
    (hZΔ : MemLp (fun w => Z₀ w - Z₁ w) 4 P)
    (hZΔ₀ : eLpNorm (fun w => Z₀ w - Z₁ w) 4 P ≤ ENNReal.ofReal δ) :
    ‖(∫ w, Insert j (A₀ w) (Z₀ w) (Z₀ w) ∂P) -
        (∫ w, Insert j (A₁ w) (Z₁ w) (Z₁ w) ∂P)‖ ≤
      aΔ * z₀ * z₀ + a₁ * δ * z₀ + a₁ * z₁ * δ := by
  have hI0 := Insert_integrable P hA₀ hZ₀ hZ₀ j
  have hI1 := Insert_integrable P hA₁ hZ₁ hZ₁ j
  have hIT1 := Insert_integrable P hAΔ hZ₀ hZ₀ j
  have hIT2 := Insert_integrable P hA₁ hZΔ hZ₀ j
  have hIT3 := Insert_integrable P hA₁ hZ₁ hZΔ j
  have hint := fp81v01_insert_pair_integral_identity P j hI0 hI1 hIT1 hIT2 hIT3
  have hbound1 := fp81v01_insert_integral_bound P j hAΔ hZ₀ hZ₀ haΔ hz₀ hz₀ hAΔ₀ hZ₀₀ hZ₀₀
  have hbound2 := fp81v01_insert_integral_bound P j hA₁ hZΔ hZ₀ ha₁ hδ hz₀ hA₁₀ hZΔ₀ hZ₀₀
  have hbound3 := fp81v01_insert_integral_bound P j hA₁ hZ₁ hZΔ ha₁ hz₁ hδ hA₁₀ hZ₁₀ hZΔ₀
  calc
    ‖(∫ w, Insert j (A₀ w) (Z₀ w) (Z₀ w) ∂P) -
        (∫ w, Insert j (A₁ w) (Z₁ w) (Z₁ w) ∂P)‖
      ≤ ‖∫ w, Insert j (A₀ w - A₁ w) (Z₀ w) (Z₀ w) ∂P‖ +
          (‖∫ w, Insert j (A₁ w) (Z₀ w - Z₁ w) (Z₀ w) ∂P‖ +
            ‖∫ w, Insert j (A₁ w) (Z₁ w) (Z₀ w - Z₁ w) ∂P‖) := by
          rw [hint]
          exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ aΔ * z₀ * z₀ + (a₁ * δ * z₀ + a₁ * z₁ * δ) :=
      add_le_add hbound1 (add_le_add hbound2 hbound3)
    _ = aΔ * z₀ * z₀ + a₁ * δ * z₀ + a₁ * z₁ * δ := by ring

private theorem fp81v01_pair_pair_integral_bound (P : Measure Ω) (j : Fin 3)
    {Q₀ Q₁ : Ω → P2} {Z₀ Z₁ : Ω → X}
    (hQ₀ : MemLp Q₀ 2 P) (hQ₁ : MemLp Q₁ 2 P)
    (hZ₀ : MemLp Z₀ 2 P) (hZ₁ : MemLp Z₁ 2 P)
    {qΔ q₁ z₀ z₁ δ : ℝ}
    (hqΔ : 0 ≤ qΔ) (hq₁ : 0 ≤ q₁) (hz₀ : 0 ≤ z₀) (hz₁ : 0 ≤ z₁) (hδ : 0 ≤ δ)
    (hQΔ : MemLp (fun w => Q₀ w - Q₁ w) 2 P)
    (hQΔ₀ : eLpNorm (fun w => Q₀ w - Q₁ w) 2 P ≤ ENNReal.ofReal qΔ)
    (hQ₁₀ : eLpNorm Q₁ 2 P ≤ ENNReal.ofReal q₁)
    (hZ₀₀ : eLpNorm Z₀ 2 P ≤ ENNReal.ofReal z₀)
    (hZ₁₀ : eLpNorm Z₁ 2 P ≤ ENNReal.ofReal z₁)
    (hZΔ : MemLp (fun w => Z₀ w - Z₁ w) 2 P)
    (hZΔ₀ : eLpNorm (fun w => Z₀ w - Z₁ w) 2 P ≤ ENNReal.ofReal δ) :
    ‖(∫ w, PairInsert j (Q₀ w) (Z₀ w) ∂P) -
        (∫ w, PairInsert j (Q₁ w) (Z₁ w) ∂P)‖ ≤ qΔ * z₀ + q₁ * δ := by
  have hI0 := PairInsert_integrable P hQ₀ hZ₀ j
  have hI1 := PairInsert_integrable P hQ₁ hZ₁ j
  have hIT1 := PairInsert_integrable P hQΔ hZ₀ j
  have hIT2 := PairInsert_integrable P hQ₁ hZΔ j
  have hdecomp : ∀ w, PairInsert j (Q₀ w) (Z₀ w) - PairInsert j (Q₁ w) (Z₁ w) =
      PairInsert j (Q₀ w - Q₁ w) (Z₀ w) + PairInsert j (Q₁ w) (Z₀ w - Z₁ w) := by
    intro w
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  have hint : (∫ w, PairInsert j (Q₀ w) (Z₀ w) ∂P) -
      ∫ w, PairInsert j (Q₁ w) (Z₁ w) ∂P =
      (∫ w, PairInsert j (Q₀ w - Q₁ w) (Z₀ w) ∂P) +
        (∫ w, PairInsert j (Q₁ w) (Z₀ w - Z₁ w) ∂P) := by
    calc
      _ = ∫ w, PairInsert j (Q₀ w) (Z₀ w) - PairInsert j (Q₁ w) (Z₁ w) ∂P :=
        (integral_sub hI0 hI1).symm
      _ = ∫ w, PairInsert j (Q₀ w - Q₁ w) (Z₀ w) + PairInsert j (Q₁ w) (Z₀ w - Z₁ w) ∂P := by
        apply integral_congr_ae
        filter_upwards with w
        exact hdecomp w
      _ = (∫ w, PairInsert j (Q₀ w - Q₁ w) (Z₀ w) ∂P) +
          ∫ w, PairInsert j (Q₁ w) (Z₀ w - Z₁ w) ∂P := integral_add hIT1 hIT2
  have hbound1 := fp81v01_pairinsert_integral_bound P j hQΔ hZ₀ hqΔ hz₀ hQΔ₀ hZ₀₀
  have hbound2 := fp81v01_pairinsert_integral_bound P j hQ₁ hZΔ hq₁ hδ hQ₁₀ hZΔ₀
  calc
    ‖(∫ w, PairInsert j (Q₀ w) (Z₀ w) ∂P) -
        (∫ w, PairInsert j (Q₁ w) (Z₁ w) ∂P)‖
      ≤ ‖∫ w, PairInsert j (Q₀ w - Q₁ w) (Z₀ w) ∂P‖ +
          ‖∫ w, PairInsert j (Q₁ w) (Z₀ w - Z₁ w) ∂P‖ := by
        rw [hint]
        exact norm_add_le _ _
    _ ≤ qΔ * z₀ + q₁ * δ := add_le_add hbound1 hbound2

private theorem fp81v01_sum_cross_sub {ι G : Type*} [NormedAddCommGroup G]
    (s : Finset ι) (f₀w f₀v f₁w f₁v : ι → G) :
    (s.sum f₀w - s.sum f₁w) - (s.sum f₀v - s.sum f₁v) =
      s.sum (fun i => (f₀w i - f₀v i) - (f₁w i - f₁v i)) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  abel

private theorem fp81v01_age (c u t : ℝ) : 0 ≤ HRS.MS.S111K2.s111k2_age c u t :=
  (Real.exp_pos _).le

private theorem fp81v01_age_integrable_local (H : ℝ) (c u : ℝ) :
    IntegrableOn (fun t => HRS.MS.S111K2.s111k2_age c u t) (Icc 0 H) := by
  have hc : Continuous fun t => HRS.MS.S111K2.s111k2_age c u t := by
    unfold HRS.MS.S111K2.s111k2_age
    fun_prop
  exact hc.continuousOn.integrableOn_Icc

private theorem fp81v01_age_sq_integrable_local (H : ℝ) (c u : ℝ) :
    IntegrableOn (fun t => HRS.MS.S111K2.s111k2_age c u t ^ 2) (Icc 0 H) := by
  have hc : Continuous fun t => HRS.MS.S111K2.s111k2_age c u t := by
    unfold HRS.MS.S111K2.s111k2_age
    fun_prop
  exact (hc.pow 2).continuousOn.integrableOn_Icc

private theorem fp81v01_absorb_age
    (hu : 0 ≤ u) (hT : 0 < T) {κ : ℝ} (hκ : 0 < κ)
    {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) (hw : w ≤ u + T)
    (g : ℝ → ℝ) (hg : IntegrableOn g (Icc v w))
    (hge : IntegrableOn (fun t => g t * Real.exp (-κ * t)) (Icc v w))
    (hg0 : ∀ t ∈ Icc v w, 0 ≤ g t) :
    Real.exp (-κ * u) * ∫ t in Icc v w, g t ≤
      Real.exp (κ * T) * ∫ t in Icc v w, g t * Real.exp (-κ * t) := by
  have hexp : ∀ t ∈ Icc v w, Real.exp (-κ * u) ≤ Real.exp (κ * T) * Real.exp (-κ * t) := by
    intro t ht
    have htu : t ≤ u + T := ht.2.trans hw
    have he : -κ * u ≤ κ * T - κ * t := by
      nlinarith [mul_le_mul_of_nonneg_left htu hκ.le]
    calc Real.exp (-κ * u) ≤ Real.exp (κ * T - κ * t) := Real.exp_le_exp.mpr he
      _ = Real.exp (κ * T) * Real.exp (-κ * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hmono := setIntegral_mono_on (hg.mul_const (Real.exp (-κ * u)))
    (hge.const_mul (Real.exp (κ * T))) measurableSet_Icc (fun t ht => by
      calc g t * Real.exp (-κ * u)
          ≤ g t * (Real.exp (κ * T) * Real.exp (-κ * t)) :=
            mul_le_mul_of_nonneg_left (hexp t ht) (hg0 t ht)
        _ = Real.exp (κ * T) * (g t * Real.exp (-κ * t)) := by ring)
  calc Real.exp (-κ * u) * ∫ t in Icc v w, g t
      = ∫ t in Icc v w, g t * Real.exp (-κ * u) := by
          rw [integral_mul_const]
          ring
    _ ≤ ∫ t in Icc v w, Real.exp (κ * T) * (g t * Real.exp (-κ * t)) := hmono
    _ = Real.exp (κ * T) * ∫ t in Icc v w, g t * Real.exp (-κ * t) := by
          rw [integral_const_mul]

/-- Paired drift and covariance sources have finite variation on the observation window.
The displayed constants retain all terms in the tensor difference expansions. -/
theorem paired_variation
    (hu : 0 ≤ u) (hT : 0 < T) (hc : 0 < c) (hB : 0 ≤ B)
    (κ R M : ℝ) (hκ : 0 < κ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (O : r26t6_IntervalOperators E C T u c B)
    (qL qQ : Fin 2 → ℝ × Ω → r26t6_Coeff)
    (Z : Fin 2 → Ω → X)
    (hctl : ∀ i, RandomIntervalControl P O (qL i) (fun _ => R) ∧
      RandomIntervalControl P O (qQ i) (fun _ => R))
    (hΔL : RandomIntervalControl P O (qL 0 - qL 1)
      (fun t => R * Real.exp (-κ * t)))
    (hΔQ : RandomIntervalControl P O (qQ 0 - qQ 1)
      (fun t => R * Real.exp (-κ * t)))
    (hqL : MemLp (qL 1) 2 ((volume.restrict (Icc 0 (u + T))).prod P))
    (hqQ : MemLp (qQ 1) 2 ((volume.restrict (Icc 0 (u + T))).prod P))
    (hZ : ∀ i, MemLp (Z i) 4 P ∧ eLpNorm (Z i) 4 P ≤ ENNReal.ofReal M)
    (hΔZ : MemLp (fun w => Z 0 w - Z 1 w) 4 P ∧
      eLpNorm (fun w => Z 0 w - Z 1 w) 4 P ≤
        ENNReal.ofReal (M * Real.exp (-κ * u))) :
    let BD := 3 * B * R * M ^ 2 * (1 + 2 * Real.exp (κ * T))
    let BJ := 3 * B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R * M *
      (1 + Real.exp (κ * T))
    eVariationOn
      (fun v => D P O (qQ 0) (Z 0) v - D P O (qQ 1) (Z 1) v)
      (Icc 0 (u + T)) ≤ ENNReal.ofReal
        (BD * ∫ t in Icc 0 (u + T),
          Real.exp (-c * max (u - t) 0) * Real.exp (-κ * t)) ∧
    eVariationOn
      (fun v => J P O (qL 0) (Z 0) v - J P O (qL 1) (Z 1) v)
      (Icc 0 (u + T)) ≤ ENNReal.ofReal
        (BJ * ∫ t in Icc 0 (u + T),
          Real.exp (-2 * c * max (u - t) 0) * Real.exp (-κ * t)) := by
  let H := u + T
  have hH : 0 ≤ H := by dsimp [H]; linarith
  have hZ₂ : ∀ i, MemLp (Z i) 2 P := fun i => (hZ i).1.mono_exponent (by norm_num)
  have hZ₂bound : ∀ i, eLpNorm (Z i) 2 P ≤ ENNReal.ofReal M := by
    intro i
    exact (eLpNorm_le_eLpNorm_of_exponent_le (μ := P) (f := Z i)
      (p := (2 : ℝ≥0∞)) (q := 4) (by norm_num)).trans (hZ i).2
  have hΔZ₂ : MemLp (fun w => Z 0 w - Z 1 w) 2 P := hΔZ.1.mono_exponent (by norm_num)
  have hΔZ₂bound : eLpNorm (fun w => Z 0 w - Z 1 w) 2 P ≤
      ENNReal.ofReal (M * Real.exp (-κ * u)) := by
    exact (eLpNorm_le_eLpNorm_of_exponent_le (μ := P)
      (f := fun w => Z 0 w - Z 1 w) (p := (2 : ℝ≥0∞)) (q := 4) (by norm_num)).trans hΔZ.2
  have hpairedQ := RandomIntervalControl.paired_increments (hctl 0).2 hΔQ hqQ
  have hpairedL := RandomIntervalControl.paired_increments (hctl 0).1 hΔL hqL
  have hDinc : ∀ v w, 0 ≤ v → v ≤ w → w ≤ H →
      ‖(D P O (qQ 0) (Z 0) w - D P O (qQ 1) (Z 1) w) -
        (D P O (qQ 0) (Z 0) v - D P O (qQ 1) (Z 1) v)‖ ≤
      ∫ t in Icc v w,
        (3 * B * R * M ^ 2 * (1 + 2 * Real.exp (κ * T))) *
          HRS.MS.S111K2.s111k2_age c u t * Real.exp (-κ * t) := by
    intro v w hv hvw hw
    have hw' : w ≤ u + T := by simpa [H] using hw
    have hPairRaw := (hpairedQ v w hv hvw hw').1
    have hPairBound : eLpNorm (fun z =>
        (r26t6_randomDrift O (qQ 0) w z - r26t6_randomDrift O (qQ 1) w z) -
          (r26t6_randomDrift O (qQ 0) v z - r26t6_randomDrift O (qQ 1) v z)) 2 P ≤
        ENNReal.ofReal (B * R * ∫ t in Icc v w,
          HRS.MS.S111K2.s111k2_age c u t * Real.exp (-κ * t)) := by
      have hEq : (∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t *
          (fun t => R * Real.exp (-κ * t)) t) = R * ∫ t in Icc v w,
            HRS.MS.S111K2.s111k2_age c u t * Real.exp (-κ * t) := by
        have hfun : (fun t => HRS.MS.S111K2.s111k2_age c u t *
            (R * Real.exp (-κ * t))) = fun t => R *
              (HRS.MS.S111K2.s111k2_age c u t * Real.exp (-κ * t)) := by
          funext t
          ring
        rw [integral_congr_ae (ae_of_all _ fun t => congrFun hfun t), integral_const_mul]
      calc
        _ ≤ ENNReal.ofReal (B * (R * ∫ t in Icc v w,
              HRS.MS.S111K2.s111k2_age c u t * Real.exp (-κ * t))) := by
          rw [← hEq]
          exact hPairRaw
        _ = _ := congrArg ENNReal.ofReal (by ring)
    have hA0v := (hctl 0).2.moments v ⟨hv, hvw.trans hw⟩
    have hA0w := (hctl 0).2.moments w ⟨hv.trans hvw, hw⟩
    have hA1v := (hctl 1).2.moments v ⟨hv, hvw.trans hw⟩
    have hA1w := (hctl 1).2.moments w ⟨hv.trans hvw, hw⟩
    let A₀ : Ω → X := fun z => r26t6_randomDrift O (qQ 0) w z - r26t6_randomDrift O (qQ 0) v z
    let A₁ : Ω → X := fun z => r26t6_randomDrift O (qQ 1) w z - r26t6_randomDrift O (qQ 1) v z
    have hA₀ : MemLp A₀ 2 P := hA0w.1.sub hA0v.1
    have hA₁ : MemLp A₁ 2 P := hA1w.1.sub hA1v.1
    have hAΔ : MemLp (fun z => A₀ z - A₁ z) 2 P := hA₀.sub hA₁
    have hAΔbound : eLpNorm (fun z => A₀ z - A₁ z) 2 P ≤
        ENNReal.ofReal (B * R * ∫ t in Icc v w,
          HRS.MS.S111K2.s111k2_age c u t * Real.exp (-κ * t)) := by
      have hEq : (fun z => A₀ z - A₁ z) = fun z =>
          (r26t6_randomDrift O (qQ 0) w z - r26t6_randomDrift O (qQ 1) w z) -
            (r26t6_randomDrift O (qQ 0) v z - r26t6_randomDrift O (qQ 1) v z) := by
        funext z
        simp only [A₀, A₁]
        abel
      calc eLpNorm (fun z => A₀ z - A₁ z) 2 P = eLpNorm _ 2 P :=
            eLpNorm_congr_ae (Eventually.of_forall fun z => congrFun hEq z)
        _ ≤ _ := hPairBound
    have hA₁boundRaw := ((hctl 1).2.increments v w hv hvw hw').1
    have hA₁bound : eLpNorm A₁ 2 P ≤ ENNReal.ofReal
        (B * R * ∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t) := by
      have hEq : (∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t * (fun _ : ℝ => R) t) =
          R * ∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t := by
        rw [integral_mul_const]
        ring
      have hraw := hA₁boundRaw
      rw [hEq] at hraw
      calc
        eLpNorm A₁ 2 P = eLpNorm (fun z =>
            r26t6_randomDrift O (qQ 1) w z - r26t6_randomDrift O (qQ 1) v z) 2 P := by
              apply eLpNorm_congr_ae
              exact Eventually.of_forall (fun z => rfl)
        _ ≤ ENNReal.ofReal (B * (R * ∫ t in Icc v w,
              HRS.MS.S111K2.s111k2_age c u t)) := hraw
        _ = _ := congrArg ENNReal.ofReal (by ring)
    have hδ : MemLp (fun z => Z 0 z - Z 1 z) 4 P := hΔZ.1
    have hsub : Icc v w ⊆ Icc 0 H := by
      intro t ht
      exact ⟨hv.trans ht.1, ht.2.trans (by simpa [H] using hw')⟩
    have hAgeI := (fp81v01_age_integrable_local H c u).mono_set hsub
    have hAgeExpCont : Continuous fun t =>
        HRS.MS.S111K2.s111k2_age c u t * Real.exp (-κ * t) := by
      unfold HRS.MS.S111K2.s111k2_age
      fun_prop
    have hAgeExpI : IntegrableOn
        (fun t => HRS.MS.S111K2.s111k2_age c u t * Real.exp (-κ * t)) (Icc 0 H) :=
      hAgeExpCont.continuousOn.integrableOn_Icc
    have hAbsorb := fp81v01_absorb_age hu hT hκ hv hvw hw'
      (fun t => HRS.MS.S111K2.s111k2_age c u t) hAgeI (hAgeExpI.mono_set hsub)
      (fun t ht => fp81v01_age c u t)
    have hterm : ∀ j : Fin 3,
        ‖(∫ z, Insert j (r26t6_randomDrift O (qQ 0) w z - r26t6_randomDrift O (qQ 0) v z)
            (Z 0 z) (Z 0 z) ∂P) -
          (∫ z, Insert j (r26t6_randomDrift O (qQ 1) w z - r26t6_randomDrift O (qQ 1) v z)
            (Z 1 z) (Z 1 z) ∂P)‖ ≤
          B * R * M ^ 2 * (1 + 2 * Real.exp (κ * T)) *
            ∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t * Real.exp (-κ * t) := by
      intro j
      have hInt0 : 0 ≤ ∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t :=
        setIntegral_nonneg measurableSet_Icc (fun t _ => fp81v01_age c u t)
      have hIntE0 : 0 ≤ ∫ t in Icc v w,
          HRS.MS.S111K2.s111k2_age c u t * Real.exp (-κ * t) :=
        setIntegral_nonneg measurableSet_Icc (fun t _ => mul_nonneg (fp81v01_age c u t) (Real.exp_pos _).le)
      have hraw := fp81v01_insert_pair_integral_bound P j hA₀ hA₁ (hZ 0).1 (hZ 1).1
        (aΔ := B * R * ∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t * Real.exp (-κ * t))
        (a₁ := B * R * ∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t)
        (z₀ := M) (z₁ := M) (δ := M * Real.exp (-κ * u))
        (mul_nonneg (mul_nonneg hB hR) hIntE0) (mul_nonneg (mul_nonneg hB hR) hInt0)
        hM hM (mul_nonneg hM (Real.exp_pos _).le)
        hAΔ hAΔbound hA₁bound (hZ 0).2 (hZ 1).2 hδ hΔZ.2
      have hRawEq :
          (B * R * ∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t * Real.exp (-κ * t)) * M * M +
          (B * R * ∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t) *
            (M * Real.exp (-κ * u)) * M +
          (B * R * ∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t) * M *
            (M * Real.exp (-κ * u)) ≤
          B * R * M ^ 2 * (1 + 2 * Real.exp (κ * T)) *
            ∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t * Real.exp (-κ * t) := by
        have hmul := mul_le_mul_of_nonneg_left hAbsorb
          (mul_nonneg (mul_nonneg hB hR) (sq_nonneg M))
        nlinarith [hmul]
      exact le_trans hraw hRawEq
    unfold D
    let f₀w : Fin 3 → P3 := fun j =>
      ∫ z, Insert j (r26t6_randomDrift O (qQ 0) w z) (Z 0 z) (Z 0 z) ∂P
    let f₀v : Fin 3 → P3 := fun j =>
      ∫ z, Insert j (r26t6_randomDrift O (qQ 0) v z) (Z 0 z) (Z 0 z) ∂P
    let f₁w : Fin 3 → P3 := fun j =>
      ∫ z, Insert j (r26t6_randomDrift O (qQ 1) w z) (Z 1 z) (Z 1 z) ∂P
    let f₁v : Fin 3 → P3 := fun j =>
      ∫ z, Insert j (r26t6_randomDrift O (qQ 1) v z) (Z 1 z) (Z 1 z) ∂P
    have hsum : ‖Finset.univ.sum (fun j : Fin 3 =>
        (f₀w j - f₀v j) - (f₁w j - f₁v j))‖ ≤
        Finset.univ.sum (fun _ : Fin 3 => B * R * M ^ 2 * (1 + 2 * Real.exp (κ * T)) *
          ∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t * Real.exp (-κ * t)) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      have hI00w := Insert_integrable P (hA0w).1 (hZ 0).1 (hZ 0).1 j
      have hI00v := Insert_integrable P (hA0v).1 (hZ 0).1 (hZ 0).1 j
      have hI11w := Insert_integrable P (hA1w).1 (hZ 1).1 (hZ 1).1 j
      have hI11v := Insert_integrable P (hA1v).1 (hZ 1).1 (hZ 1).1 j
      have heq0 := fp81v01_insert_integral_sub P j hI00w hI00v
      have heq1 := fp81v01_insert_integral_sub P j hI11w hI11v
      calc
        ‖(f₀w j - f₀v j) - (f₁w j - f₁v j)‖ =
            ‖(∫ z, Insert j (r26t6_randomDrift O (qQ 0) w z -
                  r26t6_randomDrift O (qQ 0) v z) (Z 0 z) (Z 0 z) ∂P) -
              (∫ z, Insert j (r26t6_randomDrift O (qQ 1) w z -
                  r26t6_randomDrift O (qQ 1) v z) (Z 1 z) (Z 1 z) ∂P)‖ :=
                congrArg (fun x : P3 => ‖x‖) (congrArg₂ (fun x y : P3 => x - y) heq0 heq1)
        _ ≤ _ := hterm j
    have hcross := fp81v01_sum_cross_sub Finset.univ f₀w f₀v f₁w f₁v
    change ‖(Finset.univ.sum f₀w - Finset.univ.sum f₁w) -
        (Finset.univ.sum f₀v - Finset.univ.sum f₁v)‖ ≤ _
    calc
      _ = ‖Finset.univ.sum (fun j : Fin 3 =>
          (f₀w j - f₀v j) - (f₁w j - f₁v j))‖ := congrArg (fun x : P3 => ‖x‖) hcross
      _ ≤ _ := hsum
      _ = ∫ t in Icc v w,
          (3 * B * R * M ^ 2 * (1 + 2 * Real.exp (κ * T))) *
            HRS.MS.S111K2.s111k2_age c u t * Real.exp (-κ * t) := by
        rw [Finset.sum_const, Finset.card_fin]
        simp only [nsmul_eq_mul]
        calc
          _ = (3 * (B * R * M ^ 2 * (1 + 2 * Real.exp (κ * T)))) *
                (∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t * Real.exp (-κ * t)) := by ring
          _ = ∫ t in Icc v w,
                (3 * B * R * M ^ 2 * (1 + 2 * Real.exp (κ * T))) *
                  (HRS.MS.S111K2.s111k2_age c u t * Real.exp (-κ * t)) := by
                rw [integral_const_mul]
                ring
          _ = ∫ t in Icc v w,
                (3 * B * R * M ^ 2 * (1 + 2 * Real.exp (κ * T))) *
                  HRS.MS.S111K2.s111k2_age c u t * Real.exp (-κ * t) := by
                apply setIntegral_congr_fun measurableSet_Icc
                intro t ht
                ring
  have hJinc : ∀ v w, 0 ≤ v → v ≤ w → w ≤ H →
      ‖(J P O (qL 0) (Z 0) w - J P O (qL 1) (Z 1) w) -
        (J P O (qL 0) (Z 0) v - J P O (qL 1) (Z 1) v)‖ ≤
      ∫ t in Icc v w,
        (3 * B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R * M *
          (1 + Real.exp (κ * T))) *
          HRS.MS.S111K2.s111k2_age c u t ^ 2 * Real.exp (-κ * t) := by
    -- The covariance expansion has a paired response term and one observation-difference term.
    intro v w hv hvw hw
    have hw' : w ≤ u + T := by simpa [H] using hw
    have hPairRaw := (hpairedL v w hv hvw hw').2
    have hPairBound : eLpNorm (fun z =>
        (r26t6_randomCovariance O (qL 0) w z - r26t6_randomCovariance O (qL 1) w z) -
          (r26t6_randomCovariance O (qL 0) v z - r26t6_randomCovariance O (qL 1) v z)) 2 P ≤
        ENNReal.ofReal (B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R *
          ∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t ^ 2 * Real.exp (-κ * t)) := by
      have hEq : (∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t ^ 2 *
          (fun t => R * Real.exp (-κ * t)) t) = R * ∫ t in Icc v w,
            HRS.MS.S111K2.s111k2_age c u t ^ 2 * Real.exp (-κ * t) := by
        have hfun : (fun t => HRS.MS.S111K2.s111k2_age c u t ^ 2 *
            (R * Real.exp (-κ * t))) = fun t => R *
              (HRS.MS.S111K2.s111k2_age c u t ^ 2 * Real.exp (-κ * t)) := by
          funext t
          ring
        rw [integral_congr_ae (ae_of_all _ fun t => congrFun hfun t), integral_const_mul]
      calc
        _ ≤ ENNReal.ofReal (B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| *
              (R * ∫ t in Icc v w,
                HRS.MS.S111K2.s111k2_age c u t ^ 2 * Real.exp (-κ * t))) := by
          rw [← hEq]
          exact hPairRaw
        _ = _ := congrArg ENNReal.ofReal (by ring)
    have hQ0v := (hctl 0).1.moments v ⟨hv, hvw.trans hw⟩
    have hQ0w := (hctl 0).1.moments w ⟨hv.trans hvw, hw⟩
    have hQ1v := (hctl 1).1.moments v ⟨hv, hvw.trans hw⟩
    have hQ1w := (hctl 1).1.moments w ⟨hv.trans hvw, hw⟩
    let Q₀ : Ω → P2 := fun z => r26t6_randomCovariance O (qL 0) w z - r26t6_randomCovariance O (qL 0) v z
    let Q₁ : Ω → P2 := fun z => r26t6_randomCovariance O (qL 1) w z - r26t6_randomCovariance O (qL 1) v z
    have hQ₀ : MemLp Q₀ 2 P := hQ0w.2.sub hQ0v.2
    have hQ₁ : MemLp Q₁ 2 P := hQ1w.2.sub hQ1v.2
    have hQΔ : MemLp (fun z => Q₀ z - Q₁ z) 2 P := hQ₀.sub hQ₁
    have hQΔbound : eLpNorm (fun z => Q₀ z - Q₁ z) 2 P ≤
        ENNReal.ofReal (B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R *
          ∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t ^ 2 * Real.exp (-κ * t)) := by
      have hEq : (fun z => Q₀ z - Q₁ z) = fun z =>
          (r26t6_randomCovariance O (qL 0) w z - r26t6_randomCovariance O (qL 1) w z) -
            (r26t6_randomCovariance O (qL 0) v z - r26t6_randomCovariance O (qL 1) v z) := by
        funext z
        simp only [Q₀, Q₁]
        abel
      calc eLpNorm (fun z => Q₀ z - Q₁ z) 2 P = eLpNorm _ 2 P :=
            eLpNorm_congr_ae (Eventually.of_forall fun z => congrFun hEq z)
        _ ≤ _ := hPairBound
    have hQ₁boundRaw := ((hctl 1).1.increments v w hv hvw hw').2
    have hQ₁bound : eLpNorm Q₁ 2 P ≤ ENNReal.ofReal
        (B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R *
          ∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t ^ 2) := by
      have hEq : (∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t ^ 2 * (fun _ : ℝ => R) t) =
          R * ∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t ^ 2 := by
        rw [integral_mul_const]
        ring
      have hraw := hQ₁boundRaw
      rw [hEq] at hraw
      calc
        eLpNorm Q₁ 2 P = eLpNorm (fun z =>
            r26t6_randomCovariance O (qL 1) w z -
              r26t6_randomCovariance O (qL 1) v z) 2 P := by
              apply eLpNorm_congr_ae
              exact Eventually.of_forall (fun z => rfl)
        _ ≤ ENNReal.ofReal (B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| *
              (R * ∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t ^ 2)) := hraw
        _ = _ := congrArg ENNReal.ofReal (by ring)
    have hΔZ₂bound' : eLpNorm (fun z => Z 0 z - Z 1 z) 2 P ≤
        ENNReal.ofReal (M * Real.exp (-κ * u)) := hΔZ₂bound
    have hsub : Icc v w ⊆ Icc 0 H := by
      intro t ht
      exact ⟨hv.trans ht.1, ht.2.trans (by simpa [H] using hw')⟩
    have hAgeSqCont : Continuous fun t => HRS.MS.S111K2.s111k2_age c u t ^ 2 := by
      have hAgeCont : Continuous fun t => HRS.MS.S111K2.s111k2_age c u t := by
        unfold HRS.MS.S111K2.s111k2_age
        fun_prop
      exact hAgeCont.pow 2
    have hAgeSqI : IntegrableOn
        (fun t => HRS.MS.S111K2.s111k2_age c u t ^ 2) (Icc 0 H) :=
      hAgeSqCont.continuousOn.integrableOn_Icc
    have hAgeSqExpCont : Continuous fun t =>
        HRS.MS.S111K2.s111k2_age c u t ^ 2 * Real.exp (-κ * t) := by
      unfold HRS.MS.S111K2.s111k2_age
      fun_prop
    have hAgeSqExpI : IntegrableOn
        (fun t => HRS.MS.S111K2.s111k2_age c u t ^ 2 * Real.exp (-κ * t)) (Icc 0 H) :=
      hAgeSqExpCont.continuousOn.integrableOn_Icc
    have hAbsorb := fp81v01_absorb_age hu hT hκ hv hvw hw'
      (fun t => HRS.MS.S111K2.s111k2_age c u t ^ 2)
      (hAgeSqI.mono_set hsub) (hAgeSqExpI.mono_set hsub)
      (fun t ht => sq_nonneg _)
    have hterm : ∀ j : Fin 3,
        ‖(∫ z, PairInsert j (r26t6_randomCovariance O (qL 0) w z -
            r26t6_randomCovariance O (qL 0) v z) (Z 0 z) ∂P) -
          (∫ z, PairInsert j (r26t6_randomCovariance O (qL 1) w z -
            r26t6_randomCovariance O (qL 1) v z) (Z 1 z) ∂P)‖ ≤
          B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R * M *
            (1 + Real.exp (κ * T)) *
              ∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t ^ 2 * Real.exp (-κ * t) := by
      intro j
      have hInt0 : 0 ≤ ∫ t in Icc v w,
          HRS.MS.S111K2.s111k2_age c u t ^ 2 :=
        setIntegral_nonneg measurableSet_Icc (fun t _ => sq_nonneg _)
      have hIntE0 : 0 ≤ ∫ t in Icc v w,
          HRS.MS.S111K2.s111k2_age c u t ^ 2 * Real.exp (-κ * t) :=
        setIntegral_nonneg measurableSet_Icc (fun t _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
      have hraw := fp81v01_pair_pair_integral_bound P j hQ₀ hQ₁ (hZ₂ 0) (hZ₂ 1)
        (qΔ := B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R *
          ∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t ^ 2 * Real.exp (-κ * t))
        (q₁ := B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R *
          ∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t ^ 2)
        (z₀ := M) (z₁ := M) (δ := M * Real.exp (-κ * u))
        (mul_nonneg (mul_nonneg
          (mul_nonneg hB (abs_nonneg (2 * (r26t6_thermalCoeff d s a β ρ).ν))) hR) hIntE0)
        (mul_nonneg (mul_nonneg
          (mul_nonneg hB (abs_nonneg (2 * (r26t6_thermalCoeff d s a β ρ).ν))) hR) hInt0)
        hM hM (mul_nonneg hM (Real.exp_pos _).le)
        hQΔ hQΔbound hQ₁bound (hZ₂bound 0) (hZ₂bound 1) hΔZ₂ hΔZ₂bound'
      have hmul := mul_le_mul_of_nonneg_left hAbsorb
        (mul_nonneg (mul_nonneg
          (mul_nonneg hB (abs_nonneg (2 * (r26t6_thermalCoeff d s a β ρ).ν))) hR) hM)
      have hRawEq :
          (B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R *
            ∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t ^ 2 * Real.exp (-κ * t)) * M +
          (B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R *
            ∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t ^ 2) *
              (M * Real.exp (-κ * u)) ≤
          B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R * M *
            (1 + Real.exp (κ * T)) *
              ∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t ^ 2 * Real.exp (-κ * t) := by
        nlinarith [hmul]
      exact le_trans hraw hRawEq
    unfold J
    let f₀w : Fin 3 → P3 := fun j =>
      ∫ z, PairInsert j (r26t6_randomCovariance O (qL 0) w z) (Z 0 z) ∂P
    let f₀v : Fin 3 → P3 := fun j =>
      ∫ z, PairInsert j (r26t6_randomCovariance O (qL 0) v z) (Z 0 z) ∂P
    let f₁w : Fin 3 → P3 := fun j =>
      ∫ z, PairInsert j (r26t6_randomCovariance O (qL 1) w z) (Z 1 z) ∂P
    let f₁v : Fin 3 → P3 := fun j =>
      ∫ z, PairInsert j (r26t6_randomCovariance O (qL 1) v z) (Z 1 z) ∂P
    have hsum : ‖Finset.univ.sum (fun j : Fin 3 =>
        (f₀w j - f₀v j) - (f₁w j - f₁v j))‖ ≤
        Finset.univ.sum (fun _ : Fin 3 =>
          B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R * M *
            (1 + Real.exp (κ * T)) *
              ∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t ^ 2 * Real.exp (-κ * t)) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      have hI00w := PairInsert_integrable P hQ0w.2 (hZ₂ 0) j
      have hI00v := PairInsert_integrable P hQ0v.2 (hZ₂ 0) j
      have hI11w := PairInsert_integrable P hQ1w.2 (hZ₂ 1) j
      have hI11v := PairInsert_integrable P hQ1v.2 (hZ₂ 1) j
      have heq0 := fp81v01_pairinsert_integral_sub P j hI00w hI00v
      have heq1 := fp81v01_pairinsert_integral_sub P j hI11w hI11v
      calc
        ‖(f₀w j - f₀v j) - (f₁w j - f₁v j)‖ =
            ‖(∫ z, PairInsert j (r26t6_randomCovariance O (qL 0) w z -
                  r26t6_randomCovariance O (qL 0) v z) (Z 0 z) ∂P) -
              (∫ z, PairInsert j (r26t6_randomCovariance O (qL 1) w z -
                  r26t6_randomCovariance O (qL 1) v z) (Z 1 z) ∂P)‖ :=
                congrArg (fun x : P3 => ‖x‖) (congrArg₂ (fun x y : P3 => x - y) heq0 heq1)
        _ ≤ _ := hterm j
    have hcross := fp81v01_sum_cross_sub Finset.univ f₀w f₀v f₁w f₁v
    change ‖(Finset.univ.sum f₀w - Finset.univ.sum f₁w) -
        (Finset.univ.sum f₀v - Finset.univ.sum f₁v)‖ ≤ _
    calc
      _ = ‖Finset.univ.sum (fun j : Fin 3 =>
          (f₀w j - f₀v j) - (f₁w j - f₁v j))‖ := congrArg (fun x : P3 => ‖x‖) hcross
      _ ≤ _ := hsum
      _ = ∫ t in Icc v w,
          (3 * B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R * M *
            (1 + Real.exp (κ * T))) *
            HRS.MS.S111K2.s111k2_age c u t ^ 2 * Real.exp (-κ * t) := by
        rw [Finset.sum_const, Finset.card_fin]
        simp only [nsmul_eq_mul]
        calc
          _ = (3 * (B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R * M *
                (1 + Real.exp (κ * T)))) *
                (∫ t in Icc v w,
                  HRS.MS.S111K2.s111k2_age c u t ^ 2 * Real.exp (-κ * t)) := by ring
          _ = ∫ t in Icc v w,
                (3 * B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R * M *
                  (1 + Real.exp (κ * T))) *
                  (HRS.MS.S111K2.s111k2_age c u t ^ 2 * Real.exp (-κ * t)) := by
                rw [integral_const_mul]
                ring
          _ = ∫ t in Icc v w,
                (3 * B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R * M *
                  (1 + Real.exp (κ * T))) *
                  HRS.MS.S111K2.s111k2_age c u t ^ 2 * Real.exp (-κ * t) := by
                apply setIntegral_congr_fun measurableSet_Icc
                intro t ht
                ring
  have hDmajor : IntegrableOn (fun t =>
      (3 * B * R * M ^ 2 * (1 + 2 * Real.exp (κ * T))) *
        HRS.MS.S111K2.s111k2_age c u t * Real.exp (-κ * t)) (Icc 0 H) := by
    have hcAge : Continuous fun t => HRS.MS.S111K2.s111k2_age c u t * Real.exp (-κ * t) := by
      unfold HRS.MS.S111K2.s111k2_age
      fun_prop
    have hbase : IntegrableOn
        (fun t => (3 * B * R * M ^ 2 * (1 + 2 * Real.exp (κ * T))) *
          (HRS.MS.S111K2.s111k2_age c u t * Real.exp (-κ * t))) (Icc 0 H) :=
      (hcAge.continuousOn.integrableOn_Icc).const_mul
        (3 * B * R * M ^ 2 * (1 + 2 * Real.exp (κ * T)))
    exact hbase.congr (ae_of_all _ fun t => by ring)
  have hJmajor : IntegrableOn (fun t =>
      (3 * B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R * M *
        (1 + Real.exp (κ * T))) *
        HRS.MS.S111K2.s111k2_age c u t ^ 2 * Real.exp (-κ * t)) (Icc 0 H) := by
    have hcAge : Continuous fun t => HRS.MS.S111K2.s111k2_age c u t ^ 2 * Real.exp (-κ * t) := by
      unfold HRS.MS.S111K2.s111k2_age
      fun_prop
    have hbase : IntegrableOn
        (fun t => (3 * B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R * M *
          (1 + Real.exp (κ * T))) *
          (HRS.MS.S111K2.s111k2_age c u t ^ 2 * Real.exp (-κ * t))) (Icc 0 H) :=
      (hcAge.continuousOn.integrableOn_Icc).const_mul
        (3 * B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R * M *
          (1 + Real.exp (κ * T)))
    exact hbase.congr (ae_of_all _ fun t => by ring)
  have hDmajor0 : ∀ t ∈ Icc 0 H, 0 ≤
      (3 * B * R * M ^ 2 * (1 + 2 * Real.exp (κ * T))) *
        HRS.MS.S111K2.s111k2_age c u t * Real.exp (-κ * t) := by
    intro t ht
    have hAge := fp81v01_age c u t
    positivity
  have hJmajor0 : ∀ t ∈ Icc 0 H, 0 ≤
      (3 * B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R * M *
        (1 + Real.exp (κ * T))) *
        HRS.MS.S111K2.s111k2_age c u t ^ 2 * Real.exp (-κ * t) := by
    intro t ht
    have hAge := fp81v01_age c u t
    positivity
  have hDreg := fp81v01_regular_of_majorant
    (fun v => D P O (qQ 0) (Z 0) v - D P O (qQ 1) (Z 1) v) H hH
    (fun t => (3 * B * R * M ^ 2 * (1 + 2 * Real.exp (κ * T))) *
      HRS.MS.S111K2.s111k2_age c u t * Real.exp (-κ * t)) hDmajor hDmajor0 hDinc
  have hJreg := fp81v01_regular_of_majorant
    (fun v => J P O (qL 0) (Z 0) v - J P O (qL 1) (Z 1) v) H hH
    (fun t => (3 * B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R * M *
      (1 + Real.exp (κ * T))) * HRS.MS.S111K2.s111k2_age c u t ^ 2 * Real.exp (-κ * t))
    hJmajor hJmajor0 hJinc
  have hDscalar :
      ∫ t in Icc 0 (u + T),
        (3 * B * R * M ^ 2 * (1 + 2 * Real.exp (κ * T))) *
          HRS.MS.S111K2.s111k2_age c u t * Real.exp (-κ * t) =
        (3 * B * R * M ^ 2 * (1 + 2 * Real.exp (κ * T))) *
          ∫ t in Icc 0 (u + T),
            Real.exp (-c * max (u - t) 0) * Real.exp (-κ * t) := by
    calc
      _ = ∫ t in Icc 0 (u + T),
            (3 * B * R * M ^ 2 * (1 + 2 * Real.exp (κ * T))) *
              (HRS.MS.S111K2.s111k2_age c u t * Real.exp (-κ * t)) := by
            apply setIntegral_congr_fun measurableSet_Icc
            intro t ht
            ring
      _ = (3 * B * R * M ^ 2 * (1 + 2 * Real.exp (κ * T))) *
            ∫ t in Icc 0 (u + T),
              HRS.MS.S111K2.s111k2_age c u t * Real.exp (-κ * t) := by
            rw [integral_const_mul]
      _ = _ := by
            congr 1
  have hJscalar :
      ∫ t in Icc 0 (u + T),
        (3 * B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R * M *
          (1 + Real.exp (κ * T))) *
          HRS.MS.S111K2.s111k2_age c u t ^ 2 * Real.exp (-κ * t) =
        (3 * B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R * M *
          (1 + Real.exp (κ * T))) *
          ∫ t in Icc 0 (u + T),
            Real.exp (-2 * c * max (u - t) 0) * Real.exp (-κ * t) := by
    calc
      _ = ∫ t in Icc 0 (u + T),
            (3 * B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R * M *
              (1 + Real.exp (κ * T))) *
              (HRS.MS.S111K2.s111k2_age c u t ^ 2 * Real.exp (-κ * t)) := by
            apply setIntegral_congr_fun measurableSet_Icc
            intro t ht
            ring
      _ = (3 * B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R * M *
            (1 + Real.exp (κ * T))) *
            ∫ t in Icc 0 (u + T),
              HRS.MS.S111K2.s111k2_age c u t ^ 2 * Real.exp (-κ * t) := by
            rw [integral_const_mul]
      _ = _ := by
            congr 1
            apply setIntegral_congr_fun measurableSet_Icc
            intro t ht
            simp only [HRS.MS.S111K2.s111k2_age, pow_two]
            rw [← Real.exp_add]
            congr 1
            ring
  constructor
  · have hreg : eVariationOn
        (fun v => D P O (qQ 0) (Z 0) v - D P O (qQ 1) (Z 1) v) (Icc 0 (u + T)) ≤
        ENNReal.ofReal (∫ t in Icc 0 (u + T),
          (3 * B * R * M ^ 2 * (1 + 2 * Real.exp (κ * T))) *
            HRS.MS.S111K2.s111k2_age c u t * Real.exp (-κ * t)) := by
      simpa [H] using hDreg.2
    calc
      _ ≤ _ := hreg
      _ = _ := congrArg ENNReal.ofReal hDscalar
  · have hreg : eVariationOn
        (fun v => J P O (qL 0) (Z 0) v - J P O (qL 1) (Z 1) v) (Icc 0 (u + T)) ≤
        ENNReal.ofReal (∫ t in Icc 0 (u + T),
          (3 * B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R * M *
            (1 + Real.exp (κ * T))) *
            HRS.MS.S111K2.s111k2_age c u t ^ 2 * Real.exp (-κ * t)) := by
      simpa [H] using hJreg.2
    calc
      _ ≤ _ := hreg
      _ = _ := congrArg ENNReal.ofReal hJscalar

#print axioms paired_variation

end HRS.Fp81.V01
end
