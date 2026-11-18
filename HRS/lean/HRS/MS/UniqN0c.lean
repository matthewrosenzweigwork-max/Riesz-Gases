import HRS.MS.UniqM1

/-!
# N0 of `UniqPlan.md`, parts (c) and (d): balls to sup, and the cell-sum / decay lemma

* `n0_ball_bound` (d): if `∫_{B(c,1)} F ≤ A` for every centre `c`, then `∫_{B(c,r)} F ≤ N(d,r) A` for every
  `c` and every `r` (arbitrary `F : ℝ^d → ℝ≥0∞`).
* `n0_cell_decay` (c): for `κ > d` there is `C = C(d,κ)` such that for every `f` with uniformly bounded
  local `L²` mass (`LocMass B f`) and every centre `c0`,
  `∫ |f(y)| (1+‖y - c0‖)^{-κ} dy ≤ C B`.  (The proof averages the slowly varying weight over unit balls and
  uses Tonelli; no lattice sum is needed.)
* `n0_cell_decay_mul`: the same for `∫ |f h|` with `|h| ≤ A (1+‖· - c0‖)^{-κ}`; `Integrable` version.
* `n0_jbracket_rpow_le`: `⟨x⟩^{-κ} ≤ 2^{κ/2} (1+‖x‖)^{-κ}` to pass from the `jbracket` weights of `IsRegularDensityW`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN0

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqM1

variable {d : ℕ}

/-! ### (d) balls to sup -/

theorem n0_ball_bound (d : ℕ) (r : ℝ) :
    ∃ N : ℕ, ∀ (F : Euc d → ℝ≥0∞) (A : ℝ≥0∞), (∀ c : Euc d, ∫⁻ y in ball c 1, F y ≤ A) →
      ∀ c : Euc d, ∫⁻ y in ball c r, F y ≤ (N : ℝ≥0∞) * A := by
  obtain ⟨s, hs⟩ := exists_unit_cover d r
  refine ⟨s.card, fun F A hF c => ?_⟩
  calc ∫⁻ y in ball c r, F y ≤ ∫⁻ y in ⋃ x ∈ s, ball (c + x) 1, F y :=
        lintegral_mono_set (hs c)
    _ ≤ ∑ x ∈ s, ∫⁻ y in ball (c + x) 1, F y := by
        rw [show (⋃ x ∈ s, ball (c + x) 1) = ⋃ x : s, ball (c + (x : Euc d)) 1 by
          ext; simp]
        refine (lintegral_iUnion_le _ _).trans ?_
        rw [tsum_fintype]
        exact (Finset.sum_coe_sort s fun x => ∫⁻ y in ball (c + x) 1, F y).le
    _ ≤ ∑ x ∈ s, A := Finset.sum_le_sum fun x _ => hF _
    _ = _ := by simp

/-! ### (c) decay against uniformly local `L¹` data -/

theorem n0_decay_pt {κ : ℝ} (hκ : 0 ≤ κ) (c0 y w : Euc d) (h : w ∈ ball y 1) :
    (1 + ‖y - c0‖) ^ (-κ) ≤ 2 ^ κ * (1 + ‖w - c0‖) ^ (-κ) := by
  have hw : ‖w - y‖ < 1 := by simpa [dist_eq_norm] using h
  have ha : 0 < 1 + ‖y - c0‖ := by positivity
  have hb : 0 < 1 + ‖w - c0‖ := by positivity
  have h1 : 1 + ‖w - c0‖ ≤ 2 * (1 + ‖y - c0‖) := by
    have : ‖w - c0‖ ≤ ‖w - y‖ + ‖y - c0‖ := by
      have := norm_add_le (w - y) (y - c0)
      simpa using this
    nlinarith [norm_nonneg (y - c0)]
  have h2 : (2 * (1 + ‖y - c0‖)) ^ (-κ) ≤ (1 + ‖w - c0‖) ^ (-κ) :=
    Real.rpow_le_rpow_of_nonpos hb h1 (by linarith)
  rw [Real.mul_rpow (by norm_num) ha.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] at h2
  have h3 : (0 : ℝ) < 2 ^ κ := by positivity
  calc (1 + ‖y - c0‖) ^ (-κ) = 2 ^ κ * ((2 ^ κ)⁻¹ * (1 + ‖y - c0‖) ^ (-κ)) := by
        field_simp
    _ ≤ _ := by gcongr

theorem n0_decay_integrable {κ : ℝ} (hκ : (d : ℝ) < κ) (c0 : Euc d) :
    Integrable (fun w : Euc d => (1 + ‖w - c0‖) ^ (-κ)) volume := by
  have := (integrable_one_add_norm (E := Euc d) (μ := volume) (r := κ) (by simpa using hκ))
  exact this.comp_sub_right c0

theorem n0_decay_core {κ : ℝ} (hκ : (d : ℝ) < κ) (c0 : Euc d) (f : Euc d → ℝ) (hf : Measurable f)
    (L : ℝ≥0∞) (hL : ∀ c : Euc d, ∫⁻ y in ball c 1, ‖f y‖ₑ ≤ L) :
    volume (ball (0 : Euc d) 1) * ∫⁻ y, ‖f y‖ₑ * ENNReal.ofReal ((1 + ‖y - c0‖) ^ (-κ)) ≤
      ENNReal.ofReal (2 ^ κ) *
        (L * ∫⁻ w, ENNReal.ofReal ((1 + ‖w - c0‖) ^ (-κ))) := by
  have hκ0 : 0 ≤ κ := le_trans (Nat.cast_nonneg d) hκ.le
  set W : Euc d → ℝ≥0∞ := fun w => ENNReal.ofReal ((1 + ‖w - c0‖) ^ (-κ)) with hW
  have hWm : Measurable W := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact (measurable_const.add (measurable_norm.comp (measurable_id.sub_const c0))).pow_const _
  have hWy : ∀ y, volume (ball (0 : Euc d) 1) * W y ≤
      ENNReal.ofReal (2 ^ κ) * ∫⁻ w in ball y 1, W w := by
    intro y
    calc volume (ball (0 : Euc d) 1) * W y = ∫⁻ w in ball y 1, W y := by
          have hv : volume (ball y 1) = volume (ball (0 : Euc d) 1) := by
            simp [Measure.addHaar_ball_center]
          rw [setLIntegral_const, hv, mul_comm]
      _ ≤ ∫⁻ w in ball y 1, ENNReal.ofReal (2 ^ κ) * W w := by
          refine setLIntegral_mono' measurableSet_ball fun w hw => ?_
          simp only [hW]
          rw [← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal (n0_decay_pt hκ0 c0 y w hw)
      _ = _ := lintegral_const_mul _ hWm
  set G : Euc d → Euc d → ℝ≥0∞ := fun y w => (ball y 1).indicator (fun w => ‖f y‖ₑ * W w) w
    with hG
  have hGm : Measurable (Function.uncurry G) := by
    have hS : MeasurableSet {p : Euc d × Euc d | p.2 ∈ ball p.1 1} := by
      have : {p : Euc d × Euc d | p.2 ∈ ball p.1 1} = {p | dist p.2 p.1 < 1} := by
        ext p; simp [mem_ball]
      rw [this]
      exact (isOpen_lt (continuous_snd.dist continuous_fst) continuous_const).measurableSet
    have : Function.uncurry G =
        {p : Euc d × Euc d | p.2 ∈ ball p.1 1}.indicator (fun p => ‖f p.1‖ₑ * W p.2) := by
      funext ⟨y, w⟩; simp [hG, Set.indicator, Function.uncurry]
    rw [this]
    exact ((hf.enorm.comp measurable_fst).mul (hWm.comp measurable_snd)).indicator hS
  have hGy : ∀ y, ∫⁻ w, G y w = ‖f y‖ₑ * ∫⁻ w in ball y 1, W w := by
    intro y
    simp only [hG]
    rw [lintegral_indicator measurableSet_ball, lintegral_const_mul _ hWm]
  have hGw : ∀ w, ∫⁻ y, G y w ≤ L * W w := by
    intro w
    have : ∀ y, G y w = (ball w 1).indicator (fun y => ‖f y‖ₑ * W w) y := by
      intro y
      simp only [hG, Set.indicator]
      by_cases h : w ∈ ball y 1
      · have h' : y ∈ ball w 1 := mem_ball_comm.1 h
        simp [h, h']
      · have h' : y ∉ ball w 1 := fun h'' => h (mem_ball_comm.1 h'')
        simp [h, h']
    simp_rw [this]
    rw [lintegral_indicator measurableSet_ball, lintegral_mul_const' _ _ (by simp [hW])]
    exact mul_le_mul' (hL w) le_rfl
  calc volume (ball (0 : Euc d) 1) * ∫⁻ y, ‖f y‖ₑ * W y
      = ∫⁻ y, volume (ball (0 : Euc d) 1) * (‖f y‖ₑ * W y) :=
        (lintegral_const_mul _ (hf.enorm.mul hWm)).symm
    _ = ∫⁻ y, ‖f y‖ₑ * (volume (ball (0 : Euc d) 1) * W y) := by
        refine lintegral_congr fun y => ?_; ring
    _ ≤ ∫⁻ y, ‖f y‖ₑ * (ENNReal.ofReal (2 ^ κ) * ∫⁻ w in ball y 1, W w) :=
        lintegral_mono fun y => mul_le_mul' le_rfl (hWy y)
    _ = ∫⁻ y, ENNReal.ofReal (2 ^ κ) * ∫⁻ w, G y w := by
        refine lintegral_congr fun y => ?_
        rw [hGy y]; ring
    _ = ENNReal.ofReal (2 ^ κ) * ∫⁻ y, ∫⁻ w, G y w := lintegral_const_mul' _ _ (by simp)
    _ = ENNReal.ofReal (2 ^ κ) * ∫⁻ w, ∫⁻ y, G y w := by
        rw [lintegral_lintegral_swap hGm.aemeasurable]
    _ ≤ ENNReal.ofReal (2 ^ κ) * ∫⁻ w, L * W w := by
        gcongr with w
        exact hGw w
    _ = _ := by rw [lintegral_const_mul _ hWm]

/-- (c) `∫ |f(y)| (1+‖y-c0‖)^{-κ} dy ≤ C B` for `f` of uniformly bounded local `L²` mass, `κ > d`;
`C = C(d,κ)` does not depend on `c0`, `B`, `f`. -/
theorem n0_cell_decay {κ : ℝ} (hκ : (d : ℝ) < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c0 : Euc d) (B : ℝ) (f : Euc d → ℝ), LocMass B f →
      ∫⁻ y, ‖f y‖ₑ * ENNReal.ofReal ((1 + ‖y - c0‖) ^ (-κ)) ≤ ENNReal.ofReal (C * |B|) := by
  have hκ0 : 0 ≤ κ := le_trans (Nat.cast_nonneg d) hκ.le
  obtain ⟨K, hK0, hK⟩ := exists_ball_l1_bound d 1
  set V : ℝ≥0∞ := volume (ball (0 : Euc d) 1) with hV
  have hV0 : V ≠ 0 := (Metric.measure_ball_pos volume (0 : Euc d) one_pos).ne'
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  have hVr : 0 < V.toReal := ENNReal.toReal_pos hV0 hVt
  set I0 : ℝ := ∫ w : Euc d, (1 + ‖w‖) ^ (-κ) with hI0
  have hI0nn : 0 ≤ I0 := integral_nonneg fun w => by positivity
  refine ⟨V.toReal⁻¹ * 2 ^ κ * K * I0, by positivity, fun c0 B f hf => ?_⟩
  -- a measurable representative
  set f' : Euc d → ℝ := hf.1.mk f with hf'
  have hf'm : Measurable f' := hf.1.stronglyMeasurable_mk.measurable
  have hff' : f =ᵐ[volume] f' := hf.1.ae_eq_mk
  have hLoc : LocMass |B| f' := by
    refine ⟨hf'm.aestronglyMeasurable, fun c => ?_⟩
    have : ∫⁻ y in ball c 1, ‖f' y‖ₑ ^ 2 = ∫⁻ y in ball c 1, ‖f y‖ₑ ^ 2 := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae hff'] with y hy
      rw [hy]
    rw [this, sq_abs]
    exact hf.2 c
  have hL : ∀ c : Euc d, ∫⁻ y in ball c 1, ‖f' y‖ₑ ≤ ENNReal.ofReal (K * |B|) :=
    fun c => hK |B| f' (abs_nonneg B) hLoc c
  have hcore := n0_decay_core hκ c0 f' hf'm _ hL
  have hint := n0_decay_integrable hκ c0
  have hIw : ∫⁻ w, ENNReal.ofReal ((1 + ‖w - c0‖) ^ (-κ)) = ENNReal.ofReal I0 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun w => by positivity)]
    congr 1
    exact integral_sub_right_eq_self (fun w : Euc d => (1 + ‖w‖) ^ (-κ)) c0
  rw [hIw] at hcore
  have heq : ∫⁻ y, ‖f y‖ₑ * ENNReal.ofReal ((1 + ‖y - c0‖) ^ (-κ)) =
      ∫⁻ y, ‖f' y‖ₑ * ENNReal.ofReal ((1 + ‖y - c0‖) ^ (-κ)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hff'] with y hy
    rw [hy]
  rw [heq]
  have h1 := (ENNReal.mul_le_iff_le_inv hV0 hVt).1 hcore
  refine h1.trans ?_
  have hVinv : V⁻¹ = ENNReal.ofReal V.toReal⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hVr, ENNReal.ofReal_toReal hVt]
  rw [hVinv, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  ring

/-- (c) with a pointwise decaying factor: `∫ |f h| ≤ C A B` if `|h| ≤ A (1+‖·-c0‖)^{-κ}`. -/
theorem n0_cell_decay_mul {κ : ℝ} (hκ : (d : ℝ) < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c0 : Euc d) (A B : ℝ) (f h : Euc d → ℝ), 0 ≤ A → LocMass B f →
      (∀ y, |h y| ≤ A * (1 + ‖y - c0‖) ^ (-κ)) →
      ∫⁻ y, ‖f y * h y‖ₑ ≤ ENNReal.ofReal (C * A * |B|) ∧
      (AEStronglyMeasurable h volume → Integrable (fun y => f y * h y) volume ∧
        ∫ y, |f y * h y| ≤ C * A * |B|) := by
  obtain ⟨C, hC0, hC⟩ := n0_cell_decay (d := d) hκ
  refine ⟨C, hC0, fun c0 A B f h hA hf hh => ?_⟩
  have hl : ∫⁻ y, ‖f y * h y‖ₑ ≤ ENNReal.ofReal (C * A * |B|) := by
    calc ∫⁻ y, ‖f y * h y‖ₑ ≤ ∫⁻ y, ENNReal.ofReal A *
          (‖f y‖ₑ * ENNReal.ofReal ((1 + ‖y - c0‖) ^ (-κ))) := by
          refine lintegral_mono fun y => ?_
          rw [enorm_mul]
          have : ‖h y‖ₑ ≤ ENNReal.ofReal A * ENNReal.ofReal ((1 + ‖y - c0‖) ^ (-κ)) := by
            rw [← ENNReal.ofReal_mul hA, Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_le_ofReal (hh y)
          calc ‖f y‖ₑ * ‖h y‖ₑ ≤ ‖f y‖ₑ * (ENNReal.ofReal A *
                ENNReal.ofReal ((1 + ‖y - c0‖) ^ (-κ))) := mul_le_mul' le_rfl this
            _ = _ := by ring
      _ = ENNReal.ofReal A * ∫⁻ y, ‖f y‖ₑ * ENNReal.ofReal ((1 + ‖y - c0‖) ^ (-κ)) :=
          lintegral_const_mul' _ _ (by simp)
      _ ≤ ENNReal.ofReal A * ENNReal.ofReal (C * |B|) := mul_le_mul' le_rfl (hC c0 B f hf)
      _ = _ := by rw [← ENNReal.ofReal_mul hA]; congr 1; ring
  refine ⟨hl, fun hhm => ?_⟩
  have hm : AEStronglyMeasurable (fun y => f y * h y) volume := hf.1.mul hhm
  have hfin : Integrable (fun y => f y * h y) volume := ⟨hm, hl.trans_lt ENNReal.ofReal_lt_top⟩
  refine ⟨hfin, ?_⟩
  have h1 : ∫ y, |f y * h y| = (∫⁻ y, ‖f y * h y‖ₑ).toReal := by
    rw [← integral_norm_eq_lintegral_enorm hm]
    simp [Real.norm_eq_abs]
  rw [h1]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hl).trans (ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg hC0 hA) (abs_nonneg B))).le

theorem n0_jbracket_rpow_le {κ : ℝ} (hκ : 0 ≤ κ) (x : Euc d) :
    jbracket x ^ (-κ) ≤ Real.sqrt 2 ^ κ * (1 + ‖x‖) ^ (-κ) := by
  have hj : 0 < jbracket x := by unfold jbracket; positivity
  have h1 : (1 + ‖x‖) / Real.sqrt 2 ≤ jbracket x := by
    rw [div_le_iff₀ (by positivity)]
    unfold jbracket
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (1 - ‖x‖), norm_nonneg x]
  have h2 : jbracket x ^ (-κ) ≤ ((1 + ‖x‖) / Real.sqrt 2) ^ (-κ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
  rw [Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity : (0 : ℝ) ≤ Real.sqrt 2)] at h2
  calc _ ≤ _ := h2
    _ = _ := by field_simp

end HRS.MS.UniqN0
