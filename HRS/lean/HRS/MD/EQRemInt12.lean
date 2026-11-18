import HRS.MD.EQRemInt11

/-!
# EQ-REM (b), part 12: the abstract pathwise Minkowski and second-moment assembly
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MD.EQRem

open HRS HRS.MD.EQ29 HRS.Quad

variable {d N : ℕ}

theorem eqrem_sq_eq {κ : ℝ} (hκ : 0 ≤ κ) (e : ℝ≥0∞) :
    ENNReal.ofReal (κ ^ 2) * e = (ENNReal.ofReal κ * e ^ (1 / 2 : ℝ)) ^ 2 := by
  rw [mul_pow, eqrem_sq_rpow_half, ENNReal.ofReal_pow hκ]

theorem eqrem_abstract {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {M : ℝ} (Y : ℝ × Ω → Config d N) (hY : Measurable Y) (E : Config d N → ℝ≥0∞)
    (hE : Measurable E) (Gm : ℝ → NonzeroLattice d → ℝ → Config d N → ℝ)
    (hGm : ∀ t k, Measurable (Function.uncurry (Gm t k)))
    {K c : ℝ} (hK : 0 ≤ K) (hc : 0 < c)
    (hGen : ∀ t r x, coordEnergy M (fun k => Gm t k r x) ≤
      ENNReal.ofReal (((K + 1) * Real.exp (-c * (t - r))) ^ 2) * E x)
    (a T : ℝ) (ha : 0 ≤ a) (hT : 0 ≤ T) (B0 : ℝ≥0∞) (hB0 : B0 ≠ ⊤)
    (hB : ∀ r ∈ Set.Ioc 0 (a + T), ∫⁻ ω, E (Y (r, ω)) ∂P ≤ B0) :
    ∃ Φ : Ω → ℝ≥0∞, Measurable Φ ∧
      (∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) (a + T), ∀ k,
        IntegrableOn (fun r => Gm t k r (Y (r, ω))) (Set.Ioc 0 t)) ∧
      (∀ᵐ ω ∂P, ∀ t ∈ Set.Icc a (a + T),
        (coordEnergy M (fun k => ∫ r in Set.Ioc 0 t, Gm t k r (Y (r, ω)))) ^ (1 / 2 : ℝ) ≤ Φ ω) ∧
      ∫⁻ ω, Φ ω ^ 2 ∂P ≤ ENNReal.ofReal ((K + 1) * (1 / c + T)) ^ 2 * B0 := by
  have hb : 0 ≤ a + T := add_nonneg ha hT
  have hK1 : 0 < K + 1 := by linarith
  have hjE : Measurable fun p : ℝ × Ω => E (Y p) := hE.comp hY
  have hjEh : Measurable fun p : ℝ × Ω => (E (Y p)) ^ (1 / 2 : ℝ) := hjE.pow_const _
  have hEh : ∀ ω, Measurable fun r : ℝ => (E (Y (r, ω))) ^ (1 / 2 : ℝ) := fun ω =>
    hjEh.comp (measurable_id.prodMk measurable_const)
  set wR : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal ((K + 1) * Real.exp (-c * max (a - r) 0)) with hwR
  have hwRm : Measurable wR := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact (by fun_prop : Continuous fun r : ℝ => (K + 1) * Real.exp (-c * max (a - r) 0)).measurable
  set w1 : ℝ → ℝ≥0∞ := fun _ => ENNReal.ofReal (K + 1) with hw1
  have hw1m : Measurable w1 := measurable_const
  set S0 : Set ℝ := Set.Ioc 0 (a + T) with hS0
  have hS0m : MeasurableSet S0 := measurableSet_Ioc
  -- finiteness of the unweighted functional
  set Φ1 : Ω → ℝ≥0∞ := fun ω => ∫⁻ r in S0, w1 r * (E (Y (r, ω))) ^ (1 / 2 : ℝ) with hΦ1
  have hΦ1m : Measurable Φ1 :=
    (((hw1m.comp measurable_fst).mul hjEh : Measurable fun p : ℝ × Ω => w1 p.1 *
      (E (Y p)) ^ (1 / 2 : ℝ))).lintegral_prod_left'
  have hW1 : ∫⁻ r in S0, w1 r ≠ ⊤ := by
    simp only [hw1, lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, hS0,
      Real.volume_Ioc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hmom1 := eqrem_second_moment P Y hY E hE S0 hS0m w1 hw1m B0 hB
  have hΦ1fin : ∀ᵐ ω ∂P, Φ1 ω < ⊤ := by
    have hne : ∫⁻ ω, Φ1 ω ^ 2 ∂P ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top hW1) hB0) hmom1
    have h2 : ∀ᵐ ω ∂P, Φ1 ω ^ 2 < ⊤ := ae_lt_top' (hΦ1m.pow_const 2).aemeasurable hne
    filter_upwards [h2] with ω hω
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    rw [hcon] at hω
    simp at hω
  -- pathwise bounds
  have hG1 : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), ∀ r ∈ Set.Ioc 0 t, ∀ ω,
      coordEnergy M (fun k => Gm t k r (Y (r, ω))) ≤
        (ENNReal.ofReal (K + 1) * (E (Y (r, ω))) ^ (1 / 2 : ℝ)) ^ 2 := by
    intro t ht r hr ω
    refine (hGen t r (Y (r, ω))).trans ?_
    have hκ0 : 0 ≤ (K + 1) * Real.exp (-c * (t - r)) := mul_nonneg hK1.le (Real.exp_pos _).le
    rw [eqrem_sq_eq hκ0]
    refine pow_le_pow_left' (mul_le_mul' ?_ le_rfl) 2
    refine ENNReal.ofReal_le_ofReal ?_
    have : Real.exp (-c * (t - r)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [hr.2]
    nlinarith
  have hfm : ∀ t k ω, Measurable fun r => Gm t k r (Y (r, ω)) := by
    intro t k ω
    exact (hGm t k).comp (measurable_id.prodMk (hY.comp (measurable_id.prodMk measurable_const)))
  have hint : ∀ ω, Φ1 ω < ⊤ → ∀ t ∈ Set.Icc (0 : ℝ) (a + T), ∀ k,
      IntegrableOn (fun r => Gm t k r (Y (r, ω))) (Set.Ioc 0 t) := by
    intro ω hω t ht k
    refine ⟨(hfm t k ω).aestronglyMeasurable, ?_⟩
    show ∫⁻ r in Set.Ioc 0 t, ‖Gm t k r (Y (r, ω))‖ₑ < ⊤
    have hle : ∫⁻ r in Set.Ioc 0 t, ‖Gm t k r (Y (r, ω))‖ₑ ≤
        ∫⁻ r in Set.Ioc 0 t, ENNReal.ofReal (Lattice.jp k.1 ^ M) *
          (w1 r * (E (Y (r, ω))) ^ (1 / 2 : ℝ)) := by
      refine setLIntegral_mono' measurableSet_Ioc fun r hr => ?_
      rw [Real.enorm_eq_ofReal_abs]
      exact eqrem_abs_le_of_energy_le (fun k => Gm t k r (Y (r, ω))) (hG1 t ht r hr ω) k
    refine lt_of_le_of_lt hle ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt ?_ hω)
    exact lintegral_mono_set (Set.Ioc_subset_Ioc_right ht.2)
  -- the main functional
  set Φ : Ω → ℝ≥0∞ := fun ω => ∫⁻ r in S0, wR r * (E (Y (r, ω))) ^ (1 / 2 : ℝ) with hΦ
  have hΦm : Measurable Φ :=
    (((hwRm.comp measurable_fst).mul hjEh : Measurable fun p : ℝ × Ω => wR p.1 *
      (E (Y p)) ^ (1 / 2 : ℝ))).lintegral_prod_left'
  refine ⟨Φ, hΦm, ?_, ?_, ?_⟩
  · filter_upwards [hΦ1fin] with ω hω using hint ω hω
  · filter_upwards [hΦ1fin] with ω hω t ht
    have ht0 : t ∈ Set.Icc (0 : ℝ) (a + T) := ⟨ha.trans ht.1, ht.2⟩
    have hmink := eqrem_minkowski (M := M) (Set.Ioc 0 t) measurableSet_Ioc
      (fun k r => Gm t k r (Y (r, ω))) (hint ω hω t ht0)
      (fun r => ENNReal.ofReal ((K + 1) * Real.exp (-c * (t - r))) * (E (Y (r, ω))) ^ (1 / 2 : ℝ))
      (by
        intro r hr
        refine (hGen t r (Y (r, ω))).trans (le_of_eq ?_)
        exact eqrem_sq_eq (mul_nonneg hK1.le (Real.exp_pos _).le) _)
    refine (eqrem_rpow_half_le_of_le_sq hmink).trans ?_
    refine le_trans ?_ (lintegral_mono_set (Set.Ioc_subset_Ioc_right ht.2))
    refine setLIntegral_mono' measurableSet_Ioc fun r hr => ?_
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK1.le
    have : max (a - r) 0 ≤ t - r := max_le (by linarith [ht.1]) (by linarith [hr.2])
    nlinarith
  · have hmom := eqrem_second_moment P Y hY E hE S0 hS0m wR hwRm B0 hB
    refine hmom.trans ?_
    refine mul_le_mul' (pow_le_pow_left' ?_ 2) le_rfl
    exact eqrem_weight_bound hK1.le hc ha hT

end HRS.MD.EQRem

end
