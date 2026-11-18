import HRS.Sections.AdjKBAux3

/-!
# ADJKB Aux4: probabilistic part of the Kolmogorov-Chentsov tightness criterion
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.AdjK

lemma adjkb_markov_incr {E : Type*} [NormedAddCommGroup E] {T p q : ℝ} {M : ℝ≥0} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {Y : Set.Icc (0 : ℝ) T → Ω → E}
    (hY : IsKolmogorovProcess Y P p q M) (s t : Set.Icc (0 : ℝ) T) (γ : ℝ) (hγ : 0 < γ) :
    P {ω | γ < ‖Y s ω - Y t ω‖} ≤ ENNReal.ofReal (M * |(s : ℝ) - t| ^ q / γ ^ p) := by
  have hp := hY.p_pos
  have hγp : 0 < γ ^ p := Real.rpow_pos_of_pos hγ p
  have hsub : {ω | γ < ‖Y s ω - Y t ω‖} ⊆
      {ω | ENNReal.ofReal (γ ^ p) ≤ edist (Y s ω) (Y t ω) ^ p} := by
    intro ω hω
    simp only [mem_setOf_eq] at hω ⊢
    rw [edist_eq_enorm_sub, ← ofReal_norm_eq_enorm,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hγ.le hω.le hp.le)
  have hmeas : AEMeasurable (fun ω => edist (Y s ω) (Y t ω) ^ p) P :=
    (hY.measurable_edist.pow_const p).aemeasurable
  have hmk := meas_ge_le_lintegral_div hmeas (ε := ENNReal.ofReal (γ ^ p))
    (ENNReal.ofReal_pos.2 hγp).ne' ENNReal.ofReal_ne_top
  have hK := hY.kolmogorovCondition s t
  have hedist : edist s t = ENNReal.ofReal |(s : ℝ) - t| := by
    rw [edist_dist, Subtype.dist_eq, Real.dist_eq]
  refine (measure_mono hsub).trans (hmk.trans ?_)
  refine (ENNReal.div_le_div_right hK _).trans (le_of_eq ?_)
  rw [hedist, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hY.q_pos.le,
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul M.coe_nonneg,
    ← ENNReal.ofReal_div_of_pos hγp]

lemma adjkb_proj_val {T : ℝ} (hT : 0 < T) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) T) :
    ((Set.projIcc 0 T hT.le x : Set.Icc (0 : ℝ) T) : ℝ) = x := by
  rw [Set.projIcc_of_mem _ hx]

/-- one dyadic level -/
lemma adjkb_level_bound {E : Type*} [NormedAddCommGroup E] {T p q : ℝ} (hT : 0 < T) {M : ℝ≥0}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Set.Icc (0 : ℝ) T → Ω → E}
    (hY : IsKolmogorovProcess Y P p q M) (n : ℕ) (γ : ℝ) (hγ : 0 < γ) :
    P {ω | ∃ a : ℕ, a < 2 ^ n ∧
        γ < ‖Y (Set.projIcc 0 T hT.le (((a : ℝ) + 1) * (T / 2 ^ n))) ω -
          Y (Set.projIcc 0 T hT.le ((a : ℝ) * (T / 2 ^ n))) ω‖} ≤
      ENNReal.ofReal ((2 : ℝ) ^ n * (M * (T / 2 ^ n) ^ q / γ ^ p)) := by
  have hτ : 0 < T / 2 ^ n := by positivity
  have hsub : {ω | ∃ a : ℕ, a < 2 ^ n ∧
        γ < ‖Y (Set.projIcc 0 T hT.le (((a : ℝ) + 1) * (T / 2 ^ n))) ω -
          Y (Set.projIcc 0 T hT.le ((a : ℝ) * (T / 2 ^ n))) ω‖} ⊆
      ⋃ a ∈ Finset.range (2 ^ n), {ω | γ <
        ‖Y (Set.projIcc 0 T hT.le (((a : ℝ) + 1) * (T / 2 ^ n))) ω -
          Y (Set.projIcc 0 T hT.le ((a : ℝ) * (T / 2 ^ n))) ω‖} := by
    intro ω ⟨a, ha, h⟩
    simp only [mem_iUnion, Finset.mem_range]
    exact ⟨a, ha, h⟩
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hterm : ∀ a ∈ Finset.range (2 ^ n), P {ω | γ <
        ‖Y (Set.projIcc 0 T hT.le (((a : ℝ) + 1) * (T / 2 ^ n))) ω -
          Y (Set.projIcc 0 T hT.le ((a : ℝ) * (T / 2 ^ n))) ω‖} ≤
      ENNReal.ofReal (M * (T / 2 ^ n) ^ q / γ ^ p) := by
    intro a ha
    rw [Finset.mem_range] at ha
    refine (adjkb_markov_incr hY _ _ γ hγ).trans (le_of_eq ?_)
    congr 3
    have h1 : (((a : ℝ) + 1) * (T / 2 ^ n)) ∈ Set.Icc (0 : ℝ) T := by
      refine ⟨by positivity, ?_⟩
      have : ((a : ℝ) + 1) ≤ 2 ^ n := by exact_mod_cast ha
      calc ((a : ℝ) + 1) * (T / 2 ^ n) ≤ 2 ^ n * (T / 2 ^ n) :=
            mul_le_mul_of_nonneg_right this hτ.le
        _ = T := by field_simp
    have h2 : ((a : ℝ) * (T / 2 ^ n)) ∈ Set.Icc (0 : ℝ) T := by
      refine ⟨by positivity, ?_⟩
      have : (a : ℝ) ≤ 2 ^ n := by exact_mod_cast ha.le
      calc (a : ℝ) * (T / 2 ^ n) ≤ 2 ^ n * (T / 2 ^ n) :=
            mul_le_mul_of_nonneg_right this hτ.le
        _ = T := by field_simp
    rw [adjkb_proj_val hT h1, adjkb_proj_val hT h2]
    rw [show ((a : ℝ) + 1) * (T / 2 ^ n) - (a : ℝ) * (T / 2 ^ n) = T / 2 ^ n by ring,
      abs_of_pos hτ]
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [show ((2 : ℝ) ^ n) = ((2 ^ n : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]

end HRS.AdjK
