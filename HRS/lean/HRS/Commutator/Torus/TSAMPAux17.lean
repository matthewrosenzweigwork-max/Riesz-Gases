import HRS.Commutator.Torus.TSAMPAux16

/-!
# T-SAMP helpers, part 17: the cells `Q_j` of side `1/m`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

/-- The box in `ℝ^d` whose preimage under `rep` is the cell. -/
def tsampBox (m : ℕ) (j : Fin d → Fin m) : Set (Euc d) :=
  {y | ∀ i, (j i : ℝ) / m ≤ y i ∧ y i < ((j i : ℝ) + 1) / m}

lemma tsamp_cell_eq (m : ℕ) (j : Fin d → Fin m) : cellT m j = Torus.rep ⁻¹' tsampBox m j := rfl

lemma tsamp_measurableSet_box (m : ℕ) (j : Fin d → Fin m) : MeasurableSet (tsampBox m j) := by
  have : tsampBox m j = ⋂ i, (fun y : Euc d => y i) ⁻¹' Set.Ico ((j i : ℝ) / m) (((j i : ℝ) + 1) / m) := by
    ext y; simp [tsampBox, Set.mem_Ico]
  rw [this]
  exact MeasurableSet.iInter fun i => measurableSet_Ico.preimage (tpos_measurable_coord i)

lemma tsamp_measurableSet_cell (m : ℕ) (j : Fin d → Fin m) : MeasurableSet (cellT m j) :=
  tpos_measurable_rep (tsamp_measurableSet_box m j)

lemma tsamp_box_volume {m : ℕ} (hm : 1 ≤ m) (j : Fin d → Fin m) :
    volume (tsampBox m j) = ENNReal.ofReal ((1 / (m : ℝ)) ^ d) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have e : tsampBox m j = (@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹'
      (Set.pi Set.univ fun i => Set.Ico ((j i : ℝ) / m) (((j i : ℝ) + 1) / m)) := by
    ext y; simp [tsampBox, Set.mem_Ico]
  rw [e, (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    (MeasurableSet.univ_pi fun i => measurableSet_Ico).nullMeasurableSet, Real.volume_pi_Ico]
  have : ∀ i : Fin d, ((j i : ℝ) + 1) / m - (j i : ℝ) / m = 1 / m := fun i => by ring
  simp_rw [this]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.ofReal_pow (by positivity)]

lemma tsamp_box_sub_cube {m : ℕ} (hm : 1 ≤ m) (j : Fin d → Fin m) {y : Euc d} (hy : y ∈ tsampBox m j)
    (i : Fin d) : 0 ≤ y i ∧ y i < 1 := by
  obtain ⟨h1, h2⟩ := hy i
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨le_trans (by positivity) h1, lt_of_lt_of_le h2 ?_⟩
  rw [div_le_one hm0]
  have := (j i).2
  have : ((j i : ℕ) : ℝ) + 1 ≤ m := by exact_mod_cast this
  exact this

lemma tsamp_rep_add_notin {m : ℕ} (hm : 1 ≤ m) (j : Fin d → Fin m) (x : Torus d) {l : Lattice d}
    (hl : l ≠ 0) : Torus.rep x + Lattice.toEuc l ∉ tsampBox m j := by
  intro hmem
  obtain ⟨i, hi⟩ : ∃ i, l i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hl (funext hall)
  have hb := tsamp_box_sub_cube hm j hmem i
  have hr := KernelGrad.rep_mem x i
  have h1 : (Torus.rep x + Lattice.toEuc l) i = Torus.rep x i + (l i : ℝ) := rfl
  rw [h1] at hb
  have h2 : (l i : ℝ) < 1 := by linarith [hb.2, hr.1]
  have h3 : (-1 : ℝ) < (l i : ℝ) := by linarith [hb.1, hr.2]
  have h2' : l i < 1 := by exact_mod_cast h2
  have h3' : -1 < l i := by exact_mod_cast h3
  exact hi (by omega)

lemma tsamp_cell_volume {m : ℕ} (hm : 1 ≤ m) (j : Fin d → Fin m) :
    volume (cellT m j) = ENNReal.ofReal ((1 / (m : ℝ)) ^ d) := by
  classical
  set G : Euc d → ℝ := (tsampBox m j).indicator (fun _ => (1 : ℝ)) with hG
  have hGm : Measurable G := measurable_const.indicator (tsamp_measurableSet_box m j)
  have hGnn : ∀ y, 0 ≤ G y := fun y => by
    simp only [hG, Set.indicator]; split_ifs <;> norm_num
  have hsum : ∀ y : Euc d, Summable fun l : Lattice d => G (y + Lattice.toEuc l) := by
    intro y
    refine summable_of_finite_support ?_
    refine (tpos_finite_norm_le (d := d) (d + ‖y‖)).subset ?_
    intro l hl
    simp only [Function.mem_support, hG, Set.indicator] at hl
    by_cases hmem : y + Lattice.toEuc l ∈ tsampBox m j
    · simp only [Set.mem_setOf_eq]
      have hb := tsamp_box_sub_cube hm j hmem
      have h1 : ‖y + Lattice.toEuc l‖ ≤ d := by
        have := Whole.cmxHLS_norm_toLp_le (d := d) (fun i => (y + Lattice.toEuc l) i)
        have e : (WithLp.toLp 2 (fun i => (y + Lattice.toEuc l) i) : Euc d) = y + Lattice.toEuc l := by
          ext i; rfl
        rw [e] at this
        refine this.trans ?_
        calc ∑ i, |(y + Lattice.toEuc l) i| ≤ ∑ _i : Fin d, (1 : ℝ) :=
              Finset.sum_le_sum fun i _ => by
                rw [abs_of_nonneg (hb i).1]; exact (hb i).2.le
          _ = d := by simp
      calc ‖Lattice.toEuc l‖ = ‖(y + Lattice.toEuc l) - y‖ := by rw [add_sub_cancel_left]
        _ ≤ ‖y + Lattice.toEuc l‖ + ‖y‖ := norm_sub_le _ _
        _ ≤ d + ‖y‖ := by linarith
    · exact absurd (by simp [hmem]) hl
  have hperio : ∀ x : Torus d, ENNReal.ofReal (perio G x) = (cellT m j).indicator (fun _ => (1 : ℝ≥0∞)) x := by
    intro x
    unfold perio
    rw [tsum_eq_single (0 : Lattice d)]
    · have h0 : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
      simp only [h0, add_zero, hG]
      by_cases hx : x ∈ cellT m j
      · rw [Set.indicator_of_mem (show Torus.rep x ∈ tsampBox m j from hx), Set.indicator_of_mem hx]
        simp
      · rw [Set.indicator_of_notMem (show Torus.rep x ∉ tsampBox m j from hx),
          Set.indicator_of_notMem hx]
        simp
    · intro l hl
      simp [hG, tsamp_rep_add_notin hm j x hl]
  have h1 := tpos_lintegral_perio hGm hGnn hsum
  simp_rw [hperio] at h1
  rw [lintegral_indicator_const (tsamp_measurableSet_cell m j), one_mul] at h1
  rw [h1]
  have : ∀ y, ENNReal.ofReal (G y) = (tsampBox m j).indicator (fun _ => (1 : ℝ≥0∞)) y := by
    intro y
    by_cases hy : y ∈ tsampBox m j
    · simp [hG, Set.indicator_of_mem hy]
    · simp [hG, Set.indicator_of_notMem hy]
  simp_rw [this]
  rw [lintegral_indicator_const (tsamp_measurableSet_box m j), one_mul, tsamp_box_volume hm]

end HRS.Commutator.TorusNote
