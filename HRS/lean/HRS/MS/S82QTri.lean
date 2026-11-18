import HRS.MS.S82QPairT

/-!
# S8.2 (S82Q): variance template for ordered triple statistics `c * tripleSum G` (fully symmetric `G`)
The row of site `i` is `trow G i X = sum_{j,k} G(X_i, X_j, X_k)`; a one-site update changes `tripleSum` by
`3 (trow(update) - trow)`, and `trow (insertNth z X') = pairSum (G z) X'`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82Q
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2

/-- Row `i` of the ordered triple sum. -/
def s82q_trow {d N : ℕ} (G : Euc d → Euc d → Euc d → ℝ) (i : Fin N) (X : EucConfig d N) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j, G (X i) (X j) (X k)

lemma s82q_tripleSum_ite {d N : ℕ} (G : Euc d → Euc d → Euc d → ℝ) (X : EucConfig d N) :
    Phase2S82.tripleSum G X =
      ∑ a, ∑ b, ∑ c, if (b ≠ a ∧ c ≠ a ∧ c ≠ b) then G (X a) (X b) (X c) else 0 := by
  classical
  unfold Phase2S82.tripleSum
  refine Finset.sum_congr rfl fun a _ => ?_
  have h1 : ∀ b : Fin N, (∑ c, if (b ≠ a ∧ c ≠ a ∧ c ≠ b) then G (X a) (X b) (X c) else 0) =
      if b ≠ a then ∑ c ∈ (Finset.univ.erase a).erase b, G (X a) (X b) (X c) else 0 := by
    intro b
    by_cases hb : b = a
    · simp [hb]
    · simp only [hb, ne_eq, not_false_eq_true, true_and, ite_true]
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext c
      simp [Finset.mem_erase, and_comm]
  simp_rw [h1]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext b
  simp [Finset.mem_erase]

lemma s82q_trow_ite {d N : ℕ} (G : Euc d → Euc d → Euc d → ℝ) (i : Fin N) (X : EucConfig d N) :
    s82q_trow G i X = ∑ b, ∑ c, if (b ≠ i ∧ c ≠ i ∧ c ≠ b) then G (X i) (X b) (X c) else 0 := by
  classical
  unfold s82q_trow
  have h1 : ∀ b : Fin N, (∑ c, if (b ≠ i ∧ c ≠ i ∧ c ≠ b) then G (X i) (X b) (X c) else 0) =
      if b ≠ i then ∑ c ∈ (Finset.univ.erase i).erase b, G (X i) (X b) (X c) else 0 := by
    intro b
    by_cases hb : b = i
    · simp [hb]
    · simp only [hb, ne_eq, not_false_eq_true, true_and, ite_true]
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext c
      simp [Finset.mem_erase, and_comm]
  simp_rw [h1]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext b
  simp [Finset.mem_erase]

lemma s82q_pairSum_ite {d N : ℕ} (F : Euc d → Euc d → ℝ) (X : EucConfig d N) :
    Phase2S82.pairSum F X = ∑ x : Fin N, ∑ x_1 : Fin N, if ¬x_1 = x then F (X x) (X x_1) else 0 := by
  classical
  unfold Phase2S82.pairSum
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext c
  simp [Finset.mem_erase]

lemma s82q_trow_insertNth {d m : ℕ} (G : Euc d → Euc d → Euc d → ℝ) (i : Fin (m + 1)) (z : Euc d)
    (X' : Fin m → Euc d) :
    s82q_trow G i (i.insertNth z X' : EucConfig d (m + 1)) =
      Phase2S82.pairSum (fun y w => G z y w) X' := by
  classical
  rw [s82q_trow_ite, s82q_pairSum_ite]
  simp only [Fin.sum_univ_succAbove _ i, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  have hne : ∀ x : Fin m, i.succAbove x ≠ i := fun x => Fin.succAbove_ne i x
  have hne' : ∀ x : Fin m, i ≠ i.succAbove x := fun x => (Fin.succAbove_ne i x).symm
  simp only [ne_eq, not_true_eq_false, false_and, ite_false, zero_add, Finset.sum_const_zero,
    hne, hne', not_false_eq_true, true_and, and_true, Fin.succAbove_right_inj, Finset.sum_add_distrib]

lemma s82q_tripleSum_insertNth {d m : ℕ} (G : Euc d → Euc d → Euc d → ℝ)
    (hG1 : ∀ x y z, G x y z = G y x z) (hG2 : ∀ x y z, G x y z = G x z y)
    (i : Fin (m + 1)) (z : Euc d) (X' : Fin m → Euc d) :
    Phase2S82.tripleSum G (i.insertNth z X' : EucConfig d (m + 1)) =
      3 * Phase2S82.pairSum (fun y w => G z y w) X' + Phase2S82.tripleSum G X' := by
  classical
  rw [s82q_tripleSum_ite, s82q_tripleSum_ite]
  simp only [Fin.sum_univ_succAbove _ i, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  have hne : ∀ x : Fin m, i.succAbove x ≠ i := fun x => Fin.succAbove_ne i x
  have hne' : ∀ x : Fin m, i ≠ i.succAbove x := fun x => (Fin.succAbove_ne i x).symm
  simp only [ne_eq, not_true_eq_false, false_and, ite_false, zero_add, Finset.sum_const_zero,
    hne, hne', not_false_eq_true, true_and, and_true, Fin.succAbove_right_inj, Finset.sum_add_distrib]
  have hp := s82q_pairSum_ite (fun y w => G z y w) X'
  have e2 : (∑ x : Fin m, ∑ x_1 : Fin m, if ¬x_1 = x then G (X' x) z (X' x_1) else 0) =
      ∑ x : Fin m, ∑ x_1 : Fin m, if ¬x_1 = x then G z (X' x) (X' x_1) else 0 := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x1 _ => ?_
    rw [hG1 (X' x) z (X' x1)]
  have e3 : (∑ x : Fin m, ∑ x_1 : Fin m, if ¬x_1 = x then G (X' x) (X' x_1) z else 0) =
      ∑ x : Fin m, ∑ x_1 : Fin m, if ¬x_1 = x then G z (X' x) (X' x_1) else 0 := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x1 _ => ?_
    rw [hG2 (X' x) (X' x1) z, hG1 (X' x) z (X' x1)]
  rw [hp, e2, e3]
  ring

lemma s82q_trow_measurable {d N : ℕ} {G : Euc d → Euc d → Euc d → ℝ}
    (hG : Measurable (fun p : Euc d × Euc d × Euc d => G p.1 p.2.1 p.2.2)) (i : Fin N) :
    Measurable (s82q_trow G i : EucConfig d N → ℝ) := by
  unfold s82q_trow
  refine Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ => ?_
  have h2 := hG.comp ((measurable_pi_apply i).prodMk ((measurable_pi_apply j).prodMk
    (measurable_pi_apply k)) : Measurable fun X : EucConfig d N => (X i, X j, X k))
  exact h2

lemma s82q_tripleSum_diff {d m : ℕ} {G : Euc d → Euc d → Euc d → ℝ}
    (hG1 : ∀ x y z, G x y z = G y x z) (hG2 : ∀ x y z, G x y z = G x z y)
    (i : Fin (m + 1)) (X : EucConfig d (m + 1)) (y : Euc d) :
    Phase2S82.tripleSum G (Function.update X i y) - Phase2S82.tripleSum G X =
      3 * (s82q_trow G i (Function.update X i y) - s82q_trow G i X) := by
  have key : ∀ (z : Euc d) (X' : Fin m → Euc d),
      Phase2S82.tripleSum G (Function.update (i.insertNth z X' : EucConfig d (m + 1)) i y) -
        Phase2S82.tripleSum G (i.insertNth z X' : EucConfig d (m + 1)) =
      3 * (s82q_trow G i (Function.update (i.insertNth z X' : EucConfig d (m + 1)) i y) -
        s82q_trow G i (i.insertNth z X' : EucConfig d (m + 1))) := by
    intro z X'
    rw [s82p2_update_insertNth, s82q_tripleSum_insertNth G hG1 hG2,
      s82q_tripleSum_insertNth G hG1 hG2, s82q_trow_insertNth, s82q_trow_insertNth]
    ring
  have := key (X i) (fun j => X (i.succAbove j))
  rwa [s82q_insertNth_removeNth] at this

/-- Variance template for the ordered triple sum. -/
theorem s82q_triple_template {d : ℕ} {a beta C0 : ℝ} {rho : Euc d → ℝ} {q : Euc d → ℝ}
    {h : ℕ → Euc d → ℝ} [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)]
    (hW : WeakReferenceSetup d a beta rho q h C0) (hbeta : 0 < beta) {N : ℕ} (hN : 2 ≤ N)
    {p m : ℕ} (hp : p ≤ 1) (hnp : m + 1 + p ≤ N) (hNn : N - (m + 1 + p) ≤ 2)
    (pins : Fin p → Euc d)
    (G : Euc d → Euc d → Euc d → ℝ) (hG1 : ∀ x y z, G x y z = G y x z)
    (hG2 : ∀ x y z, G x y z = G x z y)
    (hGm : Measurable (fun p : Euc d × Euc d × Euc d => G p.1 p.2.1 p.2.2))
    (cN : ℝ) (Ψ : Euc d → ℝ) (J : ℝ)
    (hrow : ∀ᵐ x ∂HRS.Whole.withDensityReal rho, ∫⁻ X', ENNReal.ofReal ((Phase2S82.pairSum (fun y w => G x y w) X') ^ 2)
      ∂referenceLaw q h (HRS.Whole.withDensityReal rho) beta N m
        (Fin.cons x pins : Fin (p + 1) → Euc d) ≤ ENNReal.ofReal (Ψ x))
    (hJ : ∫⁻ x, ENNReal.ofReal (Ψ x)
      ∂s82q_nu q (HRS.Whole.withDensityReal rho) beta N pins ≤ ENNReal.ofReal J) :
    (∀ i : Fin (m + 1), MemLp (s82q_trow G i) 2
        (referenceLaw q h (HRS.Whole.withDensityReal rho) beta N (m + 1) pins)) ∧
    MemLp (fun X : EucConfig d (m + 1) => cN * Phase2S82.tripleSum G X) 2
        (referenceLaw q h (HRS.Whole.withDensityReal rho) beta N (m + 1) pins) ∧
      evariance (fun X : EucConfig d (m + 1) => cN * Phase2S82.tripleSum G X)
        (referenceLaw q h (HRS.Whole.withDensityReal rho) beta N (m + 1) pins) ≤
        ENNReal.ofReal (36 * C0 ^ 2 * (m + 1 : ℕ) * cN ^ 2 * J) := by
  set mu := HRS.Whole.withDensityReal rho with hmu
  have hC0 := hW.positive
  have hprob0 : IsProbabilityMeasure (referenceLaw q h mu beta N (m + 1) pins) :=
    hW.probability N hN p (m + 1) (by omega) hnp pins
  have hprob1 : ∀ z : Euc d, IsProbabilityMeasure (referenceLaw q h mu beta N m
      (Fin.cons z pins : Fin (p + 1) → Euc d)) := fun z =>
    hW.probability N hN (p + 1) m (by omega) (by omega) _
  set ref := referenceLaw q h mu beta N (m + 1) pins with href
  -- Step 1: row second moments under the reference law
  have hI : ∀ i : Fin (m + 1), ∫⁻ X, ENNReal.ofReal (s82q_trow G i X ^ 2) ∂ref ≤
      ENNReal.ofReal (C0 * J) := by
    intro i
    have hmeas : Measurable (fun X : EucConfig d (m + 1) => ENNReal.ofReal (s82q_trow G i X ^ 2)) :=
      ENNReal.measurable_ofReal.comp ((s82q_trow_measurable hGm i).pow_const 2)
    have hmarg := s82q_marg_le_nu hW hbeta hN (p := p) (by omega) hnp pins i
    have hmu_dom : (referenceLaw q h mu beta N (m + 1) pins).map (fun X => X i) ≤
        ENNReal.ofReal C0 • mu := by
      refine hmarg.trans (Measure.le_iff.2 fun s hs => ?_)
      rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left
        (Measure.le_iff.1 (s82q_nu_le q hW.short.nonneg mu beta hbeta N pins) s hs) bot_le
    have hac : (referenceLaw q h mu beta N (m + 1) pins).map (fun X => X i) ≪ mu :=
      Measure.absolutelyContinuous_of_le_smul hmu_dom
    rw [href, s82p2_disintegration (mu := mu) hW.short.measurable hW.short.even beta N
      (hW.hmeas N) pins i hprob0 hprob1 _ hmeas]
    simp_rw [s82q_trow_insertNth]
    calc ∫⁻ z, ∫⁻ X', ENNReal.ofReal ((Phase2S82.pairSum (fun y w => G z y w) X') ^ 2)
            ∂referenceLaw q h mu beta N m (Fin.cons z pins : Fin (p + 1) → Euc d)
            ∂((referenceLaw q h mu beta N (m + 1) pins).map (fun X => X i))
        ≤ ∫⁻ z, ENNReal.ofReal (Ψ z)
            ∂((referenceLaw q h mu beta N (m + 1) pins).map (fun X => X i)) :=
          lintegral_mono_ae (hac.ae_le hrow)
      _ ≤ ∫⁻ z, ENNReal.ofReal (Ψ z) ∂(ENNReal.ofReal C0 • s82q_nu q mu beta N pins) :=
          lintegral_mono' (s82q_marg_le_nu hW hbeta hN (p := p) (by omega) hnp pins i) le_rfl
      _ = ENNReal.ofReal C0 * ∫⁻ z, ENNReal.ofReal (Ψ z) ∂(s82q_nu q mu beta N pins) := by
          rw [lintegral_smul_measure, smul_eq_mul]
      _ ≤ ENNReal.ofReal C0 * ENNReal.ofReal J := mul_le_mul_of_nonneg_left hJ bot_le
      _ = ENNReal.ofReal (C0 * J) := (ENNReal.ofReal_mul hC0.le).symm
  -- Step 2: membership
  have hrowL : ∀ i : Fin (m + 1), MemLp (s82q_trow G i) 2 ref := fun i =>
    s82q_memLp_two_of_lintegral (s82q_trow_measurable hGm i).aestronglyMeasurable
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hI i))
  have hFL : MemLp (fun X : EucConfig d (m + 1) => cN * Phase2S82.tripleSum G X) 2 ref := by
    have : (fun X : EucConfig d (m + 1) => cN * Phase2S82.tripleSum G X) =
        fun X => cN * ∑ i, s82q_trow G i X := rfl
    rw [this]
    exact (memLp_finsetSum _ (fun i _ => hrowL i)).const_mul cN
  refine ⟨hrowL, hFL, ?_⟩
  -- Step 3: variance
  have hdiff : ∀ (i : Fin (m + 1)) (X : EucConfig d (m + 1)) (y : Euc d),
      (cN * Phase2S82.tripleSum G (Function.update X i y)) - cN * Phase2S82.tripleSum G X =
        (3 * cN) * (s82q_trow G i (Function.update X i y) - s82q_trow G i X) := by
    intro i X y
    rw [← mul_sub, s82q_tripleSum_diff hG1 hG2]
    ring
  have hvr := s82q_var_rows hW hbeta hN (p := p) (by omega) hnp hNn pins _ hFL
    (fun i => s82q_trow G i) (fun i => s82q_trow_measurable hGm i) (3 * cN) hdiff
  refine hvr.trans ?_
  calc ENNReal.ofReal C0 * ∑ i : Fin (m + 1), ENNReal.ofReal (4 * (3 * cN) ^ 2) *
        ∫⁻ X, ENNReal.ofReal (s82q_trow G i X ^ 2) ∂ref
      ≤ ENNReal.ofReal C0 * ∑ i : Fin (m + 1), ENNReal.ofReal (4 * (3 * cN) ^ 2) *
          ENNReal.ofReal (C0 * J) := by
        gcongr with i _
        exact hI i
    _ = ENNReal.ofReal (36 * C0 ^ 2 * (m + 1 : ℕ) * cN ^ 2 * J) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul hC0.le]
        congr 1
        ring

end HRS.MS.S82Q
