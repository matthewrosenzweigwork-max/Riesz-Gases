import HRS.MS.S82QVar
import HRS.MS.S82P2Var1

/-!
# S8.2 (S82Q): variance template for ordered pair statistics `c * pairSum K` (symmetric `K`)
Under `referenceLaw N N` (no pins), `Var <= 16 C0^2 N c^2 J` where `J` bounds `int Psi dmu` and
`Psi x` bounds the second moment of the row `sum_j K x (X'_j)` under the one-pin law `R^{x}_{N-1}`.
Also the transfer of variance bounds to `canonicalP` by domination.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82Q
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2

/-- Row `i` of the ordered pair sum. -/
def s82q_prow {d N : ℕ} (K : Euc d → Euc d → ℝ) (i : Fin N) (X : EucConfig d N) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, K (X i) (X j)

lemma s82q_prow_insertNth {d m : ℕ} (K : Euc d → Euc d → ℝ) (i : Fin (m + 1)) (z : Euc d)
    (X' : Fin m → Euc d) :
    s82q_prow K i (i.insertNth z X' : EucConfig d (m + 1)) = ∑ j, K z (X' j) := by
  unfold s82q_prow
  rw [s82p2_sum_erase (fun j => K ((i.insertNth z X' : EucConfig d (m + 1)) i)
    ((i.insertNth z X' : EucConfig d (m + 1)) j)) i]
  simp

lemma s82q_prow_measurable {d N : ℕ} {K : Euc d → Euc d → ℝ} (hK : Measurable (Function.uncurry K))
    (i : Fin N) : Measurable (s82q_prow K i : EucConfig d N → ℝ) := by
  unfold s82q_prow
  refine Finset.measurable_sum _ fun j _ => ?_
  have h2 := hK.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply j) :
    Measurable fun X : EucConfig d N => (X i, X j))
  exact h2

lemma s82q_pairSum_eq {d N : ℕ} (K : Euc d → Euc d → ℝ) (X : EucConfig d N) :
    Phase2S82.pairSum K X = ∑ i, s82q_prow K i X := rfl

lemma s82q_pairSum_diff {d m : ℕ} {K : Euc d → Euc d → ℝ} (hKs : ∀ x y, K x y = K y x)
    (i : Fin (m + 1)) (X : EucConfig d (m + 1)) (y : Euc d) :
    Phase2S82.pairSum K (Function.update X i y) - Phase2S82.pairSum K X =
      2 * (s82q_prow K i (Function.update X i y) - s82q_prow K i X) := by
  have key : ∀ (z : Euc d) (X' : Fin m → Euc d),
      Phase2S82.pairSum K (Function.update (i.insertNth z X' : EucConfig d (m + 1)) i y) -
        Phase2S82.pairSum K (i.insertNth z X' : EucConfig d (m + 1)) =
      2 * (s82q_prow K i (Function.update (i.insertNth z X' : EucConfig d (m + 1)) i y) -
        s82q_prow K i (i.insertNth z X' : EucConfig d (m + 1))) := by
    intro z X'
    rw [s82p2_update_insertNth, s82p2_pairSum_insertNth_gen, s82p2_pairSum_insertNth_gen,
      s82q_prow_insertNth, s82q_prow_insertNth]
    have e : ∀ w : Euc d, ∑ j, (K w (X' j) + K (X' j) w) = 2 * ∑ j, K w (X' j) := by
      intro w
      rw [Finset.mul_sum, ← Finset.sum_congr rfl fun j _ => (two_mul (K w (X' j))).symm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hKs (X' j) w]
    rw [e, e]
    ring
  have := key (X i) (fun j => X (i.succAbove j))
  rwa [s82q_insertNth_removeNth] at this

/-- Transfer of a variance bound from the unpinned reference law to the physical canonical law. -/
theorem s82q_transfer {d : ℕ} {a beta C0 : ℝ} {rho q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}
    (hW : WeakReferenceSetup d a beta rho q h C0) {N : ℕ} (hN : 2 ≤ N)
    (F : EucConfig d N → ℝ) (hFm : Measurable F)
    (hF : MemLp F 2 (unpinnedReference q h (HRS.Whole.withDensityReal rho) beta N))
    (V : ℝ≥0∞)
    (hV : evariance F (unpinnedReference q h (HRS.Whole.withDensityReal rho) beta N) ≤ V) :
    MemLp F 2 (canonicalP d N a beta) ∧
      evariance F (canonicalP d N a beta) ≤ ENNReal.ofReal C0 * V := by
  have := s82p2_canonicalP_prob hW hN
  have : IsProbabilityMeasure (unpinnedReference q h (HRS.Whole.withDensityReal rho) beta N) :=
    hW.probability N hN 0 N (by omega) (by omega) (fun i : Fin 0 => i.elim0)
  refine ⟨(hF.smul_measure ENNReal.ofReal_ne_top).mono_measure (hW.domination N hN), ?_⟩
  exact (s82p2_evariance_le_of_le_smul (P := canonicalP d N a beta)
    (Q := unpinnedReference q h (HRS.Whole.withDensityReal rho) beta N)
    (c := ENNReal.ofReal C0) ENNReal.ofReal_ne_top (hW.domination N hN) F
    hFm.aestronglyMeasurable).trans (mul_le_mul_of_nonneg_left hV bot_le)

/-- Variance template for the ordered pair sum of `m + 1` particles with `p ≤ 1` pins, `N` fixed. -/
theorem s82q_pair_template {d : ℕ} {a beta C0 : ℝ} {rho : Euc d → ℝ} {q : Euc d → ℝ}
    {h : ℕ → Euc d → ℝ} [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)]
    (hW : WeakReferenceSetup d a beta rho q h C0) (hbeta : 0 < beta) {N : ℕ} (hN : 2 ≤ N)
    {p m : ℕ} (hp : p ≤ 1) (hnp : m + 1 + p ≤ N) (hNn : N - (m + 1 + p) ≤ 2)
    (pins : Fin p → Euc d)
    (K : Euc d → Euc d → ℝ) (hKs : ∀ x y, K x y = K y x) (hKm : Measurable (Function.uncurry K))
    (cN : ℝ) (Ψ : Euc d → ℝ) (J : ℝ)
    (hrow : ∀ᵐ x ∂HRS.Whole.withDensityReal rho, ∫⁻ X', ENNReal.ofReal ((∑ j, K x (X' j)) ^ 2)
      ∂referenceLaw q h (HRS.Whole.withDensityReal rho) beta N m
        (Fin.cons x pins : Fin (p + 1) → Euc d) ≤ ENNReal.ofReal (Ψ x))
    (hJ : ∫⁻ x, ENNReal.ofReal (Ψ x)
      ∂s82q_nu q (HRS.Whole.withDensityReal rho) beta N pins ≤ ENNReal.ofReal J) :
    (∀ i : Fin (m + 1), MemLp (s82q_prow K i) 2
        (referenceLaw q h (HRS.Whole.withDensityReal rho) beta N (m + 1) pins)) ∧
    MemLp (fun X : EucConfig d (m + 1) => cN * Phase2S82.pairSum K X) 2
        (referenceLaw q h (HRS.Whole.withDensityReal rho) beta N (m + 1) pins) ∧
      evariance (fun X : EucConfig d (m + 1) => cN * Phase2S82.pairSum K X)
        (referenceLaw q h (HRS.Whole.withDensityReal rho) beta N (m + 1) pins) ≤
        ENNReal.ofReal (16 * C0 ^ 2 * (m + 1 : ℕ) * cN ^ 2 * J) := by
  set mu := HRS.Whole.withDensityReal rho with hmu
  have hC0 := hW.positive
  have hprob0 : IsProbabilityMeasure (referenceLaw q h mu beta N (m + 1) pins) :=
    hW.probability N hN p (m + 1) (by omega) hnp pins
  have hprob1 : ∀ z : Euc d, IsProbabilityMeasure (referenceLaw q h mu beta N m
      (Fin.cons z pins : Fin (p + 1) → Euc d)) := fun z =>
    hW.probability N hN (p + 1) m (by omega) (by omega) _
  set ref := referenceLaw q h mu beta N (m + 1) pins with href
  -- Step 1: row second moments under the reference law
  have hI : ∀ i : Fin (m + 1), ∫⁻ X, ENNReal.ofReal (s82q_prow K i X ^ 2) ∂ref ≤
      ENNReal.ofReal (C0 * J) := by
    intro i
    have hmeas : Measurable (fun X : EucConfig d (m + 1) => ENNReal.ofReal (s82q_prow K i X ^ 2)) :=
      ENNReal.measurable_ofReal.comp ((s82q_prow_measurable hKm i).pow_const 2)
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
    simp_rw [s82q_prow_insertNth]
    calc ∫⁻ z, ∫⁻ X', ENNReal.ofReal ((∑ j, K z (X' j)) ^ 2)
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
  have hrowL : ∀ i : Fin (m + 1), MemLp (s82q_prow K i) 2 ref := fun i =>
    s82q_memLp_two_of_lintegral (s82q_prow_measurable hKm i).aestronglyMeasurable
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hI i))
  have hFL : MemLp (fun X : EucConfig d (m + 1) => cN * Phase2S82.pairSum K X) 2 ref := by
    have : (fun X : EucConfig d (m + 1) => cN * Phase2S82.pairSum K X) =
        fun X => cN * ∑ i, s82q_prow K i X := rfl
    rw [this]
    exact (memLp_finsetSum _ (fun i _ => hrowL i)).const_mul cN
  refine ⟨hrowL, hFL, ?_⟩
  -- Step 3: variance
  have hdiff : ∀ (i : Fin (m + 1)) (X : EucConfig d (m + 1)) (y : Euc d),
      (cN * Phase2S82.pairSum K (Function.update X i y)) - cN * Phase2S82.pairSum K X =
        (2 * cN) * (s82q_prow K i (Function.update X i y) - s82q_prow K i X) := by
    intro i X y
    rw [← mul_sub, s82q_pairSum_diff hKs]
    ring
  have hvr := s82q_var_rows hW hbeta hN (p := p) (by omega) hnp hNn pins _ hFL
    (fun i => s82q_prow K i) (fun i => s82q_prow_measurable hKm i) (2 * cN) hdiff
  refine hvr.trans ?_
  calc ENNReal.ofReal C0 * ∑ i : Fin (m + 1), ENNReal.ofReal (4 * (2 * cN) ^ 2) *
        ∫⁻ X, ENNReal.ofReal (s82q_prow K i X ^ 2) ∂ref
      ≤ ENNReal.ofReal C0 * ∑ i : Fin (m + 1), ENNReal.ofReal (4 * (2 * cN) ^ 2) *
          ENNReal.ofReal (C0 * J) := by
        gcongr with i _
        exact hI i
    _ = ENNReal.ofReal (16 * C0 ^ 2 * (m + 1 : ℕ) * cN ^ 2 * J) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul hC0.le]
        congr 1
        ring

end HRS.MS.S82Q
