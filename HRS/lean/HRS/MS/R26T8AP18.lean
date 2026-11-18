import HRS.MS.R26T8AV3
import HRS.MS.R26T8AP17
import HRS.MS.R26T8AD04

/-!
# S8.2 local Newton layer, packet T8A.P18: iterated defect conormal budget and the exact telescope (Pro contract verbatim)
Same-`k` chain: `F_0 = HSource` (P17, `Conormal (2L+10)`), `F_{j+1} = newtonDefect F_j` (P16 same-`k`, two derivatives per step, order `σ_j = criticalS d - j/2`, `M_j = 2j`).
`localNewton F_j` is `Conormal 8 1 (criticalS d - 2)` (P09 same-`k`); `pairA` of the finite sum is the sum of the `pairA` (V2), so the telescope `-pairA Q = F_0 - F_L` holds off the diagonal.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

set_option maxHeartbeats 6400000 in
theorem r26t8a_parametrix_telescope (d : ℕ) (hd : 2 ≤ d) (a beta : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ f : Euc d → ℝ, ∀ A : ℝ, 0 ≤ A → TestBound (testOrder d) A f →
      let C0 := critCoeff d a beta rho
      let mu := HRS.Whole.withDensityReal rho
      let R := r26t8a_parametrixTerm C0 mu chi f (iterationCount d)
      CanonicalPair mu (r26t8a_parametrix C0 mu chi f) ∧ CanonicalPair mu R ∧
      Conormal 10 0 M (criticalS d - (iterationCount d : ℝ) / 2) (C * A) R ∧
      Conormal 8 1 M (criticalS d - 2) (C * A) (r26t8a_parametrix C0 mu chi f) ∧
      ∀ x y, x ≠ y → -pairA C0 mu (r26t8a_parametrix C0 mu chi f) x y = HSource mu f x y - R x y := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hcrit_lt : criticalS d < d := by unfold criticalS; linarith
  have hcrit_nn : 0 ≤ criticalS d := by unfold criticalS; linarith
  obtain ⟨C17, hC170, hP17⟩ := r26t8a_source_conormal d hd a beta ha hbeta
  -- the iteration
  have iter : ∀ n : ℕ, ∃ Cn : ℝ, 0 ≤ Cn ∧ (n ≤ iterationCount d → ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho → ∀ (f : Euc d → ℝ) (A : ℝ), 0 ≤ A →
      TestBound (testOrder d) A f →
      CanonicalPair (HRS.Whole.withDensityReal rho)
        (r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f n) ∧
      Conormal (2 * (iterationCount d - n) + 10) 0 (2 * (n : ℝ)) (criticalS d - (n : ℝ) / 2) (Cn * A)
        (r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f n)) := by
    intro n
    induction n with
    | zero =>
      refine ⟨C17, hC170, fun _ rho hrho f A hA hf => ?_⟩
      obtain ⟨hcan, -, hcon⟩ := hP17 rho hrho f A hA hf
      have e : r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f 0 =
          HSource (HRS.Whole.withDensityReal rho) f := rfl
      rw [e]
      refine ⟨hcan, ?_⟩
      simpa using hcon
    | succ n ih =>
      obtain ⟨Cn, hCn0, hCn⟩ := ih
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      obtain ⟨CP, hCP0, hCP⟩ := r26t8a_defect_half_order_same d hd (2 * (iterationCount d - (n + 1)) + 10) a beta
        (2 * (n : ℝ)) (criticalS d - (n : ℝ) / 2) ha hbeta (by linarith) (by linarith) chi hchi
      refine ⟨CP * Cn, by positivity, fun hn rho hrho f A hA hf => ?_⟩
      obtain ⟨hcan, hcon⟩ := hCn (by omega) rho hrho f A hA hf
      have hcon' : Conormal (2 * (iterationCount d - (n + 1)) + 10 + 2) 0 (2 * (n : ℝ))
          (criticalS d - (n : ℝ) / 2) (Cn * A)
          (r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f n) := by
        have e : 2 * (iterationCount d - (n + 1)) + 10 + 2 = 2 * (iterationCount d - n) + 10 := by omega
        rw [e]; exact hcon
      obtain ⟨hcan', hcon''⟩ := hCP rho hrho _ (Cn * A) (mul_nonneg hCn0 hA) hcan hcon'
      have e1 : r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f (n + 1) =
          newtonDefect (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi
            (r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f n) :=
        Function.iterate_succ_apply' _ _ _
      rw [e1]
      refine ⟨hcan', ?_⟩
      have eM : 2 * (n : ℝ) + 2 = 2 * ((n + 1 : ℕ) : ℝ) := by push_cast; ring
      have eσ : criticalS d - (n : ℝ) / 2 - 1 / 2 = criticalS d - ((n + 1 : ℕ) : ℝ) / 2 := by push_cast; ring
      have eC : CP * (Cn * A) = (CP * Cn) * A := by ring
      rw [eM, eσ, eC] at hcon''
      exact hcon''
  choose Cn hCn0 hCn using iter
  -- the local Newton terms
  have hQ : ∀ j : ℕ, ∃ CQ : ℝ, 0 ≤ CQ ∧ (j < iterationCount d → ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho → ∀ (f : Euc d → ℝ) (A : ℝ), 0 ≤ A →
      TestBound (testOrder d) A f →
      CanonicalPair (HRS.Whole.withDensityReal rho)
        (localNewton (HRS.Whole.withDensityReal rho) (critCoeff d a beta rho).ν chi
          (r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f j)) ∧
      Conormal 8 1 (2 * (iterationCount d : ℝ)) (criticalS d - 2) (CQ * A)
        (localNewton (HRS.Whole.withDensityReal rho) (critCoeff d a beta rho).ν chi
          (r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f j))) := by
    intro j
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    obtain ⟨CZ, hCZ0, hCZ⟩ := r26t8a_local_newton_bound_same d hd 8 0 a beta (2 * (j : ℝ))
      (criticalS d - (j : ℝ) / 2) ha hbeta (by linarith) (by linarith) chi hchi
    refine ⟨CZ * Cn j, mul_nonneg hCZ0 (hCn0 j), fun hj rho hrho f A hA hf => ?_⟩
    obtain ⟨-, hcon⟩ := hCn j hj.le rho hrho f A hA hf
    have hcon8 : Conormal 8 0 (2 * (j : ℝ)) (criticalS d - (j : ℝ) / 2) (Cn j * A)
        (r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f j) :=
      r26t8a_conormal_mono (by omega) hcon
    obtain ⟨-, hQcan, hQcon⟩ := hCZ rho hrho _ (Cn j * A) (mul_nonneg (hCn0 j) hA) hcon8
    rw [r26t8a_critCoeff_nu a beta rho]
    refine ⟨hQcan, ?_⟩
    have hjL : (j : ℝ) ≤ iterationCount d := by exact_mod_cast hj.le
    have h1 := r26t8a_f23_conormal_M_mono (M' := 2 * (iterationCount d : ℝ)) (by linarith)
      (mul_nonneg hCZ0 (mul_nonneg (hCn0 j) hA)) hQcon
    refine r26t8a_conormal_mono_sA (mul_nonneg hCZ0 (mul_nonneg (hCn0 j) hA)) (le_of_eq (by ring)) (by linarith) h1
  choose CQ hCQ0 hCQ using hQ
  set Ctot : ℝ := Cn (iterationCount d) + ∑ j ∈ Finset.range (iterationCount d), CQ j with hCtot
  have hCtot0 : 0 ≤ Ctot := by
    have := hCn0 (iterationCount d)
    have : 0 ≤ ∑ j ∈ Finset.range (iterationCount d), CQ j := Finset.sum_nonneg fun j _ => hCQ0 j
    linarith
  refine ⟨Ctot, 2 * (iterationCount d : ℝ), hCtot0, by positivity, fun rho hrho f A hA hf => ?_⟩
  intro C0 mu R
  have hpar : r26t8a_parametrix C0 mu chi f = fun x y => ∑ j ∈ Finset.range (iterationCount d),
      localNewton mu C0.ν chi (r26t8a_parametrixTerm C0 mu chi f j) x y := by
    funext x y
    simp [r26t8a_parametrix, Finset.sum_apply]
  have hQj : ∀ j ∈ Finset.range (iterationCount d), CanonicalPair mu
      (localNewton mu C0.ν chi (r26t8a_parametrixTerm C0 mu chi f j)) ∧
      Conormal 8 1 (2 * (iterationCount d : ℝ)) (criticalS d - 2) (CQ j * A)
        (localNewton mu C0.ν chi (r26t8a_parametrixTerm C0 mu chi f j)) := fun j hj =>
    hCQ j (Finset.mem_range.1 hj) rho hrho f A hA hf
  obtain ⟨hRcan, hRcon⟩ := hCn (iterationCount d) le_rfl rho hrho f A hA hf
  have hRcon' : Conormal 10 0 (2 * (iterationCount d : ℝ)) (criticalS d - (iterationCount d : ℝ) / 2)
      (Cn (iterationCount d) * A) R := by
    have e : 2 * (iterationCount d - iterationCount d) + 10 = 10 := by omega
    rw [e] at hRcon; exact hRcon
  have hsumcon : Conormal 8 1 (2 * (iterationCount d : ℝ)) (criticalS d - 2)
      (∑ j ∈ Finset.range (iterationCount d), CQ j * A) (r26t8a_parametrix C0 mu chi f) := by
    rw [hpar]
    exact r26t8a_conormal_sum hchi _ (fun j hj => (hQj j hj).2)
  refine ⟨?_, hRcan, ?_, ?_, ?_⟩
  · rw [hpar]
    exact r26t8a_V3_canonical_sum mu _ (fun j hj => (hQj j hj).1)
  · refine r26t8a_conormal_mono_sA (mul_nonneg (hCn0 _) hA) ?_ le_rfl hRcon'
    exact mul_le_mul_of_nonneg_right (by
      have : 0 ≤ ∑ j ∈ Finset.range (iterationCount d), CQ j := Finset.sum_nonneg fun j _ => hCQ0 j
      linarith) hA
  · refine r26t8a_conormal_mono_sA (Finset.sum_nonneg fun j _ => mul_nonneg (hCQ0 j) hA) ?_ le_rfl hsumcon
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (by have := hCn0 (iterationCount d); linarith) hA
  · intro x y hxy
    have hnu : C0.ν = beta⁻¹ := r26t8a_critCoeff_nu a beta rho
    have hQ2 : ∀ j, j < iterationCount d → Conormal 2 1 (2 * (iterationCount d : ℝ)) (criticalS d - 2) (CQ j * A)
        (localNewton mu C0.ν chi (r26t8a_parametrixTerm C0 mu chi f j)) := fun j hj =>
      r26t8a_conormal_mono (by norm_num) (hQj j (Finset.mem_range.2 hj)).2
    have hpsum := r26t8a_V3_pairA_sum hd a beta (2 * (iterationCount d : ℝ)) (criticalS d) ha hbeta (by positivity)
      hcrit_lt rho hrho hchi (fun j => localNewton mu C0.ν chi (r26t8a_parametrixTerm C0 mu chi f j))
      (fun j => CQ j * A) (iterationCount d) (fun j _ => mul_nonneg (hCQ0 j) hA) hQ2 hxy
    rw [hpar, hpsum]
    have hstep : ∀ j, pairA C0 mu (localNewton mu C0.ν chi (r26t8a_parametrixTerm C0 mu chi f j)) x y =
        r26t8a_parametrixTerm C0 mu chi f (j + 1) x y - r26t8a_parametrixTerm C0 mu chi f j x y := by
      intro j
      have e1 : r26t8a_parametrixTerm C0 mu chi f (j + 1) =
          newtonDefect C0 mu chi (r26t8a_parametrixTerm C0 mu chi f j) := Function.iterate_succ_apply' _ _ _
      rw [e1]
      show _ = r26t8a_parametrixTerm C0 mu chi f j x y +
        pairA C0 mu (localNewton mu C0.ν chi (r26t8a_parametrixTerm C0 mu chi f j)) x y - _
      ring
    beta_reduce
    rw [Finset.sum_congr rfl (fun j _ => hstep j)]
    rw [Finset.sum_range_sub (fun j => r26t8a_parametrixTerm C0 mu chi f j x y)]
    have e0 : r26t8a_parametrixTerm C0 mu chi f 0 = HSource mu f := rfl
    rw [e0]
    show -(R x y - HSource mu f x y) = _
    ring

end HRS.MS.R26T8A
