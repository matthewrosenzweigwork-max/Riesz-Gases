import HRS.MS.R26T8AU2
import HRS.MS.R26T8AP18
import HRS.MS.R26T8AP19

/-!
# S8.2 local Newton layer, packet T8A.P20: exact finite parametrix with a smooth canonical remainder (Pro contract verbatim)
From P18 (telescope, canonical rows, conormal bounds), P19 (unique `C^8` diagonal extension of the final remainder), U1 (the diagonal is invisible to
canonical rows and to `pairA`) and U2 (symmetry is preserved by the Newton defect).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

set_option maxHeartbeats 6400000 in
theorem r26t8a_finite_parametrix (d : ℕ) (hd : 2 ≤ d)
    (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ f : Euc d → ℝ, ∀ A : ℝ, 0 ≤ A → TestBound (testOrder d) A f →
      ∃ Q R : Euc d → Euc d → ℝ,
        Q = r26t8a_parametrixZero (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f ∧
        R = r26t8a_remainder (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f ∧
        CanonicalPair (HRS.Whole.withDensityReal rho) Q ∧
        CanonicalPair (HRS.Whole.withDensityReal rho) R ∧
        (∀ x y, Q x y = Q y x ∧ R x y = R y x) ∧
        Conormal 8 1 M (criticalS d - 2) (C * A) Q ∧
        ContDiff ℝ 8 (Function.uncurry R) ∧
        (∀ j : ℕ, j ≤ 8 → ∀ x y,
          ‖iteratedFDeriv ℝ j (Function.uncurry R) (x, y)‖ ≤
            C * A * HRS.MS.Phase2S82.pairWeight M x y) ∧
        ∀ x y, x ≠ y →
          -pairA (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q x y =
            HSource (HRS.Whole.withDensityReal rho) f x y - R x y := by
  obtain ⟨C18, M, hC180, hM, h18⟩ := r26t8a_parametrix_telescope d hd a beta ha hbeta chi hchi
  obtain ⟨C19, hC190, h19⟩ := r26t8a_parametrix_extension hd M hM
  obtain ⟨C17, -, h17⟩ := r26t8a_source_conormal d hd a beta ha hbeta
  refine ⟨C18 + C19 * C18, M, by positivity, hM, fun rho hrho f A hA hf => ?_⟩
  obtain ⟨hcanP, hcanR, hconR, hconP, htel⟩ := h18 rho hrho f A hA hf
  obtain ⟨-, hsym0, -⟩ := h17 rho hrho f A hA hf
  set C0 := critCoeff d a beta rho with hC0
  set mu := HRS.Whole.withDensityReal rho with hmu
  set Rt := r26t8a_parametrixTerm C0 mu chi f (iterationCount d) with hRt
  have hσ : criticalS d - (iterationCount d : ℝ) / 2 = -(d : ℝ) / 2 - 12 := by
    unfold criticalS iterationCount; push_cast; ring
  rw [hσ] at hconR
  have hC18A : 0 ≤ C18 * A := mul_nonneg hC180 hA
  obtain ⟨Rext, hRc, hRe, hRb, hRu⟩ := h19 (C18 * A) hC18A Rt hconR
  have hrem : r26t8a_remainder C0 mu chi f = Rext := by
    have hex : ∃ G : Euc d → Euc d → ℝ, ContDiff ℝ 8 (Function.uncurry G) ∧
        ∀ x y, x ≠ y → G x y = Rt x y := ⟨Rext, hRc, hRe⟩
    unfold r26t8a_remainder
    rw [dif_pos hex]
    obtain ⟨hs1, hs2⟩ := hex.choose_spec
    exact hRu _ hs1.continuous hs2
  have hQeq : ∀ x y, x ≠ y → r26t8a_parametrixZero C0 mu chi f x y = r26t8a_parametrix C0 mu chi f x y := by
    intro x y hxy; simp [r26t8a_parametrixZero, hxy]
  have hRsym : ∀ x y, Rext x y = Rext y x := by
    have hcont : Continuous (Function.uncurry (fun x y => Rext y x)) :=
      hRc.continuous.comp (continuous_snd.prodMk continuous_fst)
    have := hRu (fun x y => Rext y x) hcont (fun x y hxy => by
      rw [hRe y x (Ne.symm hxy)]
      exact (r26t8a_U2_term_symm C0 mu hchi f hsym0 _ y x))
    intro x y
    exact (congrFun (congrFun this x) y).symm
  refine ⟨r26t8a_parametrixZero C0 mu chi f, Rext, rfl, hrem.symm, ?_, ?_, ?_, ?_, hRc, ?_, ?_⟩
  · exact r26t8a_U1_canonical_congr hd rho hQeq hcanP
  · exact r26t8a_U1_canonical_congr hd rho (fun x y hxy => hRe x y hxy) hcanR
  · intro x y
    refine ⟨?_, hRsym x y⟩
    by_cases hxy : x = y
    · rw [hxy]
    · rw [hQeq x y hxy, hQeq y x (Ne.symm hxy)]
      exact r26t8a_U2_parametrix_symm C0 mu hchi f hsym0 x y
  · refine r26t8a_conormal_mono_sA hC18A ?_ le_rfl (r26t8a_conormal_congr (fun x y hxy => (hQeq x y hxy).symm) hconP)
    exact mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hC190 hC180]) hA
  · intro j hj x y
    refine (hRb j hj x y).trans ?_
    have hpw := r26t8a_pairWeight_nonneg (d := d) M x y
    have : C19 * (C18 * A) * HRS.MS.Phase2S82.pairWeight M x y ≤
        (C18 + C19 * C18) * A * HRS.MS.Phase2S82.pairWeight M x y := by
      have h1 : 0 ≤ C18 * A * HRS.MS.Phase2S82.pairWeight M x y := by positivity
      nlinarith
    exact this
  · intro x y hxy
    rw [r26t8a_U1_pairA_congr hd C0 rho hQeq hxy, htel x y hxy, hRe x y hxy]

end HRS.MS.R26T8A
