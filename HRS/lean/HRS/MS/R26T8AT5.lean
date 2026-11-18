import HRS.MS.R26T8AT4b
import HRS.MS.R26T8AP20

/-!
# S8.2 T8A T5: linearity of the parametrix sum, `TestBound` of linear combinations, and the defining property of the remainder
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_T5_testBound_lin {k : ℕ} {f g : Euc d → ℝ} {A B : ℝ} (hf : TestBound k A f) (hg : TestBound k B g)
    (c : ℝ) : TestBound k (A + |c| * B) (f + c • g) := by
  refine ⟨hf.1.add (hg.1.const_smul c), fun j hj hjk x => ?_⟩
  have hfj : ContDiff ℝ (j : WithTop ℕ∞) f := contDiff_infty.1 hf.1 j
  have hgj : ContDiff ℝ (j : WithTop ℕ∞) g := contDiff_infty.1 hg.1 j
  have h1 : iteratedFDeriv ℝ j (f + c • g) x = iteratedFDeriv ℝ j f x + c • iteratedFDeriv ℝ j g x := by
    have e : (f + c • g) = f + fun y => c • g y := rfl
    rw [e, iteratedFDeriv_add_apply hfj.contDiffAt (hgj.const_smul c).contDiffAt]
    congr 1
    exact iteratedFDeriv_const_smul_apply' hgj.contDiffAt
  rw [h1]
  refine (norm_add_le _ _).trans (add_le_add (hf.2 j hj hjk x) ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hg.2 j hj hjk x) (abs_nonneg c)

theorem r26t8a_T5_parametrix_lin (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (chi : Euc d → ℝ)
    (hchi : NewtonCutoff chi) (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    {f g : Euc d → ℝ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hf : TestBound (testOrder d) A f)
    (hg : TestBound (testOrder d) B g) (c : ℝ) {x y : Euc d} (hxy : x ≠ y) :
    r26t8a_parametrix (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi (f + c • g) x y =
      r26t8a_parametrix (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f x y +
        c * r26t8a_parametrix (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi g x y := by
  have hnu : (critCoeff d a beta rho).ν = beta⁻¹ := r26t8a_critCoeff_nu a beta rho
  have hterm := r26t8a_T4_term_lin hd a beta ha hbeta chi hchi rho hrho hA hB hf hg c
  have hloc : ∀ j, j < iterationCount d → localNewton (HRS.Whole.withDensityReal rho) (critCoeff d a beta rho).ν chi
      (r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi (f + c • g) j) x y =
      localNewton (HRS.Whole.withDensityReal rho) (critCoeff d a beta rho).ν chi
        (r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f j) x y +
      c * localNewton (HRS.Whole.withDensityReal rho) (critCoeff d a beta rho).ν chi
        (r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi g j) x y := by
    intro j hj
    choose Cn hCn0 hCn using r26t8a_T4_iter d hd a beta ha hbeta chi hchi
    obtain ⟨-, hTf⟩ := hCn j hj.le rho hrho f A hA hf
    obtain ⟨-, hTg⟩ := hCn j hj.le rho hrho g B hB hg
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hσd : criticalS d - (j : ℝ) / 2 < d := by unfold criticalS; linarith
    rw [hnu, r26t8a_T4_localNewton_congr hd rho beta⁻¹ chi
      (F2 := fun x y => r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f j x y +
        c * r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi g j x y)
      (fun x y hxy => hterm j hj.le x y hxy) hxy]
    exact r26t8a_T2_localNewton_lin hd a beta (2 * (j : ℝ)) (criticalS d - (j : ℝ) / 2) ha hbeta (by linarith) hσd
      _ _ rho hrho hchi (mul_nonneg (hCn0 j) hA) (mul_nonneg (hCn0 j) hB) hTf hTg c hxy
  unfold r26t8a_parametrix
  simp only [Finset.sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j hj => hloc j (Finset.mem_range.1 hj)

theorem r26t8a_T5_remainder_spec (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (chi : Euc d → ℝ)
    (hchi : NewtonCutoff chi) (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    {f : Euc d → ℝ} {A : ℝ} (hA : 0 ≤ A) (hf : TestBound (testOrder d) A f) :
    ContDiff ℝ 8 (Function.uncurry (r26t8a_remainder (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f)) ∧
    (∀ x y, x ≠ y → r26t8a_remainder (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f x y =
      r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f (iterationCount d) x y) ∧
    (∀ G : Euc d → Euc d → ℝ, Continuous (Function.uncurry G) →
      (∀ x y, x ≠ y → G x y = r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f
        (iterationCount d) x y) →
      G = r26t8a_remainder (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f) := by
  obtain ⟨C18, M, hC180, hM, h18⟩ := r26t8a_parametrix_telescope d hd a beta ha hbeta chi hchi
  obtain ⟨C19, hC190, h19⟩ := r26t8a_parametrix_extension hd M hM
  obtain ⟨-, -, hconR, -, -⟩ := h18 rho hrho f A hA hf
  have hσ : criticalS d - (iterationCount d : ℝ) / 2 = -(d : ℝ) / 2 - 12 := by
    unfold criticalS iterationCount; push_cast; ring
  have hconR' := hconR
  rw [hσ] at hconR'
  obtain ⟨Rext, hRc, hRe, hRb, hRu⟩ := h19 (C18 * A) (mul_nonneg hC180 hA) _ hconR'
  have hex : ∃ G : Euc d → Euc d → ℝ, ContDiff ℝ 8 (Function.uncurry G) ∧
      ∀ x y, x ≠ y → G x y = r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f
        (iterationCount d) x y := ⟨Rext, hRc, hRe⟩
  have hrem : r26t8a_remainder (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f = Rext := by
    unfold r26t8a_remainder
    rw [dif_pos hex]
    obtain ⟨hs1, hs2⟩ := hex.choose_spec
    exact hRu _ hs1.continuous hs2
  rw [hrem]
  exact ⟨hRc, hRe, fun G hG hGe => hRu G hG hGe⟩

end HRS.MS.R26T8A
