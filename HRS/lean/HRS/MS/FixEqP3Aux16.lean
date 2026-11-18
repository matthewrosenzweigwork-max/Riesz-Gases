import HRS.MS.FixEqP3Aux15

/-!
# S5.7 `fixed_equation` (worker S57P), part 28: the initial part for a family

`s57pI C m a η t`; norm and Lipschitz bounds (`s57p_init_lip`), the pairing identity `eval (s57pI t) φ = a η(U^{0,t}φ)` for `φ ∈ Σ^m`
(`s57p_init_eval`).
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

variable {d : ℕ}

/-- the initial part of the linear field -/
def s57pI (C : WholeCoeff d) (m a : ℝ) (η : (Euc d → ℝ) → ℝ) (t : ℝ) : OscDual d m :=
  ellVec m (fun α => a * η (propagatorW C 0 t (oscTestFun m α)))

theorem s57p_eval_tsum {m : ℝ} (u : OscDual d m) (φ : Euc d → ℝ) :
    OscDual.eval u φ = ∑' α, s57pb d m φ α * OscDual.coord u α := by
  unfold OscDual.eval
  refine tsum_congr fun α => ?_
  unfold OscDual.hermiteCoeff s57pb
  ring

theorem s57p_b_summable {m : ℝ} {J : ℕ} (hd : 1 ≤ d) (hm : (J : ℝ) + d < m) {φ : Euc d → ℝ} (hφ : IsOscTest m φ) :
    Summable fun α : MultiIndex d => |s57pb d m φ α| * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) := by
  have hb2 : Summable fun α : MultiIndex d => (s57pb d m φ α) ^ 2 := by
    refine hφ.2.2.congr fun α => ?_
    unfold s57pb
    rw [mul_pow, rpow_half_sq _ _ (oscEv_pos α)]
  have hg2 : Summable fun α : MultiIndex d => (oscEigenvalue d α ^ (((J : ℝ) - m) / 2)) ^ 2 := by
    refine (s57p_summable_J hd hm).congr fun α => ?_
    rw [rpow_half_sq _ _ (oscEv_pos α)]
  refine Summable.of_nonneg_of_le (fun α => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (oscEv_pos α).le _))
    (fun α => ?_) ((hb2.add hg2).div_const 2)
  have h1 := two_mul_le_add_sq |s57pb d m φ α| (oscEigenvalue d α ^ (((J : ℝ) - m) / 2))
  rw [sq_abs] at h1
  linarith

section Eta

variable {n : ℕ} {P : ℝ} {η : (Euc d → ℝ) → ℝ}

theorem s57p_eta_finsum (hP : (d : ℝ) < 2 * P) (hη : IsBoundedLinearOnE n P η) {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (f : ι → Euc d → ℝ) (b : ι → ℝ) (B : ι → ℝ) (hf : ∀ α, ContDiff ℝ n (f α))
    (hB : ∀ α, ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (f α) x‖ ≤ B α) :
    ContDiff ℝ n (fun y => ∑ α ∈ F, b α * f α y) ∧
      (∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (fun y => ∑ α ∈ F, b α * f α y) x‖ ≤ ∑ α ∈ F, |b α| * B α) ∧
      η (fun y => ∑ α ∈ F, b α * f α y) = ∑ α ∈ F, b α * η (f α) := by
  have hB0 : ∀ α, 0 ≤ B α := fun α => le_trans (norm_nonneg _) (hB α 0 (Nat.zero_le _) 0)
  induction F using Finset.induction_on with
  | empty =>
    have e : (fun y : Euc d => ∑ α ∈ (∅ : Finset ι), b α * f α y) = fun _ => 0 := by funext y; simp
    refine ⟨by rw [e]; exact contDiff_const, fun j hj x => ?_, ?_⟩
    · rw [e]
      simp only [Finset.sum_empty]
      rcases j with _ | j
      · simp
      · rw [iteratedFDeriv_const_of_ne (by omega)]; simp
    · have hz : ∀ j ≤ n, ∀ x : Euc d, ‖iteratedFDeriv ℝ j (fun _ : Euc d => (0 : ℝ)) x‖ ≤ 0 := fun j hj x => by
        rcases j with _ | j
        · simp
        · rw [iteratedFDeriv_const_of_ne (by omega)]; simp
      have hEz : weightedSobolevE n P (fun _ : Euc d => (0 : ℝ)) < ⊤ :=
        lt_of_le_of_lt (s57p_E_le_cb (r := n) hP (le_refl 0) hz) ENNReal.ofReal_lt_top
      have := (hη.1 (fun _ => 0) (fun _ => 0) contDiff_const hEz contDiff_const hEz 0).2
      have e2 : ((0 : ℝ) • fun _ : Euc d => (0 : ℝ)) = fun _ => 0 := by funext y; simp
      rw [e2] at this
      rw [e]
      simpa using this
  | insert β F hβ ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    have e : (fun y => ∑ α ∈ insert β F, b α * f α y) = fun y => (1 : ℝ) * (∑ α ∈ F, b α * f α y) + b β * f β y := by
      funext y; rw [Finset.sum_insert hβ, one_mul, add_comm]
    have hsB : 0 ≤ ∑ α ∈ F, |b α| * B α := Finset.sum_nonneg fun α _ => mul_nonneg (abs_nonneg _) (hB0 α)
    have hcf : ContDiff ℝ n (fun y => b β * f β y) := contDiff_const.mul (hf β)
    refine ⟨?_, fun j hj x => ?_, ?_⟩
    · rw [e]; exact (contDiff_const.mul ih1).add hcf
    · rw [e, s57p_iter_lin2 (ih1.of_le (by exact_mod_cast hj)) ((hf β).of_le (by exact_mod_cast hj)), Finset.sum_insert hβ]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_one, one_mul]
      have := mul_le_mul_of_nonneg_left (hB β j hj x) (abs_nonneg (b β))
      linarith [ih2 j hj x]
    · rw [Finset.sum_insert hβ, e]
      have hE : ∀ {u : Euc d → ℝ} {B' : ℝ}, 0 ≤ B' → (∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j u x‖ ≤ B') →
          weightedSobolevE n P u < ⊤ := fun hB' hu => lt_of_le_of_lt (s57p_E_le_cb hP hB' hu) ENNReal.ofReal_lt_top
      have h1 := (hη.1 (fun y => ∑ α ∈ F, b α * f α y) (fun y => b β * f β y) ih1 (hE hsB ih2) hcf
        (hE (mul_nonneg (abs_nonneg _) (hB0 β)) (fun j hj x => by
          refine (s57p_norm_const_mul ((hf β).of_le (by exact_mod_cast hj)) (b β) x).trans ?_
          exact mul_le_mul_of_nonneg_left (hB β j hj x) (abs_nonneg _))) 0).1
      have h2 := (hη.1 (f β) (f β) (hf β) (hE (hB0 β) (hB β)) (hf β) (hE (hB0 β) (hB β)) (b β)).2
      have e3 : (fun y => (1 : ℝ) * (∑ α ∈ F, b α * f α y) + b β * f β y) =
          (fun y => ∑ α ∈ F, b α * f α y) + fun y => b β * f β y := by funext y; simp
      have e4 : (b β • f β) = fun y => b β * f β y := by funext y; simp
      rw [e3, h1, ih3]
      rw [e4] at h2
      rw [h2]; ring

end Eta

end HRS.MS.FixEq
