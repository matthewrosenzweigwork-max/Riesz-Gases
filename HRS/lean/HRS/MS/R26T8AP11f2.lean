import HRS.MS.R26T8AP11f1
import HRS.MS.S82P2Defs
import HRS.MS.WadAux1

/-!
# S8.2 T8A P11f (part 2): a `C^k` pair function with jets bounded by `B * pairWeight M` is `Conormal k 0 M 0 (2^k B)`
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_conormal_of_smooth {k b : ℕ} {σ M B : ℝ} (hB : 0 ≤ B) {F : Euc d → Euc d → ℝ}
    (hF : ContDiff ℝ (k : WithTop ℕ∞) (Function.uncurry F))
    (hj : ∀ j ≤ k, ∀ x y : Euc d, ‖iteratedFDeriv ℝ j (Function.uncurry F) (x, y)‖ ≤ B * pairWeight M x y) :
    Conormal k b M σ (2 ^ k * B) F := by
  refine ⟨hF.contDiffOn, fun p q hpq X z hz => ?_⟩
  set Λ : (Euc d × Euc d) →L[ℝ] (Euc d × Euc d) :=
    ((ContinuousLinearMap.fst ℝ (Euc d) (Euc d)) + (1 / 2 : ℝ) • ContinuousLinearMap.snd ℝ (Euc d) (Euc d)).prod
      ((ContinuousLinearMap.fst ℝ (Euc d) (Euc d)) - (1 / 2 : ℝ) • ContinuousLinearMap.snd ℝ (Euc d) (Euc d))
    with hΛ
  have hΛn : ‖Λ‖ ≤ 2 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun w => ?_
    have h1 : ‖w.1‖ ≤ ‖w‖ := norm_fst_le w
    have h2 : ‖w.2‖ ≤ ‖w‖ := norm_snd_le w
    simp only [hΛ, ContinuousLinearMap.prod_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.smul_apply, Prod.norm_def]
    have h3 := le_max_left ‖w.1‖ ‖w.2‖
    have h4 := le_max_right ‖w.1‖ ‖w.2‖
    have h5 : 0 ≤ max ‖w.1‖ ‖w.2‖ := le_max_of_le_left (norm_nonneg _)
    refine max_le ?_ ?_
    · refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg (by norm_num)]; linarith
    · refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg (by norm_num)]; linarith
  have hΛx : Λ (X, z) = (X + (1 / 2 : ℝ) • z, X - (1 / 2 : ℝ) • z) := by
    simp [hΛ]
  have hΦ : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) := by
    have h1 : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (Function.uncurry F ∘ Λ) :=
      (hF.of_le (by exact_mod_cast hpq)).comp Λ.contDiff
    exact h1
  have hmj : mixedJet p q F X z = r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) X z := rfl
  rw [hmj]
  refine (r26t8a_nest_le_joint p q hΦ X z).trans ?_
  have hcomp := Λ.iteratedFDeriv_comp_right (n := ((p + q : ℕ) : WithTop ℕ∞))
    (f := Function.uncurry F) (hF.of_le (by exact_mod_cast hpq)) (X, z) (i := p + q) le_rfl
  have hfun : (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) = Function.uncurry F ∘ Λ := by
    funext Yw; simp [hΛ, midPair, Function.uncurry]
  rw [hfun, hcomp]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _i : Fin (p + q), ‖Λ‖ ≤ 2 ^ (p + q) := by
    calc ∏ _i : Fin (p + q), ‖Λ‖ = ‖Λ‖ ^ (p + q) := by simp
      _ ≤ 2 ^ (p + q) := pow_le_pow_left₀ (norm_nonneg _) hΛn _
  have hb := hj (p + q) hpq (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z)
  rw [hΛx]
  have hpw : 0 ≤ pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := by
    unfold pairWeight
    exact mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _)
  have h2k : (2 : ℝ) ^ (p + q) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hpq
  have hn0 := norm_nonneg (iteratedFDeriv ℝ (p + q) (Function.uncurry F) (X + (1 / 2 : ℝ) • z, X - (1 / 2 : ℝ) • z))
  calc _ ≤ ‖iteratedFDeriv ℝ (p + q) (Function.uncurry F) (X + (1 / 2 : ℝ) • z, X - (1 / 2 : ℝ) • z)‖ * 2 ^ (p + q) :=
        mul_le_mul_of_nonneg_left hprod hn0
    _ ≤ (B * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z)) * 2 ^ k :=
        mul_le_mul hb h2k (by positivity) (mul_nonneg hB hpw)
    _ = 2 ^ k * B * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) * 1 := by ring
    _ ≤ _ := by
        have hs : (0 : ℝ) ≤ (min 1 ‖z‖) ^ (-(σ + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ b := by
          apply mul_nonneg
          · exact Real.rpow_nonneg (le_min zero_le_one (norm_nonneg _)) _
          · positivity
        have h2kB : 0 ≤ 2 ^ k * B * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) :=
          mul_nonneg (mul_nonneg (by positivity) hB) hpw
        nlinarith

end HRS.MS.R26T8A
