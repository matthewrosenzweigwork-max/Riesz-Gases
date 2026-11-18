import HRS.MS.R26T8AContInt
import HRS.MS.R26T8AP11a
import HRS.MS.WadAux1

/-!
# S8.2 T8A P11f (part 4): jets of products of an affine-pulled kernel and a `snd`-pulled factor
`r26t8a_f4_jet_G`: `‖D^n (p ↦ K(p.1-p.2-v) * g p.2) p‖ ≤ 4^n BK Bg` if `‖D^j K‖ ≤ BK` and `‖D^m g (p.2)‖ ≤ Bg` for `j, m ≤ n`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_f4_jet_kernel {K : Euc d → ℝ} {i : ℕ} (hK : ContDiff ℝ (i : WithTop ℕ∞) K) {B : ℝ}
    (hB : ∀ u, ‖iteratedFDeriv ℝ i K u‖ ≤ B) (v : Euc d) (p : Euc d × Euc d) :
    ‖iteratedFDeriv ℝ i (fun q : Euc d × Euc d => K (q.1 - q.2 - v)) p‖ ≤ B * 2 ^ i := by
  set ℓ : (Euc d × Euc d) →L[ℝ] Euc d :=
    ContinuousLinearMap.fst ℝ (Euc d) (Euc d) - ContinuousLinearMap.snd ℝ (Euc d) (Euc d) with hℓ
  have hℓn : ‖ℓ‖ ≤ 2 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun w => ?_
    simp only [hℓ, ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
    have h1 : ‖w.1‖ ≤ ‖w‖ := norm_fst_le w
    have h2 : ‖w.2‖ ≤ ‖w‖ := norm_snd_le w
    have := norm_sub_le w.1 w.2
    linarith
  have hfun : (fun q : Euc d × Euc d => K (q.1 - q.2 - v)) = (fun w => K (w - v)) ∘ ℓ := by
    funext q; simp [hℓ]
  have hKs : ContDiff ℝ (i : WithTop ℕ∞) (fun w => K (w - v)) := hK.comp (contDiff_id.sub contDiff_const)
  rw [hfun, ℓ.iteratedFDeriv_comp_right hKs p le_rfl, iteratedFDeriv_comp_sub]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _j : Fin i, ‖ℓ‖ ≤ 2 ^ i := by
    calc ∏ _j : Fin i, ‖ℓ‖ = ‖ℓ‖ ^ i := by simp
      _ ≤ 2 ^ i := pow_le_pow_left₀ (norm_nonneg _) hℓn _
  exact (mul_le_mul (hB _) hprod (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    ((norm_nonneg _).trans (hB 0)))

theorem r26t8a_f4_jet_snd {g : Euc d → ℝ} {m : ℕ} (hg : ContDiff ℝ (m : WithTop ℕ∞) g) (p : Euc d × Euc d) :
    ‖iteratedFDeriv ℝ m (fun q : Euc d × Euc d => g q.2) p‖ ≤ ‖iteratedFDeriv ℝ m g p.2‖ := by
  have hfun : (fun q : Euc d × Euc d => g q.2) = g ∘ (ContinuousLinearMap.snd ℝ (Euc d) (Euc d)) := rfl
  rw [hfun, (ContinuousLinearMap.snd ℝ (Euc d) (Euc d)).iteratedFDeriv_comp_right hg p le_rfl]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hn : ‖ContinuousLinearMap.snd ℝ (Euc d) (Euc d)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by simpa using norm_snd_le w
  have hprod : ∏ _j : Fin m, ‖ContinuousLinearMap.snd ℝ (Euc d) (Euc d)‖ ≤ 1 := by
    calc ∏ _j : Fin m, ‖ContinuousLinearMap.snd ℝ (Euc d) (Euc d)‖
        = ‖ContinuousLinearMap.snd ℝ (Euc d) (Euc d)‖ ^ m := by simp
      _ ≤ 1 := pow_le_one₀ (norm_nonneg _) hn
  calc _ ≤ ‖iteratedFDeriv ℝ m g p.2‖ * 1 := mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = _ := mul_one _

theorem r26t8a_f4_jet_G {K g : Euc d → ℝ} {n : ℕ} (hK : ContDiff ℝ (n : WithTop ℕ∞) K)
    (hg : ContDiff ℝ (n : WithTop ℕ∞) g) {BK Bg : ℝ}
    (hBK : ∀ j ≤ n, ∀ u, ‖iteratedFDeriv ℝ j K u‖ ≤ BK) (v : Euc d) (p : Euc d × Euc d)
    (hBg : ∀ m ≤ n, ‖iteratedFDeriv ℝ m g p.2‖ ≤ Bg) :
    ‖iteratedFDeriv ℝ n (fun q : Euc d × Euc d => K (q.1 - q.2 - v) * g q.2) p‖ ≤ 4 ^ n * (BK * Bg) := by
  have hBK0 : 0 ≤ BK := (norm_nonneg _).trans (hBK 0 (Nat.zero_le _) 0)
  have hBg0 : 0 ≤ Bg := (norm_nonneg _).trans (hBg 0 (Nat.zero_le _))
  have hkc : ∀ j ≤ n, ContDiff ℝ (j : WithTop ℕ∞) K := fun j hj => hK.of_le (by exact_mod_cast hj)
  have hK2 : ContDiff ℝ (n : WithTop ℕ∞) (fun q : Euc d × Euc d => K (q.1 - q.2 - v)) :=
    hK.comp ((contDiff_fst.sub contDiff_snd).sub contDiff_const)
  have hg2 : ContDiff ℝ (n : WithTop ℕ∞) (fun q : Euc d × Euc d => g q.2) := hg.comp contDiff_snd
  refine (norm_iteratedFDeriv_mul_le hK2 hg2 p (n := n) le_rfl).trans ?_
  calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun q : Euc d × Euc d => K (q.1 - q.2 - v)) p‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun q : Euc d × Euc d => g q.2) p‖
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (BK * 2 ^ n) * Bg := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have h1 := r26t8a_f4_jet_kernel (hkc i hi') (hBK i hi') v p
        have h2 := (r26t8a_f4_jet_snd (hg.of_le (by exact_mod_cast Nat.sub_le n i)) p).trans
          (hBg (n - i) (Nat.sub_le n i))
        have h3 : (2 : ℝ) ^ i ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hi'
        have hch : (0 : ℝ) ≤ n.choose i := Nat.cast_nonneg _
        have h4 : ‖iteratedFDeriv ℝ i (fun q : Euc d × Euc d => K (q.1 - q.2 - v)) p‖ ≤ BK * 2 ^ n :=
          h1.trans (mul_le_mul_of_nonneg_left h3 hBK0)
        exact mul_le_mul (mul_le_mul_of_nonneg_left h4 hch) h2 (norm_nonneg _)
          (mul_nonneg hch (mul_nonneg hBK0 (by positivity)))
    _ = 2 ^ n * (BK * 2 ^ n) * Bg := by
        have : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) = 2 ^ n := by exact_mod_cast Nat.sum_range_choose n
        rw [← Finset.sum_mul, ← Finset.sum_mul, this]
    _ = 4 ^ n * (BK * Bg) := by
        have : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
        rw [this]; ring

end HRS.MS.R26T8A
