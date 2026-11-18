import HRS.MS.SA16Y3Op2
import HRS.MS.SA16Y3Pair1

/-!
# S.A.16 (SA16Y3) Hk5: the Hilbert pairing of the jet energy with `P^A_μ` on `C_c^∞` and its extension (packet P7, Hilbert corner)

`sa16y3_hpair`: `|∫ sa16sz_dens m 2 φ (P^A_μ φ)| ≤ C AB Λ ∑_{k ≤ m} ∫ |D^kφ|²`.
`sa16y3_hdissA`: for a bounded `T^A` extending `P^A_μ`: `d(jetEnergy_m)_{ι²G}(-T^A G) ≤ 2 C AB Λ jetEnergy_m(ι²G)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Hk5
variable {d : ℕ} {s : ℝ}

lemma sa16y3_dens_two (m : ℕ) (φ ψ : Euc d → ℝ) (x : Euc d) :
    sa16sz_dens m 2 φ ψ x = ∑ j : Fin (m + 1), ∑ idx : Fin (j : ℕ) → Fin d,
      partialDeriv idx φ x * partialDeriv idx ψ x := by
  unfold sa16sz_dens
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

theorem sa16y3_hpair (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {A : Matrix (Fin d) (Fin d) ℝ} {AB : ℝ}, 0 ≤ AB → (∀ a b, |A a b| ≤ AB) →
      A.transpose = -A → ∀ {μ φ : Euc d → ℝ}, ContDiff ℝ ∞ μ → IsCcInfty φ → ∀ {Λ : ℝ}, 0 ≤ Λ →
      sa16z_Cb (m + 2) Λ μ →
      |∫ x, sa16sz_dens m 2 φ (sa16y3_PA s A μ φ) x| ≤
        C * (AB * Λ) * ∑ k : Fin (m + 1), ∫ x, sa16sz_vn φ k x ^ (2 : ℝ) := by
  choose Cj hCj0 hCj using fun j : ℕ => sa16y3_hilbert_term hd hs0 hsd hθ1 j
  refine ⟨∑ j ∈ Finset.range (m + 1), (d : ℝ) ^ j * Cj j,
    Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (hCj0 j), ?_⟩
  intro A AB hAB hAab hA μ φ hμ hφ Λ hΛ hCb
  have hΛA : 0 ≤ AB * Λ := mul_nonneg hAB hΛ
  have hvnMem : ∀ k, MemLp (sa16sz_vn φ k) (ENNReal.ofReal 2) volume := fun k =>
    (sa16sz_vn_cont φ hφ.1 k).memLp_of_hasCompactSupport (sa16sz_vn_cs hφ k)
  have hEk : ∀ k : ℕ, ∫ x, sa16sz_vn φ k x ^ (2 : ℝ) = sa16y3_ee φ k ^ 2 := fun k => by
    unfold sa16y3_ee
    rw [← sa16y3_N2_sq (hvnMem k)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [Real.rpow_two]
  have hsumk : ∑ k : Fin (m + 1), ∫ x, sa16sz_vn φ k x ^ (2 : ℝ) = ∑ k ∈ Finset.range (m + 1), sa16y3_ee φ k ^ 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun k => ∫ x, sa16sz_vn φ k x ^ (2 : ℝ)) (m + 1)]
    exact Finset.sum_congr rfl fun k _ => hEk k
  rw [hsumk]
  set Em : ℝ := ∑ k ∈ Finset.range (m + 1), sa16y3_ee φ k ^ 2 with hEm
  have hPs : ContDiff ℝ ∞ (sa16y3_PA s A μ φ) := sa16y3_PA_smooth hs0 hsd A hμ hφ
  have hint : ∀ (j : ℕ) (idx : Fin j → Fin d),
      Integrable (fun x => partialDeriv idx φ x * partialDeriv idx (sa16y3_PA s A μ φ) x) := fun j idx =>
    ((sa16s_cc_partialDeriv hφ idx).1.continuous.mul (sa16j_pd_smooth hPs idx).continuous).integrable_of_hasCompactSupport
      (sa16s_cc_partialDeriv hφ idx).2.mul_right
  have hdens : ∫ x, sa16sz_dens m 2 φ (sa16y3_PA s A μ φ) x = ∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d,
      ∫ x, partialDeriv idx φ x * partialDeriv idx (sa16y3_PA s A μ φ) x := by
    simp_rw [sa16y3_dens_two]
    have : ∀ x, ∑ j : Fin (m + 1), ∑ idx : Fin (j : ℕ) → Fin d,
        partialDeriv idx φ x * partialDeriv idx (sa16y3_PA s A μ φ) x =
        ∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d,
          partialDeriv idx φ x * partialDeriv idx (sa16y3_PA s A μ φ) x := fun x =>
      Fin.sum_univ_eq_sum_range (fun j => ∑ idx : Fin j → Fin d,
        partialDeriv idx φ x * partialDeriv idx (sa16y3_PA s A μ φ) x) (m + 1)
    simp_rw [this]
    rw [integral_finsetSum _ (fun j _ => integrable_finset_sum _ fun idx _ => hint j idx)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ (fun idx _ => hint j idx)]
  rw [hdens]
  have hEmono : ∀ j ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (j + 1), sa16y3_ee φ k ^ 2 ≤ Em := fun j hj =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by have := Finset.mem_range.1 hj; omega))
      fun k _ _ => sq_nonneg _
  have hEm0 : 0 ≤ Em := Finset.sum_nonneg fun k _ => sq_nonneg _
  calc |∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d,
        ∫ x, partialDeriv idx φ x * partialDeriv idx (sa16y3_PA s A μ φ) x|
      ≤ ∑ j ∈ Finset.range (m + 1), (d : ℝ) ^ j * (Cj j * AB * Λ * Em) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
        have hjm : j ≤ m := by have := Finset.mem_range.1 hj; omega
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        have h1 : ∀ idx : Fin j → Fin d,
            |∫ x, partialDeriv idx φ x * partialDeriv idx (sa16y3_PA s A μ φ) x| ≤ Cj j * AB * Λ * Em :=
          fun idx => (hCj j hA hAB hAab hμ hφ hΛ (sa16z_Cb_mono (by omega) hCb) idx).trans
            (mul_le_mul_of_nonneg_left (hEmono j hj) (mul_nonneg (mul_nonneg (hCj0 j) hAB) hΛ))
        refine (Finset.sum_le_sum fun idx _ => h1 idx).trans (le_of_eq ?_)
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring
    _ = (∑ j ∈ Finset.range (m + 1), (d : ℝ) ^ j * Cj j) * (AB * Λ) * Em := by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring

end Hk5

end HRS.Whole.AppendixA.Phase2SA16R
