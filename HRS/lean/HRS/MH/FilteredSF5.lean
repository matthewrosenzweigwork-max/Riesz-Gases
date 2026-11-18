import HRS.MH.FilteredSF4
import HRS.MH.FilteredSF1
import HRS.Main.GFB3Aux4

/-!
# Packet SF5 `sf5_F_props_L` (the trace-duality test function is `C^{2L}` with `|Δ^L F| ≤ KΔ`)

Statement copied verbatim from `HRS/MH/FilteredSpec.lean` (namespace `HRS.MH.Filtered` there, `HRS.MH.FilteredP` here).
Route: copy of `gfb3_F_contDiff`/`gfb3_F_iter_bound` (`HRS/Main/GFB3Aux2.lean:151-197`) with `gfb3_bVec_contDiff` replaced by
`sf4_bVec_contDiff` and the constant `gfb3_Cn` by `sf5_Cn K`; then `sf1_laplacian_iter_le`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.FilteredP

open HRS HRS.Uniform HRS.GF

variable {d : ℕ}

/-- The Leibniz constant of the `i`-th derivative of `F_B / ‖B‖`, in terms of the bounds `K` of `bVec`. -/
def sf5_Cn (d : ℕ) (K : ℕ → ℝ) (i : ℕ) : ℝ :=
  d * ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * K l * K (i - l)

lemma sf5_Cn_nonneg (d : ℕ) {K : ℕ → ℝ} (hK : ∀ i, 0 ≤ K i) (i : ℕ) : 0 ≤ sf5_Cn d K i :=
  mul_nonneg (Nat.cast_nonneg d) (Finset.sum_nonneg fun l _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hK _)) (hK _))

lemma sf5_F_iter_bound (n : ℕ) {γ : ℝ} {K : ℕ → ℝ}
    (hcd : ∀ j : Fin d, ContDiff ℝ n (fun y : Euc d => bVec γ j (Torus.mk y)))
    (hK : ∀ j : Fin d, ∀ i : ℕ, i ≤ n → ∀ y : Euc d,
      ‖iteratedFDeriv ℝ i (fun y : Euc d => bVec γ j (Torus.mk y)) y‖ ≤ K i)
    (B : NegSobolev d γ →L[ℝ] NegSobolev d γ →L[ℝ] ℝ) (i : ℕ) (hi : i ≤ n) (y : Euc d) :
    ‖iteratedFDeriv ℝ i (Torus.lift (gfb3_F γ B)) y‖ ≤ ‖B‖ * sf5_Cn d K i := by
  rw [gfb3_lift_F]
  have hcd' : ∀ j ∈ (Finset.univ : Finset (Fin d)), ContDiff ℝ i
      (fun y : Euc d => B (bVec γ j (Torus.mk y)) (bVec γ j (Torus.mk y))) := by
    intro j _
    exact (B.isBoundedBilinearMap.contDiff.comp ((hcd j).prodMk (hcd j))).of_le (by exact_mod_cast hi)
  rw [iteratedFDeriv_sum hcd']
  simp only [Finset.sum_apply]
  refine (norm_sum_le _ _).trans ?_
  have hj : ∀ j : Fin d, ‖iteratedFDeriv ℝ i (fun y : Euc d => B (bVec γ j (Torus.mk y))
      (bVec γ j (Torus.mk y))) y‖ ≤ ‖B‖ * ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * K l * K (i - l) := by
    intro j
    have hb := B.norm_iteratedFDeriv_le_of_bilinear (hcd j) (hcd j) y (n := i) (by exact_mod_cast hi)
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg B))
    refine Finset.sum_le_sum fun l hl => ?_
    have hl' : l ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have h1 := hK j l (hl'.trans hi) y
    have h2 := hK j (i - l) ((Nat.sub_le _ _).trans hi) y
    have hch : (0 : ℝ) ≤ (i.choose l : ℝ) := Nat.cast_nonneg _
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hch) h2 (norm_nonneg _)
      (mul_nonneg hch ((norm_nonneg _).trans h1))
  calc _ ≤ ∑ _j : Fin d, ‖B‖ * ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * K l * K (i - l) :=
        Finset.sum_le_sum fun j _ => hj j
    _ = ‖B‖ * sf5_Cn d K i := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sf5_Cn]
        ring

theorem sf5_F_props_L (hd1 : 1 ≤ d) (L : ℕ) (hL : 1 ≤ L) {γ : ℝ} (hγ : (d : ℝ) / 2 + 1 + 2 * (L : ℝ) < γ) :
    ∃ KΔ : ℝ, 0 ≤ KΔ ∧ ∀ B : NegSobolev d γ →L[ℝ] NegSobolev d γ →L[ℝ] ℝ, ‖B‖ ≤ 1 →
      Torus.IsCk (2 * L : ℕ) (gfb3_F γ B) ∧
      ∀ x, |((Torus.laplacian : (Torus d → ℝ) → Torus d → ℝ)^[L] (gfb3_F γ B)) x| ≤ KΔ := by
  have hγ' : (d : ℝ) / 2 + ((2 * L : ℕ) : ℝ) + 1 < γ := by push_cast; linarith
  obtain ⟨K, hK0, hK⟩ := sf4_bVec_contDiff (d := d) (2 * L) hγ'
  have hcd : ∀ j : Fin d, ContDiff ℝ ((2 * L : ℕ) : WithTop ℕ∞) (fun y : Euc d => bVec γ j (Torus.mk y)) :=
    fun j => (hK j).1
  have hKb : ∀ j : Fin d, ∀ i : ℕ, i ≤ 2 * L → ∀ y : Euc d,
      ‖iteratedFDeriv ℝ i (fun y : Euc d => bVec γ j (Torus.mk y)) y‖ ≤ K i := fun j => (hK j).2
  refine ⟨(d : ℝ) ^ L * ∑ j ∈ Finset.range (2 * L + 1), sf5_Cn d K j, ?_, ?_⟩
  · exact mul_nonneg (pow_nonneg (Nat.cast_nonneg d) L)
      (Finset.sum_nonneg fun j _ => sf5_Cn_nonneg d hK0 j)
  intro B hB
  have hCk : Torus.IsCk (2 * L : ℕ) (gfb3_F γ B) := by
    unfold Torus.IsCk
    rw [gfb3_lift_F]
    refine ContDiff.sum fun j _ => ?_
    exact B.isBoundedBilinearMap.contDiff.comp ((hcd j).prodMk (hcd j))
  refine ⟨hCk, fun x => ?_⟩
  refine (sf1_laplacian_iter_le L hCk x).trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg (Nat.cast_nonneg d) L))
  unfold Torus.cbNorm
  refine Finset.sum_le_sum fun j hj => ?_
  have hj' : j ≤ 2 * L := by have := Finset.mem_range.mp hj; omega
  refine ciSup_le fun y => ?_
  exact (sf5_F_iter_bound (2 * L) hcd hKb B j hj' y).trans
    (by nlinarith [sf5_Cn_nonneg d hK0 j, norm_nonneg B])

end HRS.MH.FilteredP
