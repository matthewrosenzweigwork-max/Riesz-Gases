import HRS.MS.SA16ZE8
import HRS.MS.CzElemBAux2
import HRS.MS.LpDissConvex

/-!
# S.A.16 (SA16Z) E9: absorption of the unbounded top-order terms
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.BreakdownSA16

section E9
variable {d : ℕ} {s : ℝ}

/-- the dissipation of the tensor `W` weighted by `μ` -/
def sa16z_Diss (d : ℕ) (θ p : ℝ) (μ : Euc d → ℝ) {ι : Type*} [Fintype ι] (W : ι → 𝓢(Euc d, ℝ)) : ℝ :=
  (∫⁻ x, ENNReal.ofReal (μ x) * dissipationDensity d θ p (fun y i => W i y) x).toReal

theorem sa16z_IB_bound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) {p : ℝ} (hp : 2 ≤ p)
    (Λ : ℝ) (hΛ : 0 ≤ Λ) {ε : ℝ} (hε : 0 < ε) (cA cs : ℝ) (l : Fin d) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {μ φ : Euc d → ℝ} (hφ : IsCcInfty φ), ContDiff ℝ ∞ μ → (∀ x, 0 ≤ μ x) →
      sa16z_Cb (j + 2) Λ μ →
      ∫ x, sa16z_IBd cA cs μ φ p (s + 2 - d) l j x ≤
        ε * sa16z_Diss d (s + 2 - d) p μ (sa16z_Wt hφ j) +
          C * (1 + ((|cA| + |cs| * j) * Real.sqrt (2 * Λ)) ^ 2) * ∫ x, sa16sz_vn φ j x ^ p := by
  have hθ2 : s + 2 - (d : ℝ) < 2 := by linarith
  have hθ0 : 0 < s + 2 - (d : ℝ) := by linarith
  obtain ⟨C, hC⟩ := HRS.CZ.ElemB.lp_tensor_absorption_proof hd (s + 2 - d) p hθ1 hθ2 hp
    (fun u : Euc d => u l) (HRS.CZ.Asm15.asm15_isOddSmooth_coord l) Λ ε hε (Fin j → Fin d)
  obtain ⟨Cw, hCw0, hCw⟩ := sa16bd_weighted_leading hd (s + 2 - d) p hθ0 hθ2 hp (Fin j → Fin d)
  refine ⟨max C 0, le_max_right _ _, fun {μ φ} hφ hμ hpos hCb => ?_⟩
  have hCb2 : sa16z_Cb 2 Λ μ := sa16z_Cb_mono (by omega) hCb
  have hμΛ : ∀ x, μ x ≤ Λ := fun x => (le_abs_self _).trans (sa16z_Cb_abs (sa16z_Cb_mono (by omega) hCb) x)
  have hmem2 : HRS.MemCb 2 μ := sa16z_memCb hμ hCb2
  set Bb : ℝ := (|cA| + |cs| * j) * Real.sqrt (2 * Λ) with hBb
  have hB : ∀ (x : Euc d) (i k : Fin j → Fin d), |sa16z_Bm cA cs μ l j x i k| ≤ Bb :=
    fun x i k => sa16z_Bm_abs hμ hpos hΛ hCb2 cA cs l j x i k
  have habs := hC μ (fun x => sa16z_Bm cA cs μ l j x) Bb (fun x => ⟨hpos x, hμΛ x⟩) hB (sa16z_Wt hφ j)
  obtain ⟨hVint, -, hDfin, -⟩ := hCw μ hmem2 hpos (sa16z_Wt hφ j)
  have hI : ∀ x, sa16z_IBd cA cs μ φ p (s + 2 - d) l j x =
      vnorm (fun i => sa16z_Wt hφ j i x) ^ (p - 2) * ∑ i : Fin j → Fin d, sa16z_Wt hφ j i x *
        (Real.sqrt (μ x) * ∑ k : Fin j → Fin d, sa16z_Bm cA cs μ l j x i k *
          pvOdd d (s + 2 - d) (fun u : Euc d => u l) (fun y => sa16z_Wt hφ j k y) x) :=
    fun x => sa16z_IBd_eq hμ hpos hCb2 hφ cA cs p (s + 2 - d) l j x
  have hint : ∫ x, sa16z_IBd cA cs μ φ p (s + 2 - d) l j x = ∫ x, vnorm (fun i => sa16z_Wt hφ j i x) ^ (p - 2) *
      ∑ i : Fin j → Fin d, sa16z_Wt hφ j i x *
        (Real.sqrt (μ x) * ∑ k : Fin j → Fin d, sa16z_Bm cA cs μ l j x i k *
          pvOdd d (s + 2 - d) (fun u : Euc d => u l) (fun y => sa16z_Wt hφ j k y) x) :=
    integral_congr_ae (Eventually.of_forall hI)
  rw [hint]
  have hV : ∫⁻ x, ENNReal.ofReal (vnorm (fun i => sa16z_Wt hφ j i x) ^ p) =
      ENNReal.ofReal (∫ x, sa16sz_vn φ j x ^ p) := by
    exact (ofReal_integral_eq_lintegral_ofReal hVint
      (Eventually.of_forall fun x => Real.rpow_nonneg (Real.sqrt_nonneg _) _)).symm
  rw [hV] at habs
  have hfinR : ENNReal.ofReal ε * (∫⁻ x, ENNReal.ofReal (μ x) *
        dissipationDensity d (s + 2 - d) p (fun y i => sa16z_Wt hφ j i y) x) +
      ENNReal.ofReal (C * (1 + Bb ^ 2)) * ENNReal.ofReal (∫ x, sa16sz_vn φ j x ^ p) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hDfin.ne,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩
  have h2 := (ENNReal.ofReal_le_iff_le_toReal hfinR).1 habs
  refine (le_abs_self _).trans (h2.trans ?_)
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hDfin.ne)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hε.le, ENNReal.toReal_ofReal (integral_nonneg
      fun x => Real.rpow_nonneg (sa16sz_vn_nonneg φ j x) _)]
  unfold sa16z_Diss
  have hV0 : 0 ≤ ∫ x, sa16sz_vn φ j x ^ p := integral_nonneg fun x => Real.rpow_nonneg (sa16sz_vn_nonneg φ j x) _
  have hr : (ENNReal.ofReal (C * (1 + Bb ^ 2))).toReal ≤ max C 0 * (1 + Bb ^ 2) := by
    rw [ENNReal.toReal_ofReal' ]
    rcases le_total 0 (C * (1 + Bb ^ 2)) with h | h
    · rw [max_eq_left h]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · rw [max_eq_right h]; exact mul_nonneg (le_max_right _ _) (by positivity)
  gcongr

end E9

end HRS.Whole.AppendixA.Phase2SA16R
