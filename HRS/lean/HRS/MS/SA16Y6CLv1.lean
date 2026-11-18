import HRS.MS.SA16Y6CEr1
import HRS.MS.SA16Y6C1
import HRS.MS.SA16Y5Lv1

/-! # SA16Y6 critical-case copy of SA16Y5Lv1 (s = d-1) -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q HRS.Whole.AppendixA.BreakdownSA16

section Lv1
variable {d : ℕ} {s : ℝ}
set_option maxHeartbeats 1600000 in
theorem sa16y6c_level (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hs1 : s = (d : ℝ) - 1)
    (hθ0 : 0 < s + 2 - d) {p : ℝ} (hp : 2 ≤ p) (hfar : (d : ℝ) < p * (s + 1)) {Wd : ℝ} (hWd : 0 ≤ Wd)
    (Λ : ℝ) (hΛ : 0 ≤ Λ) (j : ℕ) :
    ∃ Cj : ℝ, 0 ≤ Cj ∧ ∀ {μ φ : Euc d → ℝ}, HRS.S16Frac.S16FracCb μ → (∀ x, 0 ≤ μ x) → IsCcInfty φ →
      sa16z_Cb 2 Λ μ → sa16y5_Dec (j + 2) Wd μ →
      ∫ x, sa16sz_vn φ j x ^ (p - 2) * ∑ idx : Fin j → Fin d, partialDeriv idx φ x *
          partialDeriv idx (sa16z_P s μ φ) x ≤
        Cj * ∑ k ∈ Finset.range (j + 1), ∫ x, sa16sz_vn φ k x ^ p := by
  have hθ2 : s + 2 - (d : ℝ) < 2 := by linarith
  have hp0 : 0 < p := by linarith
  obtain ⟨c, hc, hErr⟩ := sa16y6c_Err_bound hd hs0 hsd hs1 hθ0 hp hfar hWd Λ hΛ
  obtain ⟨K, hK0, hK⟩ := hErr j
  obtain ⟨Cw, hCw0, hCw⟩ := sa16bd_weighted_leading hd (s + 2 - d) p hθ0 hθ2 hp (Fin j → Fin d)
  have hcc : 0 < sa16bd_convexityConst p := by unfold sa16bd_convexityConst; positivity
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set N : ℝ := (d : ℝ) ^ j with hN
  have hNpos : 0 < N := by positivity
  refine ⟨c * Cw * (3 * Λ) + N * ((p - 1) / p) + (1 / p) * N * (K ^ p * ((j : ℝ) + 1) ^ (p - 1)),
    by
      have h1 : 0 ≤ c * Cw * (3 * Λ) := by positivity
      have h3 : 0 ≤ N * ((p - 1) / p) := mul_nonneg hNpos.le (div_nonneg (by linarith) hp0.le)
      have h4 : 0 ≤ (1 / p) * N * (K ^ p * ((j : ℝ) + 1) ^ (p - 1)) :=
        mul_nonneg (mul_nonneg (by positivity) hNpos.le)
          (mul_nonneg (Real.rpow_nonneg hK0 _) (Real.rpow_nonneg (by positivity) _))
      linarith,
    fun {μ φ} hμ hpos hφ hCb hdec => ?_⟩
  have hμs : ContDiff ℝ ∞ μ := hμ.1
  have hmem2 : HRS.MemCb 2 μ := sa16z_memCb hμs hCb
  have hcb2 : HRS.cbNorm 2 μ ≤ 3 * Λ := by
    have := sa16z_cbNorm_le hCb; push_cast at this; linarith
  set Wt := sa16z_Wt hφ j with hWt
  obtain ⟨hVint, hAint, hDfin, hlead⟩ := hCw μ hmem2 hpos Wt
  set D : ℝ := sa16z_Diss d (s + 2 - d) p μ Wt with hD
  have hD0 : 0 ≤ D := ENNReal.toReal_nonneg
  set V : ℕ → ℝ := fun k => ∫ x, sa16sz_vn φ k x ^ p with hV
  have hV0 : ∀ k, 0 ≤ V k := fun k => integral_nonneg fun x => Real.rpow_nonneg (sa16sz_vn_nonneg φ k x) _
  have hVj : V j ≤ ∑ k ∈ Finset.range (j + 1), V k :=
    Finset.single_le_sum (f := V) (fun k _ => hV0 k) (Finset.mem_range.2 (by omega))
  have hSV : 0 ≤ ∑ k ∈ Finset.range (j + 1), V k := Finset.sum_nonneg fun k _ => hV0 k
  set I : Euc d → ℝ := fun x => sa16sz_vn φ j x ^ (p - 2) * ∑ idx : Fin j → Fin d, partialDeriv idx φ x *
    partialDeriv idx (sa16z_P s μ φ) x with hI
  set IA : Euc d → ℝ := fun x => μ x * sa16sz_vn φ j x ^ (p - 2) * ∑ idx : Fin j → Fin d, partialDeriv idx φ x *
    fracLap d (s + 2 - d) (partialDeriv idx φ) x with hIA
  set IE : Euc d → ℝ := fun x => sa16sz_vn φ j x ^ (p - 2) * ∑ idx : Fin j → Fin d, partialDeriv idx φ x *
    (partialDeriv idx (sa16z_P s μ φ) x + c * μ x * fracLap d (s + 2 - d) (partialDeriv idx φ) x) with hIE
  have hIAint : Integrable IA := hAint
  have hIi : Integrable I := sa16z_I_int hs0 hsd hμs hφ hp j
  have hsp : ∀ x, I x = -c * IA x + IE x := by
    intro x
    simp only [hI, hIA, hIE]
    have : ∑ idx : Fin j → Fin d, partialDeriv idx φ x * (partialDeriv idx (sa16z_P s μ φ) x +
        c * μ x * fracLap d (s + 2 - d) (partialDeriv idx φ) x) =
        ∑ idx : Fin j → Fin d, partialDeriv idx φ x * partialDeriv idx (sa16z_P s μ φ) x +
          c * μ x * ∑ idx : Fin j → Fin d, partialDeriv idx φ x * fracLap d (s + 2 - d) (partialDeriv idx φ) x := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun idx _ => by ring
    rw [this]; ring
  have hIEint : Integrable IE := by
    have : IE = fun x => I x - (-c * IA x) := funext fun x => by rw [hsp x]; ring
    rw [this]
    exact hIi.sub (hIAint.const_mul (-c))
  have hint_eq : ∫ x, I x = -c * (∫ x, IA x) + (∫ x, IE x) := by
    have : (fun x => I x) = fun x => -c * IA x + IE x := funext hsp
    rw [this, integral_add (hIAint.const_mul (-c)) hIEint, integral_const_mul]
  -- leading term
  have hA : -c * ∫ x, IA x ≤ c * Cw * (3 * Λ) * V j := by
    have h1 : -c * ∫ x, IA x ≤ -c * sa16bd_convexityConst p * D + c * Cw * HRS.cbNorm 2 μ * V j :=
      hlead c hc.le
    have h2 : -c * sa16bd_convexityConst p * D ≤ 0 := by
      have : 0 ≤ c * sa16bd_convexityConst p * D := by positivity
      linarith
    have h3 : c * Cw * HRS.cbNorm 2 μ * V j ≤ c * Cw * (3 * Λ) * V j :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcb2 (mul_nonneg hc.le hCw0)) (hV0 j)
    linarith
  -- the error pairing
  have hSfin : sa16z_S p φ j ≠ ⊤ := by
    unfold sa16z_S
    exact (ENNReal.sum_lt_top.2 fun k _ => sa16z_JJ_lt_top hφ k).ne
  have hErr' : ∀ idx : Fin j → Fin d, Integrable (fun x => |partialDeriv idx (sa16z_P s μ φ) x +
        c * μ x * fracLap d (s + 2 - d) (partialDeriv idx φ) x| ^ p) ∧
      ∫ x, |partialDeriv idx (sa16z_P s μ φ) x + c * μ x * fracLap d (s + 2 - d) (partialDeriv idx φ) x| ^ p ≤
        (K * (sa16z_S p φ j).toReal) ^ p := by
    intro idx
    have hb := hK hμ hφ hCb hdec idx
    have hne : ENNReal.ofReal K * sa16z_S p φ j ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSfin
    have hPs : ContDiff ℝ ∞ (sa16z_P s μ φ) := sa16z_P_smooth hs0 hsd hμs hφ
    have hfl := sa16bd_fracLap_aesm hd hθ0 hθ2 (sa16z_Wt hφ j idx)
    have hae : AEStronglyMeasurable (fun x => partialDeriv idx (sa16z_P s μ φ) x +
        c * μ x * fracLap d (s + 2 - d) (partialDeriv idx φ) x) volume :=
      (sa16j_pd_smooth hPs idx).continuous.aestronglyMeasurable.add
        ((continuous_const.mul hμs.continuous).aestronglyMeasurable.mul hfl)
    have := sa16z_rpow_int_of_eLpNorm hae hp0 hne hb
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0] at this
    exact this
  set h : Euc d → ℝ := fun x => ∑ idx : Fin j → Fin d, (((p - 1) / p) * sa16sz_vn φ j x ^ p +
    (1 / p) * |partialDeriv idx (sa16z_P s μ φ) x + c * μ x * fracLap d (s + 2 - d) (partialDeriv idx φ) x| ^ p)
    with hh
  have hyoung : ∀ x, IE x ≤ h x := fun x =>
    sa16z_young_pair hp (fun idx => partialDeriv idx φ x) (fun idx => partialDeriv idx (sa16z_P s μ φ) x +
      c * μ x * fracLap d (s + 2 - d) (partialDeriv idx φ) x)
  have hh0 : ∀ x, 0 ≤ h x := fun x => Finset.sum_nonneg fun idx _ => add_nonneg
    (mul_nonneg (div_nonneg (by linarith) hp0.le) (Real.rpow_nonneg (sa16sz_vn_nonneg φ j x) _))
    (mul_nonneg (by positivity) (Real.rpow_nonneg (abs_nonneg _) _))
  have hVint' : Integrable (fun x => sa16sz_vn φ j x ^ p) := hVint
  have hInt : ∀ idx : Fin j → Fin d, Integrable (fun x => ((p - 1) / p) * sa16sz_vn φ j x ^ p +
      (1 / p) * |partialDeriv idx (sa16z_P s μ φ) x + c * μ x * fracLap d (s + 2 - d) (partialDeriv idx φ) x| ^ p) :=
    fun idx => (hVint'.const_mul _).add ((hErr' idx).1.const_mul _)
  have hhint : Integrable h := integrable_finsetSum _ fun idx _ => hInt idx
  have hE1 : ∫ x, IE x ≤ ∫ x, h x := sa16z_integral_le_of_le hyoung hhint hh0
  have hcard : (Fintype.card (Fin j → Fin d) : ℝ) = N := by simp [hN]
  have hE2 : ∫ x, h x ≤ N * ((p - 1) / p) * V j +
      (1 / p) * N * (K ^ p * ((sa16z_S p φ j).toReal) ^ p) := by
    have e : ∫ x, h x = ∑ idx : Fin j → Fin d, ((((p - 1) / p) * V j) +
        (1 / p) * ∫ x, |partialDeriv idx (sa16z_P s μ φ) x + c * μ x * fracLap d (s + 2 - d) (partialDeriv idx φ) x| ^ p) := by
      simp only [hh]
      rw [integral_finsetSum _ fun idx _ => hInt idx]
      refine Finset.sum_congr rfl fun idx _ => ?_
      rw [integral_add (hVint'.const_mul _) ((hErr' idx).1.const_mul _), integral_const_mul, integral_const_mul]
    rw [e]
    calc ∑ idx : Fin j → Fin d, ((((p - 1) / p) * V j) + (1 / p) * ∫ x, |partialDeriv idx (sa16z_P s μ φ) x +
          c * μ x * fracLap d (s + 2 - d) (partialDeriv idx φ) x| ^ p)
        ≤ ∑ idx : Fin j → Fin d, ((((p - 1) / p) * V j) + (1 / p) * (K * (sa16z_S p φ j).toReal) ^ p) :=
          Finset.sum_le_sum fun idx _ => by
            have := (hErr' idx).2
            have : 0 < 1 / p := by positivity
            nlinarith
      _ = N * ((p - 1) / p) * V j + (1 / p) * N * (K ^ p * ((sa16z_S p φ j).toReal) ^ p) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard,
            Real.mul_rpow hK0 ENNReal.toReal_nonneg]
          ring
  have hSp := sa16z_S_rpow_le hφ j (by linarith : 1 ≤ p)
  have hE3 : (1 / p) * N * (K ^ p * ((sa16z_S p φ j).toReal) ^ p) ≤
      (1 / p) * N * (K ^ p * ((j : ℝ) + 1) ^ (p - 1)) * ∑ k ∈ Finset.range (j + 1), V k := by
    have h0 : 0 ≤ (1 / p) * N * K ^ p := mul_nonneg (mul_nonneg (by positivity) hNpos.le)
      (Real.rpow_nonneg hK0 _)
    calc (1 / p) * N * (K ^ p * ((sa16z_S p φ j).toReal) ^ p)
        = ((1 / p) * N * K ^ p) * ((sa16z_S p φ j).toReal) ^ p := by ring
      _ ≤ ((1 / p) * N * K ^ p) * (((j : ℝ) + 1) ^ (p - 1) * ∑ k ∈ Finset.range (j + 1), V k) :=
          mul_le_mul_of_nonneg_left hSp h0
      _ = _ := by ring
  have hfinal : ∫ x, I x ≤ (c * Cw * (3 * Λ) + N * ((p - 1) / p) +
      (1 / p) * N * (K ^ p * ((j : ℝ) + 1) ^ (p - 1))) * ∑ k ∈ Finset.range (j + 1), V k := by
    rw [hint_eq]
    have hc1 : 0 ≤ c * Cw * (3 * Λ) := by positivity
    have hc3 : 0 ≤ N * ((p - 1) / p) := mul_nonneg hNpos.le (div_nonneg (by linarith) hp0.le)
    have e1 : c * Cw * (3 * Λ) * V j ≤ c * Cw * (3 * Λ) * ∑ k ∈ Finset.range (j + 1), V k :=
      mul_le_mul_of_nonneg_left hVj hc1
    have e3 : N * ((p - 1) / p) * V j ≤ N * ((p - 1) / p) * ∑ k ∈ Finset.range (j + 1), V k :=
      mul_le_mul_of_nonneg_left hVj hc3
    nlinarith [hA, hE1, hE2, hE3, e1, e3]
  exact hfinal

end Lv1

end HRS.Whole.AppendixA.Phase2SA16R
