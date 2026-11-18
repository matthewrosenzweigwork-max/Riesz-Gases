import HRS.MS.S21H2_S03
import HRS.MS.Comm

/-!
# S21L S08 -- `r26t3_static_kernel_bounds` (R26-T3.S08): commutator and `A`-entry derivative bounds

Contract of packet R26-T3.S08 (`origin/pro/fine-breakdown`), statement verbatim.  Route: `v_j` has `‖Dv_j‖ ≤ C n_j` (`StaticTransport.bounds`,
`n_j = ‖q_j‖_{C_b^J}`), hence is globally Lipschitz with that constant; the commutator kernel of a Lipschitz field with constant `Λ` is a bounded
pair kernel with `B = max(s,1) Λ` (merged `HRS.MS.Comm`; at `s = 0` the bound `|h| ≤ Λ` suffices because `rieszWeight 0 ≥ 0`); the
`A`-entry `⟪v_j, ∇q_k⟫` is bounded through order two by the Leibniz rule for the bilinear form `⟪·,·⟫` (`‖D^i(∇q)‖ = ‖D^{i+1}q‖`), the sum of the
binomial coefficients being `2^i ≤ 4`.  Helpers carry the prefix `s21l_s08_`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T3

open HRS HRS.Whole

theorem s21l_s08_weight_nonneg {d : ℕ} (s : ℝ) (z : Euc d) : 0 ≤ rieszWeight s z := by
  unfold rieszWeight
  split_ifs
  · exact le_max_right _ _
  · exact Real.rpow_nonneg (norm_nonneg _) _

theorem s21l_s08_comm_bounded {d : ℕ} (s : ℝ) (hs0 : 0 ≤ s) (Λ : ℝ≥0) (v : Euc d → Euc d)
    (hv : LipschitzWith Λ v) : IsBoundedPairKernel s (max s 1 * Λ) (commutatorKernel d s v) := by
  have hΛ0 : (0 : ℝ) ≤ (Λ : ℝ) := NNReal.coe_nonneg Λ
  rcases hs0.eq_or_lt with h0 | hpos
  · subst h0
    refine ⟨HRS.MS.Comm.comm_meas (s := 0) v hv.continuous.measurable, HRS.MS.Comm.comm_symm (s := 0) v,
      fun x y hxy => ?_⟩
    have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hzpos : 0 < ‖x - y‖ := norm_pos_iff.mpr hz
    have hG : ‖rieszKernelGrad d 0 (x - y)‖ = ‖x - y‖⁻¹ := by
      rw [movtr_rieszKernelGrad_norm 0 le_rfl hz]
      norm_num [movtr_sigma, Real.rpow_neg_one]
    have key : |commutatorKernel d 0 v x y| ≤ (Λ : ℝ) := by
      unfold commutatorKernel
      calc |inner ℝ (v x - v y) (rieszKernelGrad d 0 (x - y))|
          ≤ ‖v x - v y‖ * ‖rieszKernelGrad d 0 (x - y)‖ := abs_real_inner_le_norm _ _
        _ ≤ ((Λ : ℝ) * ‖x - y‖) * ‖x - y‖⁻¹ :=
            mul_le_mul (HRS.MS.Comm.comm_lip hv x y) hG.le (norm_nonneg _) (by positivity)
        _ = (Λ : ℝ) := by rw [mul_assoc, mul_inv_cancel₀ hzpos.ne', mul_one]
    have hw := s21l_s08_weight_nonneg (d := d) 0 (x - y)
    have hm : max (0 : ℝ) 1 = 1 := max_eq_right zero_le_one
    rw [hm]
    nlinarith [mul_nonneg hΛ0 hw]
  · have h1 := HRS.MS.Comm.commutatorKernel_isBounded_proof hpos Λ v hv
    refine ⟨h1.measurable, h1.symm, fun x y hxy => (h1.bound x y hxy).trans ?_⟩
    have hw := s21l_s08_weight_nonneg (d := d) s (x - y)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hΛ0) (by linarith)

theorem r26t3_static_kernel_bounds {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    {q : ℕ → Euc p.d → ℝ} (V : StaticTransport R q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j k : ℕ,
      IsBoundedPairKernel p.s (C*cbNorm (r26t3_J p.d) (q j)) (r26t3_h V j) ∧
      MemCb 2 (r26t3_Aentry V j k) ∧
      cbNorm 2 (r26t3_Aentry V j k) ≤
        C*cbNorm (r26t3_J p.d) (q j)*cbNorm (r26t3_J p.d) (q k) := by
  have hk : 3 ≤ r26t3_k p.d := by simp only [r26t3_k]; omega
  have hJ : 3 ≤ r26t3_J p.d := by simp only [r26t3_J]; omega
  have hc0 : 0 ≤ V.C := V.Cpos
  have hm1 : (1 : ℝ) ≤ max p.s 1 := le_max_right _ _
  refine ⟨12 * max p.s 1 * V.C, by positivity, fun j k => ?_⟩
  have hnj : 0 ≤ cbNorm (r26t3_J p.d) (q j) := s21h2_s03_cbNorm_nonneg _
  have hnk : 0 ≤ cbNorm (r26t3_J p.d) (q k) := s21h2_s03_cbNorm_nonneg _
  have hv := V.bounds j
  set nj := cbNorm (r26t3_J p.d) (q j) with hnjdef
  set nk := cbNorm (r26t3_J p.d) (q k) with hnkdef
  have hq : ContDiff ℝ ((r26t3_J p.d : ℕ) : WithTop ℕ∞) (q k) := (V.summable.1 k).1
  -- (1) the commutator kernel
  have hd : Differentiable ℝ (V.v j) := hv.1.differentiable (by norm_cast; omega)
  have hf1 : ∀ x, ‖fderiv ℝ (V.v j) x‖ ≤ V.C * nj := fun x => by
    rw [← norm_iteratedFDeriv_one]
    exact hv.2 1 (by omega) x
  have hL : LipschitzWith (V.C * nj).toNNReal (V.v j) :=
    lipschitzWith_of_nnnorm_fderiv_le hd (fun x => by
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact (hf1 x).trans (Real.le_coe_toNNReal _))
  have hK := s21l_s08_comm_bounded p.s p.hs0 _ _ hL
  have hcoe : (((V.C * nj).toNNReal : ℝ≥0) : ℝ) = V.C * nj := Real.coe_toNNReal _ (mul_nonneg hc0 hnj)
  rw [hcoe] at hK
  have hK' : IsBoundedPairKernel p.s ((12 * max p.s 1 * V.C) * nj) (r26t3_h V j) := by
    refine ⟨hK.measurable, hK.symm, fun x y hxy => (hK.bound x y hxy).trans ?_⟩
    have hw := s21l_s08_weight_nonneg (d := p.d) p.s (x - y)
    have hle : max p.s 1 * (V.C * nj) ≤ (12 * max p.s 1 * V.C) * nj := by nlinarith [mul_nonneg hc0 hnj, mul_nonneg (mul_nonneg hc0 hnj) (by linarith : (0 : ℝ) ≤ max p.s 1)]
    exact mul_le_mul_of_nonneg_right hle (by linarith)
  -- (2) the `A`-entry
  have hg2 : ContDiff ℝ 2 (gradient (q k)) := by
    have := s21h2_s03_grad_cd (d := p.d) (j := 2) (hq.of_le (by norm_cast))
    exact this
  have hv2 : ContDiff ℝ 2 (V.v j) := hv.1.of_le (by norm_cast; omega)
  have hA : r26t3_Aentry V j k = fun y => (innerSL ℝ : Euc p.d →L[ℝ] Euc p.d →L[ℝ] ℝ) (V.v j y) (gradient (q k) y) := by
    funext y; simp [r26t3_Aentry]
  have hcd : ContDiff ℝ 2 (r26t3_Aentry V j k) := by
    rw [hA]
    exact (innerSL ℝ : Euc p.d →L[ℝ] Euc p.d →L[ℝ] ℝ).isBoundedBilinearMap.contDiff.comp (hv2.prodMk hg2)
  have hbd : ∀ i ≤ 2, ∀ x, ‖iteratedFDeriv ℝ i (r26t3_Aentry V j k) x‖ ≤ 4 * (V.C * nj * nk) := by
    intro i hi x
    rw [hA]
    have hb := (innerSL ℝ : Euc p.d →L[ℝ] Euc p.d →L[ℝ] ℝ).norm_iteratedFDeriv_le_of_bilinear hv2 hg2 x
      (n := i) (by exact_mod_cast hi)
    refine hb.trans ?_
    have hterm : ∀ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * ‖iteratedFDeriv ℝ l (V.v j) x‖ *
        ‖iteratedFDeriv ℝ (i - l) (gradient (q k)) x‖ ≤ (i.choose l : ℝ) * (V.C * nj * nk) := by
      intro l hl
      have hl' : l ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
      have h1 : ‖iteratedFDeriv ℝ l (V.v j) x‖ ≤ V.C * nj := hv.2 l (by omega) x
      have h2 : ‖iteratedFDeriv ℝ (i - l) (gradient (q k)) x‖ ≤ nk := by
        have hqq : ContDiff ℝ (((i - l) + 1 : ℕ) : WithTop ℕ∞) (q k) := hq.of_le (by norm_cast; omega)
        rw [s21h2_s03_grad_norm hqq x]
        exact s21h2_s03_iter_le (V.summable.1 k) (by omega) x
      have hch : (0 : ℝ) ≤ (i.choose l : ℝ) := Nat.cast_nonneg _
      calc (i.choose l : ℝ) * ‖iteratedFDeriv ℝ l (V.v j) x‖ * ‖iteratedFDeriv ℝ (i - l) (gradient (q k)) x‖
          ≤ (i.choose l : ℝ) * (V.C * nj) * nk :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 hch) h2 (norm_nonneg _) (by positivity)
        _ = (i.choose l : ℝ) * (V.C * nj * nk) := by ring
    have hsum : ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * (V.C * nj * nk) = 2 ^ i * (V.C * nj * nk) := by
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast Nat.sum_range_choose i
    have hK0 : 0 ≤ V.C * nj * nk := by positivity
    have h2i : (2 : ℝ) ^ i ≤ 4 := by
      interval_cases i <;> norm_num
    calc ‖(innerSL ℝ : Euc p.d →L[ℝ] Euc p.d →L[ℝ] ℝ)‖ * ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) *
          ‖iteratedFDeriv ℝ l (V.v j) x‖ * ‖iteratedFDeriv ℝ (i - l) (gradient (q k)) x‖
        ≤ 1 * ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * (V.C * nj * nk) :=
          mul_le_mul (norm_innerSL_le ℝ) (Finset.sum_le_sum hterm) (Finset.sum_nonneg fun l _ => by positivity)
            zero_le_one
      _ = 2 ^ i * (V.C * nj * nk) := by rw [one_mul, hsum]
      _ ≤ 4 * (V.C * nj * nk) := mul_le_mul_of_nonneg_right h2i hK0
  refine ⟨hK', ⟨hcd, fun i hi => ⟨4 * (V.C * nj * nk), ?_⟩⟩, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hbd i hi x
  · have hK0 : 0 ≤ V.C * nj * nk := by positivity
    have hcb : cbNorm 2 (r26t3_Aentry V j k) ≤ 12 * (V.C * nj * nk) := by
      unfold cbNorm
      calc ∑ i ∈ Finset.range (2 + 1), ⨆ x, ‖iteratedFDeriv ℝ i (r26t3_Aentry V j k) x‖
          ≤ ∑ i ∈ Finset.range (2 + 1), 4 * (V.C * nj * nk) :=
            Finset.sum_le_sum fun i hi => ciSup_le fun x =>
              hbd i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) x
        _ = 12 * (V.C * nj * nk) := by simp [Finset.sum_range_succ]; ring
    calc cbNorm 2 (r26t3_Aentry V j k) ≤ 12 * (V.C * nj * nk) := hcb
      _ ≤ 12 * (V.C * nj * nk) * max p.s 1 := le_mul_of_one_le_right (by positivity) hm1
      _ = (12 * max p.s 1 * V.C) * nj * nk := by ring

end HRS.MS.R26T3
