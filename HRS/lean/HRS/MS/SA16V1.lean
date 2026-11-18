import HRS.PDE.ToolboxRd.Fourier
import HRS.Whole.AppendixAAdjoint

/-!
# S.A.16 A2, part 1: an `H^1` bound for a `C^1` compactly supported function from its gradient

For `v ∈ C¹_c(ℝ^d)` with `Γ(y) = ∑_i |∂_i v(y)|`:
`∫ (v(x) - v(x-h))² ≤ ‖h‖² ∫ Γ²`  (`sa16v_diff_sq`) and
`sobolevNormSq 1 v ≤ ∫ v² + d ∫ Γ²` (`sa16v_h1`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16V
open HRS HRS.Whole HRS.Whole.AppendixA HRS.PDE.ToolboxRd

section H1
variable {d : ℕ}

/-- `Γ(y) = ∑_i |∂_i v (y)|` -/
def sa16v_grad (v : Euc d → ℝ) (y : Euc d) : ℝ :=
  ∑ i : Fin d, |fderiv ℝ v y (EuclideanSpace.single i (1 : ℝ))|

lemma sa16v_grad_nonneg (v : Euc d → ℝ) (y : Euc d) : 0 ≤ sa16v_grad v y :=
  Finset.sum_nonneg fun i _ => abs_nonneg _

lemma sa16v_fderiv_le (v : Euc d → ℝ) (y h : Euc d) :
    |fderiv ℝ v y h| ≤ ‖h‖ * sa16v_grad v y := by
  have hh : h = ∑ i : Fin d, h i • (EuclideanSpace.single i (1 : ℝ) : Euc d) := by
    ext j
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb.symm]
    · simp
  conv_lhs => rw [hh]
  rw [map_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  unfold sa16v_grad
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [map_smul, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right (by simpa using PiLp.norm_apply_le h i) (abs_nonneg _)

lemma sa16v_grad_cont {v : Euc d → ℝ} (hv : ContDiff ℝ 1 v) : Continuous (sa16v_grad v) := by
  unfold sa16v_grad
  have h1 : Continuous (fun y => fderiv ℝ v y) := hv.continuous_fderiv one_ne_zero
  refine continuous_finsetSum _ fun i _ => ?_
  exact (h1.clm_apply continuous_const).abs

lemma sa16v_grad_support {v : Euc d → ℝ} (hv : HasCompactSupport v) : HasCompactSupport (sa16v_grad v) := by
  refine IsCompact.of_isClosed_subset hv (isClosed_tsupport _) ?_
  refine closure_minimal (fun y hy => ?_) (isClosed_tsupport v)
  have : fderiv ℝ v y ≠ 0 := by
    intro h0
    apply hy
    unfold sa16v_grad
    simp [h0]
  exact support_fderiv_subset ℝ this

lemma sa16v_sq_integral_le (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ t in (0 : ℝ)..1, g t) ^ 2 ≤ ∫ t in (0 : ℝ)..1, (g t) ^ 2 := by
  set m : ℝ := ∫ t in (0 : ℝ)..1, g t with hm
  have hgi : IntervalIntegrable g volume 0 1 := hg.intervalIntegrable _ _
  have hg2 : IntervalIntegrable (fun t => (g t) ^ 2) volume 0 1 := (hg.pow 2).intervalIntegrable _ _
  have h0 : 0 ≤ ∫ t in (0 : ℝ)..1, (g t - m) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun t _ => sq_nonneg _
  have e : ∀ t, (g t - m) ^ 2 = ((g t) ^ 2 - 2 * m * g t) + m ^ 2 := fun t => by ring
  simp_rw [e] at h0
  rw [intervalIntegral.integral_add (hg2.sub (hgi.const_mul _)) intervalIntegrable_const,
    intervalIntegral.integral_sub hg2 (hgi.const_mul _), intervalIntegral.integral_const_mul] at h0
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] at h0
  rw [← hm] at h0
  nlinarith [h0]

lemma sa16v_pointwise {v : Euc d → ℝ} (hv : ContDiff ℝ 1 v) (x h : Euc d) :
    (v x - v (x - h)) ^ 2 ≤ ‖h‖ ^ 2 * ∫ t in (0 : ℝ)..1, sa16v_grad v (x - h + t • h) ^ 2 := by
  set f' : ℝ → ℝ := fun t => fderiv ℝ v (x - h + t • h) h with hf'
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => v (x - h + t • h)) (f' t) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => x - h + t • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add (x - h)
    have h2 : HasFDerivAt v (fderiv ℝ v (x - h + t • h)) (x - h + t • h) :=
      ((hv.differentiable one_ne_zero) _).hasFDerivAt
    exact h2.comp_hasDerivAt t h1
  have hcont : Continuous f' := by
    have h1 : Continuous (fun y => fderiv ℝ v y) := hv.continuous_fderiv one_ne_zero
    have h2 : Continuous (fun t : ℝ => x - h + t • h) := by fun_prop
    exact (h1.comp h2).clm_apply continuous_const
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable _ _)
  have e1 : x - h + (1 : ℝ) • h = x := by simp
  have e0 : x - h + (0 : ℝ) • h = x - h := by simp
  simp only [e1, e0] at hftc
  rw [← hftc]
  refine (sa16v_sq_integral_le f' hcont).trans ?_
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on (by norm_num) ((hcont.pow 2).intervalIntegrable _ _)
    ((((sa16v_grad_cont hv).comp (by fun_prop : Continuous (fun t : ℝ => x - h + t • h))).pow 2).const_mul
      _ |>.intervalIntegrable _ _) fun t _ => ?_
  have := sa16v_fderiv_le v (x - h + t • h) h
  have h3 : (f' t) ^ 2 ≤ (‖h‖ * sa16v_grad v (x - h + t • h)) ^ 2 := by
    rw [← sq_abs (f' t)]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  calc (f' t) ^ 2 ≤ (‖h‖ * sa16v_grad v (x - h + t • h)) ^ 2 := h3
    _ = ‖h‖ ^ 2 * sa16v_grad v (x - h + t • h) ^ 2 := by ring

set_option maxHeartbeats 400000 in
lemma sa16v_diff_sq {v : Euc d → ℝ} (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v) (h : Euc d) :
    ∫ x, (v x - v (x - h)) ^ 2 ≤ (∫ y, sa16v_grad v y ^ 2) * ‖h‖ ^ 2 := by
  have hcont := sa16v_grad_cont hv
  have hcs := sa16v_grad_support hc
  have hcs2 : HasCompactSupport (fun y => sa16v_grad v y ^ 2) :=
    hcs.comp_left (g := fun r : ℝ => r ^ 2) (by simp)
  have hG2 : Integrable (fun y => sa16v_grad v y ^ 2) volume :=
    (hcont.pow 2).integrable_of_hasCompactSupport hcs2
  have hvL2 : MemLp v 2 volume := hv.continuous.memLp_of_hasCompactSupport hc
  have hLint : Integrable (fun x => (v x - v (x - h)) ^ 2) volume :=
    (hvL2.sub (FourierAux.memLp_translate hvL2 h)).integrable_sq
  have hL0 : ∀ x, 0 ≤ (v x - v (x - h)) ^ 2 := fun x => sq_nonneg _
  -- pointwise bound in `ℝ≥0∞`
  have hpt : ∀ x, ENNReal.ofReal ((v x - v (x - h)) ^ 2) ≤ ENNReal.ofReal (‖h‖ ^ 2) *
      ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (sa16v_grad v (x - h + t • h) ^ 2) := by
    intro x
    have hgc : Continuous (fun t : ℝ => sa16v_grad v (x - h + t • h) ^ 2) :=
      (hcont.comp (by fun_prop : Continuous (fun t : ℝ => x - h + t • h))).pow 2
    have hint : ∫ t in (0 : ℝ)..1, sa16v_grad v (x - h + t • h) ^ 2 =
        ∫ t in Ioc (0 : ℝ) 1, sa16v_grad v (x - h + t • h) ^ 2 :=
      intervalIntegral.integral_of_le zero_le_one
    have hii : IntegrableOn (fun t : ℝ => sa16v_grad v (x - h + t • h) ^ 2) (Ioc (0 : ℝ) 1) volume :=
      (hgc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have hofr : ENNReal.ofReal (∫ t in (0 : ℝ)..1, sa16v_grad v (x - h + t • h) ^ 2) =
        ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (sa16v_grad v (x - h + t • h) ^ 2) := by
      rw [hint]
      exact ofReal_integral_eq_lintegral_ofReal hii (Eventually.of_forall fun t => sq_nonneg _)
    rw [← hofr, ← ENNReal.ofReal_mul (sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (sa16v_pointwise hv x h)
  have hA : ∫⁻ x, ENNReal.ofReal ((v x - v (x - h)) ^ 2) ≤
      ENNReal.ofReal (‖h‖ ^ 2) * ∫⁻ y, ENNReal.ofReal (sa16v_grad v y ^ 2) := by
    refine (lintegral_mono hpt).trans ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine mul_le_mul' le_rfl (le_of_eq ?_)
    have hmeas : Measurable (Function.uncurry fun (x : Euc d) (t : ℝ) =>
        ENNReal.ofReal (sa16v_grad v (x - h + t • h) ^ 2)) := by
      refine ENNReal.measurable_ofReal.comp ?_
      refine Measurable.pow_const ?_ 2
      exact (hcont.measurable.comp (by fun_prop : Measurable (fun q : Euc d × ℝ => q.1 - h + q.2 • h)))
    rw [lintegral_lintegral_swap hmeas.aemeasurable]
    have : ∀ t : ℝ, ∫⁻ x, ENNReal.ofReal (sa16v_grad v (x - h + t • h) ^ 2) =
        ∫⁻ y, ENNReal.ofReal (sa16v_grad v y ^ 2) := by
      intro t
      have e : ∀ x : Euc d, x - h + t • h = x - (h - t • h) := fun x => by abel
      simp_rw [e]
      exact lintegral_sub_right_eq_self (fun y => ENNReal.ofReal (sa16v_grad v y ^ 2)) (h - t • h)
    simp_rw [this]
    rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
    simp
  have hB : ENNReal.ofReal (∫ x, (v x - v (x - h)) ^ 2) ≤
      ENNReal.ofReal ((∫ y, sa16v_grad v y ^ 2) * ‖h‖ ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hLint (Eventually.of_forall hL0), mul_comm,
      ENNReal.ofReal_mul (sq_nonneg _), ofReal_integral_eq_lintegral_ofReal hG2
        (Eventually.of_forall fun y => sq_nonneg _)]
    exact hA
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (integral_nonneg fun y => sq_nonneg _)
    (sq_nonneg _))).1 hB

theorem sa16v_h1 {v : Euc d → ℝ} (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v) :
    HRS.PDE.ToolboxRd.MemSobolev 1 v ∧ HRS.PDE.ToolboxRd.sobolevNormSq 1 v ≤ (∫ x, v x ^ 2) + (d : ℝ) * ∫ y, sa16v_grad v y ^ 2 := by
  have hvL2 : MemLp v 2 volume := hv.continuous.memLp_of_hasCompactSupport hc
  set C : ℝ := ∫ y, sa16v_grad v y ^ 2 with hC
  have hCh : ∀ h : Euc d, ∫ x, (v x - v (x - h)) ^ 2 ≤ C * ‖h‖ ^ 2 := sa16v_diff_sq hv hc
  have hmem := FourierAux.memSobolev_one_of_diff_bound hvL2 C hCh
  refine ⟨hmem, ?_⟩
  have hco := fun i : Fin d => FourierAux.coord_integrable hvL2 C hCh i
  have hI0 := FourierAux.integrable_norm_sq_fourierL2 hvL2
  have hsum : ∀ ξ : Euc d, (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (1 : ℝ) * ‖fourierL2 v ξ‖ ^ 2 =
      ‖fourierL2 v ξ‖ ^ 2 + ∑ i : Fin d, 4 * Real.pi ^ 2 * (ξ i) ^ 2 * ‖fourierL2 v ξ‖ ^ 2 := by
    intro ξ
    rw [Real.rpow_one]
    have hn : ‖ξ‖ ^ 2 = ∑ i : Fin d, (ξ i) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp
    simp only [hn, ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  unfold HRS.PDE.ToolboxRd.sobolevNormSq
  simp_rw [hsum]
  rw [integral_add hI0 (integrable_finsetSum _ fun i _ => (hco i).1), integral_finsetSum _ fun i _ => (hco i).1,
    FourierAux.integral_norm_sq_fourierL2 hvL2]
  have : ∑ i : Fin d, ∫ ξ, 4 * Real.pi ^ 2 * (ξ i) ^ 2 * ‖fourierL2 v ξ‖ ^ 2 ≤ ∑ i : Fin d, C :=
    Finset.sum_le_sum fun i _ => (hco i).2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  linarith

end H1

end HRS.Whole.AppendixA.Phase2SA16V
