import HRS.MS.SA12C5

/-!
# S.A.12(c), packet E7.06 (part 4): the transport term over the period box

`∫_{Q_L} 2 W (b·∇W) = -∫_{Q_L} (div b) W²` for periodic `W, b`, hence `≤ d C_b ∫_{Q_L} W²`.
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12Near HRS.MS.UniqT3

variable {d : ℕ}

theorem sa12c_transport_idx {L : ℝ} (hL : 0 < L) {m : ℕ} {b : Euc d → Euc d} {Cb : ℝ}
    (hbC : ContDiff ℝ (m + 1) b)
    (hbp : ∀ (x : Euc d) (k : Fin d → ℤ), b (x + L • latticePt k) = b x)
    (hbb : ∀ k, 1 ≤ k → k ≤ m + 1 → ∀ x, ‖iteratedFDeriv ℝ k b x‖ ≤ Cb)
    {W : Euc d → ℝ} (hWi : ContDiff ℝ ∞ W)
    (hWp : ∀ (x : Euc d) (k : Fin d → ℤ), W (x + L • latticePt k) = W x) :
    ∫ x in periodBox d L, 2 * (W x * fderiv ℝ W x (b x)) ≤
      d * Cb * ∫ x in periodBox d L, W x ^ 2 := by
  have hbC1 : ContDiff ℝ 1 b := hbC.of_le (by exact_mod_cast (by omega : 1 ≤ m + 1))
  have hCb0 : 0 ≤ Cb := (norm_nonneg _).trans (hbb 1 le_rfl (by omega) 0)
  have hW1 : ContDiff ℝ 1 W := sa12z3_cd_of_inf hWi 1
  have hWc : Continuous W := hWi.continuous
  have hWd : Differentiable ℝ W := hW1.differentiable one_ne_zero
  have hbd : Differentiable ℝ b := hbC1.differentiable one_ne_zero
  have hbi : ∀ i : Fin d, ContDiff ℝ 1 (fun y => b y i) := fun i =>
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff.comp hbC1
  have hbip : ∀ i : Fin d, ∀ (x : Euc d) (k : Fin d → ℤ), b (x + L • latticePt k) i = b x i :=
    fun i x k => by rw [hbp x k]
  have hu1 : ContDiff ℝ 1 (fun z => W z * W z) := hW1.mul hW1
  have hup : ∀ (x : Euc d) (k : Fin d → ℤ), W (x + L • latticePt k) * W (x + L • latticePt k) = W x * W x :=
    fun x k => by rw [hWp x k]
  -- fderiv W (b x) as a sum
  have e2 : ∀ x, fderiv ℝ W x (b x) = ∑ i : Fin d, b x i * D1 i W x := by
    intro x
    have := sa12x3_inner_grad (b x) W x
    rw [← this, real_inner_comm, HRS.MS.Wad.s83_inner_gradient]
  have hper : ∀ i : Fin d, ∫ x in periodBox d L, (2 * (W x * D1 i W x)) * b x i =
      -∫ x in periodBox d L, (W x * W x) * fderiv ℝ (fun y => b y i) x (EuclideanSpace.single i (1 : ℝ)) := by
    intro i
    have h := sa12v_per_ibp L hL hu1 (hbi i) hup (hbip i) i
    have hd : ∀ z, fderiv ℝ (fun z => W z * W z) z (EuclideanSpace.single i (1 : ℝ)) =
        2 * (W z * D1 i W z) := by
      intro z
      have h3 : HasFDerivAt (fun z => W z * W z) (W z • fderiv ℝ W z + W z • fderiv ℝ W z) z :=
        (hWd z).hasFDerivAt.mul (hWd z).hasFDerivAt
      rw [h3.fderiv]
      simp [D1]
      ring
    simp_rw [hd] at h
    exact h
  have hcb : ∀ i : Fin d, Continuous (fun x => fderiv ℝ (fun y => b y i) x (EuclideanSpace.single i (1 : ℝ))) :=
    fun i => ((hbi i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hD1c : ∀ i : Fin d, Continuous (D1 i W) := fun i => (sa12y_D1_contDiff hWi i).continuous
  have hbc : ∀ i : Fin d, Continuous (fun x => b x i) := fun i => (hbi i).continuous
  -- the sum
  have hsum : ∫ x in periodBox d L, 2 * (W x * fderiv ℝ W x (b x)) =
      -∫ x in periodBox d L, (∑ i : Fin d, fderiv ℝ (fun y => b y i) x (EuclideanSpace.single i (1 : ℝ))) *
        (W x * W x) := by
    have hfun : (fun x => 2 * (W x * fderiv ℝ W x (b x))) =
        fun x => ∑ i : Fin d, (2 * (W x * D1 i W x)) * b x i := by
      funext x
      rw [e2, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hfun, integral_finset_sum (Finset.univ : Finset (Fin d))
      (f := fun i x => (2 * (W x * D1 i W x)) * b x i) fun i _ => sa12v_integrableOn_box L
      (((continuous_const.mul (hWc.mul (hD1c i)))).mul (hbc i))]
    simp_rw [hper]
    rw [Finset.sum_neg_distrib, ← integral_finset_sum (Finset.univ : Finset (Fin d))
      (f := fun i x => (W x * W x) * fderiv ℝ (fun y => b y i) x (EuclideanSpace.single i (1 : ℝ)))
      fun i _ => sa12v_integrableOn_box L ((hWc.mul hWc).mul (hcb i))]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hdivb : ∀ x, |∑ i : Fin d, fderiv ℝ (fun y => b y i) x (EuclideanSpace.single i (1 : ℝ))| ≤ d * Cb := by
    intro x
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ i : Fin d, |fderiv ℝ (fun y => b y i) x (EuclideanSpace.single i (1 : ℝ))| ≤ Cb := by
      intro i
      have h1 : HasFDerivAt (fun y => b y i) ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).comp (fderiv ℝ b x)) x :=
        (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasFDerivAt.comp x (hbd x).hasFDerivAt
      rw [h1.fderiv]
      have h2 : ‖fderiv ℝ b x‖ ≤ Cb := by
        rw [← norm_iteratedFDeriv_one]; exact hbb 1 le_rfl (by omega) x
      have h3 := (fderiv ℝ b x).le_opNorm (EuclideanSpace.single i (1 : ℝ))
      have hn1 : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := by simp
      rw [hn1, mul_one] at h3
      have h4 := PiLp.norm_apply_le (fderiv ℝ b x (EuclideanSpace.single i (1 : ℝ))) i
      simp only [ContinuousLinearMap.comp_apply]
      rw [← Real.norm_eq_abs]
      exact (h4.trans h3).trans h2
    calc ∑ i : Fin d, |fderiv ℝ (fun y => b y i) x (EuclideanSpace.single i (1 : ℝ))| ≤ ∑ _i : Fin d, Cb :=
          Finset.sum_le_sum fun i _ => this i
      _ = d * Cb := by simp
  have hdc : Continuous (fun x => ∑ i : Fin d, fderiv ℝ (fun y => b y i) x (EuclideanSpace.single i (1 : ℝ))) :=
    continuous_finsetSum _ fun i _ => hcb i
  rw [hsum]
  have hi1 : IntegrableOn (fun x => (∑ i : Fin d, fderiv ℝ (fun y => b y i) x (EuclideanSpace.single i (1 : ℝ))) *
      (W x * W x)) (periodBox d L) := sa12v_integrableOn_box L (hdc.mul (hWc.mul hWc))
  have hi2 : IntegrableOn (fun x => W x ^ 2) (periodBox d L) := sa12v_integrableOn_box L (hWc.pow 2)
  calc -∫ x in periodBox d L, (∑ i : Fin d, fderiv ℝ (fun y => b y i) x (EuclideanSpace.single i (1 : ℝ))) *
        (W x * W x)
      = ∫ x in periodBox d L, -((∑ i : Fin d, fderiv ℝ (fun y => b y i) x (EuclideanSpace.single i (1 : ℝ))) *
        (W x * W x)) := (integral_neg _).symm
    _ ≤ ∫ x in periodBox d L, (d * Cb) * W x ^ 2 := by
        refine integral_mono hi1.neg (hi2.const_mul _) fun x => ?_
        have hS := hdivb x
        have h0 : 0 ≤ W x * W x := mul_self_nonneg _
        set S := ∑ i : Fin d, fderiv ℝ (fun y => b y i) x (EuclideanSpace.single i (1 : ℝ)) with hSdef
        have h6 : 0 ≤ (|S| + S) * (W x * W x) :=
          mul_nonneg (by linarith [neg_abs_le S]) h0
        have h7 : |S| * (W x * W x) ≤ (d * Cb) * (W x * W x) := mul_le_mul_of_nonneg_right hS h0
        have h8 : (d * Cb) * W x ^ 2 = (d * Cb) * (W x * W x) := by ring
        rw [h8]
        linarith
    _ = d * Cb * ∫ x in periodBox d L, W x ^ 2 := by rw [integral_const_mul]

end HRS.MH.AdjointRd.Phase2SA12C
