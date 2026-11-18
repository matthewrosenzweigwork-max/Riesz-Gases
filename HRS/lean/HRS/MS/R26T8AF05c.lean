import HRS.MS.R26T8AF05a
import HRS.MS.R26T8AF04
import HRS.MS.SA12V3N

/-!
# S8.2 observed-time layer, packet T8A.F05 (helper 05c): generic Sobolev and Euler tools

Schwartz functions lie in `SobSmooth`; Sobolev norms are monotone in the order; finite sums of
`SobSmooth` functions are `SobSmooth`, with the triangle inequality for `sobolevNormE`; multiplication of a
Schwartz function by a temperate coefficient; Euler operator `E h x = fderiv h x x` in coordinates and on
products.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

theorem r26t8a_f05c_schw_sob (g : SchwartzMap (Euc d) ℝ) : r26t8a_SobSmooth (⇑g) :=
  ⟨g.smooth (⊤ : ℕ∞), fun r => HRS.MS.MovC1.movc1_memSob_schwartz g r⟩

theorem r26t8a_f05c_sob_mono {r s : ℝ} (h : r ≤ s) (u : Euc d → ℝ) :
    sobolevNormE r u ≤ sobolevNormE s u := by
  unfold sobolevNormE
  by_cases hs : HRS.PDE.ToolboxRd.MemSobolev s u
  · have hr : HRS.PDE.ToolboxRd.MemSobolev r u := memSobolev_mono h hs
    rw [if_pos hs, if_pos hr]
    refine ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_)
    unfold sobolevNormSq
    refine integral_mono_of_nonneg (Eventually.of_forall fun ξ => ?_) hs.2
      (Eventually.of_forall fun ξ => ?_)
    · exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)
    · have hw : (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ r ≤ (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ s :=
        Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (Real.pi), sq_nonneg ‖ξ‖])
          h
      exact mul_le_mul_of_nonneg_right hw (sq_nonneg _)
  · rw [if_neg hs]
    exact le_top

theorem r26t8a_f05c_sob_zero (r : ℝ) : sobolevNormE r (fun _ : Euc d => (0 : ℝ)) = 0 := by
  have hmem : HRS.PDE.ToolboxRd.MemSobolev r (fun _ : Euc d => (0 : ℝ)) := by
    have h0 : (fun _ : Euc d => (0 : ℝ)) = ⇑(0 : SchwartzMap (Euc d) ℝ) := by
      funext x
      simp
    rw [h0]
    exact HRS.MS.MovC1.movc1_memSob_schwartz (0 : SchwartzMap (Euc d) ℝ) r
  have hae := fourierL2_smul hmem.1 0
  have hz : ∀ᵐ ξ ∂(volume : Measure (Euc d)), fourierL2 (fun _ : Euc d => (0 : ℝ)) ξ = 0 := by
    filter_upwards [hae] with ξ hξ
    simpa using hξ
  have key : ∀ᵐ ξ ∂(volume : Measure (Euc d)),
      (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ r * ‖fourierL2 (fun _ : Euc d => (0 : ℝ)) ξ‖ ^ 2 = 0 := by
    filter_upwards [hz] with ξ hξ
    rw [hξ]
    simp
  have hs : sobolevNormSq r (fun _ : Euc d => (0 : ℝ)) = 0 := by
    unfold sobolevNormSq
    rw [integral_congr_ae key]
    simp
  unfold sobolevNormE
  rw [if_pos hmem, hs, Real.sqrt_zero, ENNReal.ofReal_zero]

theorem r26t8a_f05c_sob_sum (r : ℝ) {ι : Type*} (s : Finset ι) (F : ι → Euc d → ℝ) :
    sobolevNormE r (fun x => ∑ i ∈ s, F i x) ≤ ∑ i ∈ s, sobolevNormE r (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (r26t8a_f05c_sob_zero r).le
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact le_trans (HRS.MH.AdjointRd.Phase2SA12V3.sa12v3_sobolevNormE_add_le r _ _)
      (add_le_add le_rfl ih)

theorem r26t8a_f05c_mem_of_lt_top {r : ℝ} {u : Euc d → ℝ} (h : sobolevNormE r u < ⊤) :
    HRS.PDE.ToolboxRd.MemSobolev r u := by
  by_contra hn
  unfold sobolevNormE at h
  rw [if_neg hn] at h
  exact lt_irrefl _ h

theorem r26t8a_f05c_sum_sob {ι : Type*} (s : Finset ι) (F : ι → Euc d → ℝ)
    (hF : ∀ i ∈ s, r26t8a_SobSmooth (F i)) : r26t8a_SobSmooth (fun x => ∑ i ∈ s, F i x) := by
  refine ⟨ContDiff.sum fun i hi => (hF i hi).1, fun r => ?_⟩
  by_contra hn
  have h1 : sobolevNormE (r : ℝ) (fun x => ∑ i ∈ s, F i x) = ⊤ := by
    unfold sobolevNormE
    rw [if_neg hn]
  have hle := r26t8a_f05c_sob_sum (r : ℝ) s F
  have hfin : ∑ i ∈ s, sobolevNormE (r : ℝ) (F i) < ⊤ := by
    refine (ENNReal.sum_lt_top).2 fun i hi => ?_
    unfold sobolevNormE
    rw [if_pos ((hF i hi).2 r)]
    exact ENNReal.ofReal_lt_top
  rw [h1] at hle
  exact lt_irrefl _ (lt_of_le_of_lt hle hfin)

theorem r26t8a_f05c_mul (c : Euc d → ℝ) (hc : c.HasTemperateGrowth) (g : SchwartzMap (Euc d) ℝ) :
    ∃ h : SchwartzMap (Euc d) ℝ, ∀ x, h x = c x * g x :=
  ⟨SchwartzMap.smulLeftCLM ℝ c g, fun x => by
    simp [SchwartzMap.smulLeftCLM_apply_apply hc]⟩

theorem r26t8a_f05c_coord_tg (k : Fin d) :
    (fun x : Euc d => inner ℝ x (EuclideanSpace.single k (1 : ℝ))).HasTemperateGrowth :=
  ((innerSL ℝ).flip (EuclideanSpace.single k (1 : ℝ) : Euc d)).hasTemperateGrowth

theorem r26t8a_f05c_euler_sum (v : Euc d → ℝ) (x : Euc d) :
    fderiv ℝ v x x = ∑ k : Fin d,
      inner ℝ x (EuclideanSpace.single k (1 : ℝ)) * fderiv ℝ v x (EuclideanSpace.single k (1 : ℝ)) := by
  have hx : x = ∑ k : Fin d,
      inner ℝ x (EuclideanSpace.single k (1 : ℝ)) • (EuclideanSpace.single k (1 : ℝ) : Euc d) := by
    ext j
    simp [Finset.sum_apply, EuclideanSpace.inner_single_right, Pi.single_apply, mul_ite,
      Finset.sum_ite_eq', Finset.sum_ite_eq]
  calc fderiv ℝ v x x = fderiv ℝ v x (∑ k : Fin d,
        inner ℝ x (EuclideanSpace.single k (1 : ℝ)) • (EuclideanSpace.single k (1 : ℝ) : Euc d)) := by
        rw [← hx]
    _ = _ := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_smul, smul_eq_mul]

theorem r26t8a_f05c_euler_mul (s v : Euc d → ℝ) (x : Euc d) (hs : DifferentiableAt ℝ s x)
    (hv : DifferentiableAt ℝ v x) :
    fderiv ℝ (fun y => s y * v y) x x = s x * fderiv ℝ v x x + v x * fderiv ℝ s x x := by
  have h := fderiv_mul hs hv
  rw [show (fun y => s y * v y) = s * v from rfl, h, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul]

end HRS.MS.R26T8A

end
