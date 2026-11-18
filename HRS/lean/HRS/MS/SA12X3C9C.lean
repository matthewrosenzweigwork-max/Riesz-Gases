import HRS.MS.SA12X3C9B
import HRS.MS.WadAux14

/-!
# S.A.12 C9 (SA12X3), part C: the pointwise bound of the transport commutator
`|∂^idx ⟨b,∇F⟩ - ⟨b,∇ ∂^idx F⟩| ≤ d Cb 2^m T_m(F)` (jets of `F` of order `≤ m`).
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MH.AdjointRd HRS.MS.UniqT3

variable {d : ℕ}

theorem sa12x3_inner_grad (b : Euc d) (F : Euc d → ℝ) (y : Euc d) :
    inner ℝ b (gradient F y) = ∑ i : Fin d, b i * D1 i F y := by
  rw [real_inner_comm, HRS.MS.Wad.s83_inner_gradient]
  have : b = ∑ i : Fin d, b i • (EuclideanSpace.single i (1 : ℝ) : Euc d) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [this]
  simp [map_sum, D1, mul_comm]

theorem sa12x3_comm_pt {m n : ℕ} (hn : n ≤ m) {Cb : ℝ} {b : Euc d → Euc d} (hbC : ContDiff ℝ (m + 1) b)
    (hbb : ∀ k, 1 ≤ k → k ≤ m + 1 → ∀ x, ‖iteratedFDeriv ℝ k b x‖ ≤ Cb) {F : Euc d → ℝ}
    (hF : ContDiff ℝ ∞ F) (idx : Fin n → Fin d) (x : Euc d) :
    |partialDeriv idx (fun y => inner ℝ (b y) (gradient F y)) x - fderiv ℝ (partialDeriv idx F) x (b x)| ≤
      d * (Cb * 2 ^ m * sa12z3_T m F x) := by
  have hbi : ∀ i : Fin d, ContDiff ℝ (m + 1) (fun y => b y i) := fun i =>
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff.comp hbC
  have hbj : ∀ i : Fin d, ∀ k, 1 ≤ k → k ≤ m + 1 → ∀ y, ‖iteratedFDeriv ℝ k (fun y => b y i) y‖ ≤ Cb := by
    intro i k hk1 hkm y
    have h := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)
      (hbC.contDiffAt (x := y)) (n := k) (by exact_mod_cast hkm)
    have hn1 : ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
        simpa using PiLp.norm_apply_le v i
    have h' : ‖iteratedFDeriv ℝ k (fun y => b y i) y‖ ≤
        ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)‖ * ‖iteratedFDeriv ℝ k b y‖ := h
    exact h'.trans ((mul_le_mul_of_nonneg_right hn1 (norm_nonneg _)).trans (by rw [one_mul]; exact hbb k hk1 hkm y))
  have hcdF : ∀ k : ℕ, ContDiff ℝ k F := fun k => sa12z3_cd_of_inf hF k
  have hD1 : ∀ i : Fin d, ContDiff ℝ n (D1 i F) := fun i =>
    ((sa12z3_cd_of_inf hF (n + 1)).fderiv_right (m := n) (by push_cast; rfl)).clm_apply contDiff_const
  have hprod : ∀ i : Fin d, ContDiff ℝ n (fun y => b y i * D1 i F y) := fun i =>
    ((hbi i).of_le (by exact_mod_cast (by omega : n ≤ m + 1))).mul (hD1 i)
  have e1 : (fun y => inner ℝ (b y) (gradient F y)) = fun y => ∑ i ∈ (Finset.univ : Finset (Fin d)),
      (fun _ => (1 : ℝ)) i * (fun i y => b y i * D1 i F y) i y := by
    funext y; rw [sa12x3_inner_grad]; simp
  have e2 : fderiv ℝ (partialDeriv idx F) x (b x) = ∑ i : Fin d, b x i * D1 i (partialDeriv idx F) x :=
    by
      have := sa12x3_inner_grad (b x) (partialDeriv idx F) x
      rw [← this, real_inner_comm, HRS.MS.Wad.s83_inner_gradient]
  rw [e1, sa12z3_pd_sum (Finset.univ : Finset (Fin d)) (fun i y => b y i * D1 i F y) (fun _ => 1) (n := n)
    (fun i _ => hprod i) idx x, e2, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ i : Fin d, |1 * partialDeriv idx (fun y => b y i * D1 i F y) x - b x i * D1 i (partialDeriv idx F) x| ≤
      Cb * 2 ^ m * sa12z3_T m F x := fun i => by
    have h := sa12x3_Rj_pt' hn (a := fun y => b y i) (hbi i) hF (Ka := Cb) (hbj i) idx i x
    unfold sa12z3_Rj at h
    simpa using h
  calc ∑ i : Fin d, |1 * partialDeriv idx (fun y => b y i * D1 i F y) x - b x i * D1 i (partialDeriv idx F) x|
      ≤ ∑ _i : Fin d, Cb * 2 ^ m * sa12z3_T m F x := Finset.sum_le_sum fun i _ => hterm i
    _ = d * (Cb * 2 ^ m * sa12z3_T m F x) := by simp

end HRS.MH.AdjointRd.Phase2SA12Near
