import HRS.MS.SA12DE7K

/-!
# S.A.12(c), packet E7.07 (worker S82Z2), part L: plumbing for the weak-limit lemma

`L²(ℝ^d)` is separable; inner products against real `C_c^∞` tests; the squared norm of a `toLp` element; derivatives of
`C_c^∞` functions; smoothness of `partialDeriv idx F`; the zeroth jet; removing an indicator on the support of a test.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.SA12DE7

open HRS HRS.Whole HRS.MH.AdjointRd HRS.Whole.AppendixA HRS.Whole.Q09A

variable {d : ℕ}

instance sa12de7_sep : TopologicalSpace.SeparableSpace (Lp ℝ 2 (volume : Measure (Euc d))) :=
  inferInstance

theorem sa12de7_cc_memLp {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) : MemLp ψ 2 volume :=
  hψ.1.continuous.memLp_of_hasCompactSupport hψ.2

theorem sa12de7_inner_toLp {f ψ : Euc d → ℝ} (hf : MemLp f 2 volume) (hψ : IsCcInfty ψ) :
    inner ℝ (hf.toLp f) ((sa12de7_cc_memLp hψ).toLp ψ) = ∫ x, f x * ψ x := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, (sa12de7_cc_memLp hψ).coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

theorem sa12de7_norm_sq_toLp {f : Euc d → ℝ} (hf : MemLp f 2 volume) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, (f x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with x h1
  rw [h1]
  simp [sq]

theorem sa12de7_cc_fderiv {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) (i : Fin d) :
    IsCcInfty (fun x => fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))) := by
  refine ⟨?_, ?_⟩
  · exact (hψ.1.fderiv_right (m := (∞ : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const
  · have : HasCompactSupport (fderiv ℝ ψ) := hψ.2.fderiv (𝕜 := ℝ)
    exact this.comp_left (g := fun A : Euc d →L[ℝ] ℝ => A (EuclideanSpace.single i (1 : ℝ))) (by simp)

theorem sa12de7_partialDeriv_contDiff {F : Euc d → ℝ} (hF : ContDiff ℝ ∞ F) {j : ℕ} (idx : Fin j → Fin d) :
    ContDiff ℝ ∞ (partialDeriv idx F) := by
  have h1 : ContDiff ℝ ∞ (iteratedFDeriv ℝ j F) := hF.iteratedFDeriv_right (by simp)
  have h2 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ
    (fun l => EuclideanSpace.single (idx l) (1 : ℝ))).contDiff.comp h1
  exact h2

theorem sa12de7_partialDeriv_zero (F : Euc d → ℝ) (idx : Fin 0 → Fin d) (x : Euc d) :
    partialDeriv idx F x = F x := by
  unfold partialDeriv
  rw [iteratedFDeriv_zero_apply]

theorem sa12de7_indicator_mul {S : Set (Euc d)} {f ψ : Euc d → ℝ} (hS : tsupport ψ ⊆ S) (x : Euc d) :
    S.indicator f x * ψ x = f x * ψ x := by
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx]
  · have : ψ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hS h)
    simp [this]

end HRS.MS.SA12DE7
