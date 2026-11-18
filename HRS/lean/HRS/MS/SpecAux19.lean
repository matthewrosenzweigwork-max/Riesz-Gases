import HRS.MS.SpecAux18
import HRS.MS.SpecAux12

/-!
# S8P: the operator `A = ν I + P Q` on a closed subspace and its `BData` (S8.7, packet E1)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  For a subspace `K ⊂ L²(dx)` (later `K = L²_0 = √ρ^⊥`) the operator
`s8p_Asub : K →L K` with `⟨A v, w⟩ = ν ⟨v, w⟩ + ⟨Q v, w⟩`, symmetric, `⟨v, A v⟩ ≥ ν ‖v‖²`, and the `BData` of `A`.
In the variables `v = √ρ f`, `A` is the operator `ν + K_μ` of the manuscript acting on `f ∈ L²_0(μ)`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal RealInnerProductSpace

namespace HRS.MS.Spec

open HRS HRS.Whole

variable {d : ℕ}

section Sub

variable {ρ : Euc d → ℝ} {s M : ℝ} (h : S8pRho d s ρ M)
  (K : Submodule ℝ (Lp ℝ 2 (volume : Measure (Euc d)))) [CompleteSpace K]

/-- The operator `A = ν I + P_K Q|_K`. -/
def s8p_Asub (ν : ℝ) : K →L[ℝ] K :=
  ν • ContinuousLinearMap.id ℝ K + (K.orthogonalProjectionOnto ∘L s8p_Q h ∘L K.subtypeL)

theorem s8p_Asub_inner (ν : ℝ) (v w : K) :
    ⟪s8p_Asub h K ν v, w⟫ = ν * ⟪v, w⟫ + s8p_qf s ρ (v : Lp ℝ 2 (volume : Measure (Euc d)))
      (w : Lp ℝ 2 (volume : Measure (Euc d))) := by
  unfold s8p_Asub
  rw [ContinuousLinearMap.add_apply, inner_add_left]
  have h1 : ⟪(ν • ContinuousLinearMap.id ℝ K) v, w⟫ = ν * ⟪v, w⟫ := by
    simp [real_inner_smul_left]
  have h2 : ⟪(K.orthogonalProjectionOnto ∘L s8p_Q h ∘L K.subtypeL) v, w⟫ =
      ⟪s8p_Q h (v : Lp ℝ 2 (volume : Measure (Euc d))), (w : Lp ℝ 2 (volume : Measure (Euc d)))⟫ :=
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right w _
  rw [h1, h2, s8p_Q_inner]

theorem s8p_Asub_symm (ν : ℝ) (v w : K) : ⟪s8p_Asub h K ν v, w⟫ = ⟪v, s8p_Asub h K ν w⟫ := by
  rw [s8p_Asub_inner, real_inner_comm (s8p_Asub h K ν w) v, s8p_Asub_inner, real_inner_comm v w,
    s8p_qf_symm h]

theorem s8p_Asub_low (hd : 1 ≤ d) (ν : ℝ) (v : K) : ν * ‖v‖ ^ 2 ≤ ⟪v, s8p_Asub h K ν v⟫ := by
  rw [real_inner_comm, s8p_Asub_inner, real_inner_self_eq_norm_sq]
  have := s8p_qf_self_nonneg h hd (v : Lp ℝ 2 (volume : Measure (Euc d)))
  linarith

/-- `BData` of `A` (for `ν > 0`). -/
def s8p_AData (hd : 1 ≤ d) {ν : ℝ} (hν : 0 < ν) : BData K where
  B := s8p_Asub h K ν
  symm := s8p_Asub_symm h K ν
  c := ν
  c_pos := hν
  low := fun x => s8p_Asub_low h K hd ν x

end Sub

end HRS.MS.Spec
