import HRS.MS.MfeConfAux61

/-!
# S.B.1, packet F6 (part 23): the static Hamiltonian of the regularised particle system

`sb1Hs D k N Z = (1/(2N)) ∑_i ∑_{j≠i} k(Z_i - Z_j) + ∑_i V(Z_i)`; `sb1_hasFDerivAt_Hs`: `∇ sb1Hs = -sb1DriftM` for an even
differentiable kernel `k`; `sb1_molData_regularised`: the laws of the regularised solutions `Y^M` carry the `P4MolData` of
the mollified entropy inequality (`sb1_level_ineq`) for the static potential `sb1Hs`.
-/

open MeasureTheory Filter Topology InformationTheory
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

/-- The static Hamiltonian of the regularised system. -/
def sb1Hs (D : Whole.WholeDyn d) (k : Euc d → ℝ) (N : ℕ) (Z : Whole.EucConfig d N) : ℝ :=
  (1 / (2 * (N : ℝ))) * p4k_pairSum k N Z + ∑ i, D.V (Z i)

theorem sb1_hasFDerivAt_Hs (D : Whole.WholeDyn d) {k : Euc d → ℝ} (hk : Differentiable ℝ k)
    (hev : ∀ x, k (-x) = k x) (hV : Differentiable ℝ D.V) (N : ℕ) (Z : Whole.EucConfig d N) :
    HasFDerivAt (sb1Hs D k N) (-(p4InnerL (sb1DriftM D k N Z))) Z := by
  have h1 := (p4k_pairSum_hasFDeriv hk Z).const_mul (1 / (2 * (N : ℝ)))
  have h2 : HasFDerivAt (fun Z : Whole.EucConfig d N => ∑ i, D.V (Z i))
      (∑ i, (fderiv ℝ D.V (Z i)).comp (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin N => Euc d) i)) Z :=
    HasFDerivAt.fun_sum fun i _ => (hV (Z i)).hasFDerivAt.comp Z (hasFDerivAt_apply i Z)
  have h3 := h1.add h2
  refine (show HasFDerivAt (sb1Hs D k N) _ Z from h3).congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  rw [p4k_pair_apply hk hev, p4k_p4InnerL_apply]
  have e : ∀ i, inner ℝ (sb1DriftM D k N Z i) (v i) =
      -((1 / (N : ℝ)) * inner ℝ (∑ j ∈ Finset.univ.erase i, gradient k (Z i - Z j)) (v i) +
        fderiv ℝ D.V (Z i) (v i)) := fun i => by
    simp only [sb1DriftM, PiLp.sub_apply, PiLp.neg_apply, inner_sub_left, inner_neg_left,
      real_inner_smul_left, p4k_inner_grad]
    ring
  simp only [e, Finset.sum_neg_distrib, neg_neg, Finset.sum_add_distrib, ← Finset.mul_sum,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  rcases eq_or_ne (N : ℝ) 0 with h | h
  · have hN0 : N = 0 := by exact_mod_cast h
    subst hN0
    simp
  · field_simp

theorem sb1_hasFDerivAt_Hs' (D : Whole.WholeDyn d) {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k)
    {B : ℝ} (P : Sb1Pot D.V B) (N : ℕ) (Z : Whole.EucConfig d N) :
    HasFDerivAt (sb1Hs D k N) (-(p4InnerL (sb1DriftM D k N Z))) Z :=
  sb1_hasFDerivAt_Hs D ((hk.smooth.differentiable (by norm_num))) hk.even
    ((P.c3.differentiable (by norm_num))) N Z

theorem sb1_molData_regularised {θ T : ℝ} (hT : 0 ≤ T) (D : Whole.WholeDyn d) {s r₀ : ℝ} {k : Euc d → ℝ}
    (hk : IsP4Kernel d s r₀ k) {B₀ : ℝ} (P : Sb1Pot D.V B₀) (N : ℕ)
    {μ : ℝ → Measure (Whole.EucConfig d N)} (hμ : P4FlowHyp θ (fun _ => sb1DriftM D k N) T μ) :
    ∃ (Kl : ℝ≥0) (B K M CV : ℝ), P4MolData θ T (fun _ => sb1DriftM D k N) (fun _ => sb1Hs D k N)
      (fun _ _ => 0) (fun r => μ (p4m_clamp T r)) Kl B K M CV := by
  obtain ⟨Kl, hKl⟩ := sb1_driftM_lip D hk P N
  have hH := sb1_hasFDerivAt_Hs' D hk P (N := N)
  have hHc : Continuous (sb1Hs D k N) := continuous_iff_continuousAt.2 fun x => (hH x).continuousAt
  obtain ⟨B, K, M, CV, h⟩ := sb1_molData_static hT hKl hHc hH hμ
  exact ⟨Kl, B, K, M, CV, h⟩

end HRS.MS.MfeConf
