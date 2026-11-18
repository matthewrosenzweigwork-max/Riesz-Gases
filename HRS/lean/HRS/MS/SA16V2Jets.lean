import HRS.MS.SA16V6
import HRS.MS.SA16TransferDefs

/-!
# S.A.16 T1, part 3: the jet spaces
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.Whole.AppendixA.Phase2SA16V2
open HRS.Whole.AppendixA.Phase2SA16V
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16Transfer

section Jets
variable (d k : ℕ) (p : ℝ) [Fact (2 ≤ p)]

/-- the order-`j` component of a jet value, as a Euclidean vector -/
def sa16v2_L (j : Fin (k + 1)) : (WIndex d k → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (j : ℕ) → Fin d) :=
  (EuclideanSpace.equiv (Fin (j : ℕ) → Fin d) ℝ).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun idx : Fin (j : ℕ) → Fin d =>
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : WIndex d k => ℝ) (⟨j, idx⟩ : WIndex d k))

lemma sa16v2_L_apply (j : Fin (k + 1)) (v : WIndex d k → ℝ) (idx : Fin (j : ℕ) → Fin d) :
    sa16v2_L d k j v idx = v ⟨j, idx⟩ := rfl

lemma sa16v2_L_norm (j : Fin (k + 1)) (v : WIndex d k → ℝ) :
    ‖sa16v2_L d k j v‖ = vnorm (fun idx : Fin (j : ℕ) → Fin d => v ⟨j, idx⟩) := by
  rw [EuclideanSpace.norm_eq]
  unfold vnorm
  congr 1
  refine Finset.sum_congr rfl fun idx _ => ?_
  rw [Real.norm_eq_abs, sq_abs]
  rfl

lemma sa16v2_L_inner (j : Fin (k + 1)) (v w : WIndex d k → ℝ) :
    ⟪sa16v2_L d k j v, sa16v2_L d k j w⟫ = ∑ idx : Fin (j : ℕ) → Fin d, v ⟨j, idx⟩ * w ⟨j, idx⟩ := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun idx _ => ?_
  simp only [RCLike.inner_apply, conj_trivial]
  rw [mul_comm]
  rfl

/-- `G ↦ (x ↦ order-j part of G(x))` as a bounded operator `W^{k,p} → L^p(ℝ^d; ℝ^{d^j})` -/
def sa16v2_T (j : Fin (k + 1)) : WmpSpace d k p →L[ℝ]
    Lp (EuclideanSpace ℝ (Fin (j : ℕ) → Fin d)) (ENNReal.ofReal p) (volume : Measure (Euc d)) :=
  ((sa16v2_L d k j).compLpL (ENNReal.ofReal p) volume) ∘L (WmpSpace d k p).subtypeL

lemma sa16v2_T_coe (j : Fin (k + 1)) (G : WmpSpace d k p) :
    (sa16v2_T d k p j G : Euc d → EuclideanSpace ℝ (Fin (j : ℕ) → Fin d)) =ᵐ[volume]
      fun x => sa16v2_L d k j (((G : WLp d k p) : Euc d → (WIndex d k → ℝ)) x) :=
  ContinuousLinearMap.coeFn_compLpL (sa16v2_L d k j) (G : WLp d k p)

lemma sa16v2_T_norm (j : Fin (k + 1)) (G : WmpSpace d k p) :
    ∀ᵐ x ∂(volume : Measure (Euc d)), ‖(sa16v2_T d k p j G) x‖ = vnorm (closedTensor d k p G j x) := by
  filter_upwards [sa16v2_T_coe d k p j G] with x hx
  rw [hx, sa16v2_L_norm]
  rfl

lemma sa16v2_jetEnergy_eq (G : WmpSpace d k p) :
    jetEnergy d k p G = ∑ j : Fin (k + 1), sa16v_Psi p (sa16v2_T d k p j G) := by
  unfold jetEnergy sa16v_Psi
  refine Finset.sum_congr rfl fun j _ => ?_
  refine integral_congr_ae ?_
  filter_upwards [sa16v2_T_norm d k p j G] with x hx
  rw [hx]

lemma sa16v2_norm_pow_eq {E : Type*} [NormedAddCommGroup E] {α : Type*} {m : MeasurableSpace α}
    {μ : Measure α} (f : Lp E (ENNReal.ofReal p) μ) : ‖f‖ ^ p = ∫ x, ‖f x‖ ^ p ∂μ := by
  have hp0 : 0 < p := by have : (2 : ℝ) ≤ p := Fact.out; linarith
  have hP0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have h := (Lp.memLp f).eLpNorm_eq_integral_rpow_norm hP0 ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_ofReal hp0.le] at h
  have hnn : 0 ≤ ∫ x, ‖f x‖ ^ p ∂μ := integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have h2 : ‖f‖ = (∫ x, ‖f x‖ ^ p ∂μ) ^ p⁻¹ := by
    rw [Lp.norm_def, h, ENNReal.toReal_ofReal (Real.rpow_nonneg hnn _)]
  rw [h2, Real.rpow_inv_rpow hnn hp0.ne']

lemma sa16v2_jetEnergy_eq_norm (G : WmpSpace d k p) :
    jetEnergy d k p G = ∑ j : Fin (k + 1), ‖sa16v2_T d k p j G‖ ^ p := by
  rw [sa16v2_jetEnergy_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold sa16v_Psi
  exact (sa16v2_norm_pow_eq p _).symm

/-- the derivative of the jet energy -/
def sa16v2_Dj (G : WmpSpace d k p) : WmpSpace d k p →L[ℝ] ℝ :=
  ∑ j : Fin (k + 1), (sa16v_D p (sa16v2_T d k p j G)).comp (sa16v2_T d k p j)

theorem sa16v2_jetEnergy_hasFDerivAt (G : WmpSpace d k p) :
    HasFDerivAt (jetEnergy d k p) (sa16v2_Dj d k p G) G := by
  have hfun : jetEnergy d k p = fun G => ∑ j : Fin (k + 1), sa16v_Psi p (sa16v2_T d k p j G) :=
    funext (sa16v2_jetEnergy_eq d k p)
  rw [hfun]
  exact HasFDerivAt.fun_sum fun j _ =>
    (sa16v_hasFDerivAt p (sa16v2_T d k p j G)).comp G (sa16v2_T d k p j).hasFDerivAt

theorem sa16v2_Dj_continuous : Continuous (sa16v2_Dj d k p) := by
  unfold sa16v2_Dj
  have : ContinuousAdd (WmpSpace d k p →L[ℝ] ℝ) :=
    (inferInstance : IsTopologicalAddGroup (WmpSpace d k p →L[ℝ] ℝ)).toContinuousAdd
  refine continuous_finsetSum _ fun j _ => ?_
  exact ((sa16v_D_continuous p).comp (sa16v2_T d k p j).continuous).clm_comp continuous_const

lemma sa16v2_pair_ae (j : Fin (k + 1)) (G H : WmpSpace d k p) :
    ∀ᵐ x ∂(volume : Measure (Euc d)),
      ⟪(sa16v2_T d k p j H) x, sa16v_g (p - 2) ((sa16v2_T d k p j G) x)⟫ =
        vnorm (closedTensor d k p G j x) ^ (p - 2) *
          ∑ idx : Fin (j : ℕ) → Fin d, closedTensor d k p G j x idx * closedTensor d k p H j x idx := by
  filter_upwards [sa16v2_T_coe d k p j G, sa16v2_T_coe d k p j H] with x h1 h2
  rw [h1, h2]
  unfold sa16v_g
  rw [real_inner_smul_right, sa16v2_L_norm, sa16v2_L_inner]
  congr 1
  exact Finset.sum_congr rfl (fun idx _ => mul_comm _ _)

theorem sa16v2_pairDensity (G H : WmpSpace d k p) :
    Integrable (closedPairDensity d k p G H) volume ∧
      sa16v2_Dj d k p G H = p * ∫ x, closedPairDensity d k p G H x := by
  have hint : ∀ j : Fin (k + 1), Integrable (fun x => vnorm (closedTensor d k p G j x) ^ (p - 2) *
      ∑ idx : Fin (j : ℕ) → Fin d, closedTensor d k p G j x idx * closedTensor d k p H j x idx)
      volume := by
    intro j
    exact (sa16v_inner_integrable p (sa16v2_T d k p j H) (sa16v2_T d k p j G)).congr (sa16v2_pair_ae d k p j G H)
  have hdens : closedPairDensity d k p G H = fun x => ∑ j : Fin (k + 1),
      vnorm (closedTensor d k p G j x) ^ (p - 2) *
        ∑ idx : Fin (j : ℕ) → Fin d, closedTensor d k p G j x idx * closedTensor d k p H j x idx := rfl
  refine ⟨?_, ?_⟩
  · rw [hdens]
    exact integrable_finset_sum _ fun j _ => hint j
  · rw [hdens, integral_finset_sum _ fun j _ => hint j, Finset.mul_sum]
    unfold sa16v2_Dj
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.comp_apply, sa16v_D_apply, ← integral_congr_ae (sa16v2_pair_ae d k p j G H)]

end Jets

end HRS.Whole.AppendixA.Phase2SA16V2
