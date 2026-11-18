import HRS.MS.SA16V2Jets
import HRS.MS.SA16TransferDefs

/-!
# S.A.16 T1, part 4: the closed jet energy calculus (frozen statement `closed_jet_energy_calculus`)

`jetNorm G = (∑_j ‖T_j G‖^p)^(1/p)` where `T_j` is the order-`j` jet operator on `W^{k,p}`.
Lower bound `‖G‖ ≤ jetNorm G` by the pointwise sup-norm estimate; upper bound from the
operator norms of the `T_j`; the smooth-norm conditions follow from the `ℓ^p`-structure and
the `C^1` calculus of `jetEnergy` (`sa16v2_jetEnergy_hasFDerivAt`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.Whole.AppendixA.Phase2SA16Transfer
open HRS HRS.Whole HRS.Whole.AppendixA
open HRS.Whole.AppendixA.Phase2SA16V2 HRS.Whole.AppendixA.Phase2SA16V

section Calc
variable (d k : ℕ) (p : ℝ) [Fact (2 ≤ p)]

lemma sa16v2c_p_pos : 0 < p := by
  have : (2 : ℝ) ≤ p := Fact.out
  linarith

lemma sa16v2c_E_nonneg (G : WmpSpace d k p) : 0 ≤ jetEnergy d k p G := by
  rw [sa16v2_jetEnergy_eq_norm]
  exact Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) _

lemma sa16v2c_jetNorm_eq (G : WmpSpace d k p) :
    jetNorm d k p G = (∑ j : Fin (k+1), ‖sa16v2_T d k p j G‖ ^ p) ^ (1 / p) := by
  unfold jetNorm
  rw [sa16v2_jetEnergy_eq_norm]

lemma sa16v2c_abs_le_L (j : Fin (k+1)) (v : WIndex d k → ℝ) (idx : Fin (j : ℕ) → Fin d) :
    |v ⟨j, idx⟩| ≤ ‖sa16v2_L d k j v‖ := by
  rw [sa16v2_L_norm]
  unfold vnorm
  exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun i : Fin (j : ℕ) → Fin d => (v ⟨j, i⟩) ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ idx))

/-- pointwise: the sup norm of a jet value is controlled by the `ℓ^p` sum of its order-blocks -/
lemma sa16v2c_pointwise (v : WIndex d k → ℝ) :
    ‖v‖ ^ p ≤ ∑ j : Fin (k+1), ‖sa16v2_L d k j v‖ ^ p := by
  have hp0 := sa16v2c_p_pos p
  set S := ∑ j : Fin (k+1), ‖sa16v2_L d k j v‖ ^ p with hSdef
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) _
  have hle : ‖v‖ ≤ S ^ p⁻¹ := by
    refine (pi_norm_le_iff_of_nonneg (Real.rpow_nonneg hS _)).2 fun i => ?_
    obtain ⟨j, idx⟩ := i
    rw [Real.norm_eq_abs]
    refine le_trans (sa16v2c_abs_le_L d k j v idx) ?_
    rw [Real.le_rpow_inv_iff_of_pos (norm_nonneg _) hS hp0]
    exact Finset.single_le_sum (f := fun j : Fin (k+1) => ‖sa16v2_L d k j v‖ ^ p)
      (fun j _ => Real.rpow_nonneg (norm_nonneg _) _) (Finset.mem_univ j)
  have := Real.rpow_le_rpow (norm_nonneg _) hle hp0.le
  rwa [Real.rpow_inv_rpow hS hp0.ne'] at this

lemma sa16v2c_integrable_pow {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {V : Type*}
    [NormedAddCommGroup V] (f : Lp V (ENNReal.ofReal p) μ) : Integrable (fun x => ‖f x‖ ^ p) μ := by
  have hp0 : 0 < p := sa16v2c_p_pos p
  have h := (Lp.memLp f).integrable_norm_rpow (by simpa using hp0) ENNReal.ofReal_ne_top
  simpa [ENNReal.toReal_ofReal hp0.le] using h

lemma sa16v2c_lower (G : WmpSpace d k p) : ‖G‖ ≤ jetNorm d k p G := by
  have hp0 := sa16v2c_p_pos p
  have hpt : ∀ᵐ x ∂(volume : Measure (Euc d)),
      ‖((G : WLp d k p)) x‖ ^ p ≤ ∑ j : Fin (k+1), ‖sa16v2_T d k p j G x‖ ^ p := by
    filter_upwards [ae_all_iff.2 fun j => sa16v2_T_coe d k p j G] with x hx
    calc ‖((G : WLp d k p)) x‖ ^ p
        ≤ ∑ j : Fin (k+1), ‖sa16v2_L d k j (((G : WLp d k p)) x)‖ ^ p := sa16v2c_pointwise d k p _
      _ = ∑ j : Fin (k+1), ‖sa16v2_T d k p j G x‖ ^ p :=
          Finset.sum_congr rfl fun j _ => by rw [hx j]
  have hint2 : Integrable (fun x => ∑ j : Fin (k+1), ‖sa16v2_T d k p j G x‖ ^ p)
      (volume : Measure (Euc d)) :=
    integrable_finsetSum _ fun j _ => sa16v2c_integrable_pow p (sa16v2_T d k p j G)
  have hmono := integral_mono_of_nonneg (ae_of_all _ fun x => Real.rpow_nonneg (norm_nonneg _) _)
    hint2 hpt
  rw [integral_finsetSum _ fun j _ => sa16v2c_integrable_pow p (sa16v2_T d k p j G)] at hmono
  have hT : ∑ j : Fin (k+1), ∫ x, ‖sa16v2_T d k p j G x‖ ^ p
      = ∑ j : Fin (k+1), ‖sa16v2_T d k p j G‖ ^ p :=
    Finset.sum_congr rfl fun j _ => (sa16v2_norm_pow_eq p _).symm
  rw [hT] at hmono
  have hG : ‖G‖ ^ p = ∫ x, ‖((G : WLp d k p)) x‖ ^ p := sa16v2_norm_pow_eq p (G : WLp d k p)
  rw [← hG] at hmono
  have hS : 0 ≤ ∑ j : Fin (k+1), ‖sa16v2_T d k p j G‖ ^ p :=
    Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) _
  rw [sa16v2c_jetNorm_eq, one_div]
  exact (Real.le_rpow_inv_iff_of_pos (norm_nonneg _) hS hp0).2 hmono

lemma sa16v2c_sumT_nonneg : (0 : ℝ) ≤ ∑ j : Fin (k+1), ‖sa16v2_T d k p j‖ ^ p :=
  Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg (sa16v2_T d k p j)) _

lemma sa16v2c_jetNorm_nonneg (G : WmpSpace d k p) : 0 ≤ jetNorm d k p G := by
  unfold jetNorm
  exact Real.rpow_nonneg (sa16v2c_E_nonneg d k p G) _

lemma sa16v2c_pow_eq (G : WmpSpace d k p) : (jetNorm d k p G) ^ p = jetEnergy d k p G := by
  unfold jetNorm
  rw [one_div]
  exact Real.rpow_inv_rpow (sa16v2c_E_nonneg d k p G) (sa16v2c_p_pos p).ne'

lemma sa16v2c_upper (G : WmpSpace d k p) :
    jetNorm d k p G ≤ (∑ j : Fin (k+1), ‖sa16v2_T d k p j‖ ^ p) ^ (1 / p) * ‖G‖ := by
  have hp0 := sa16v2c_p_pos p
  have hA0 : (0 : ℝ) ≤ ∑ j : Fin (k+1), ‖sa16v2_T d k p j‖ ^ p := sa16v2c_sumT_nonneg d k p
  have hterm : ∀ j : Fin (k+1), ‖sa16v2_T d k p j G‖ ^ p ≤ ‖sa16v2_T d k p j‖ ^ p * ‖G‖ ^ p := by
    intro j
    calc ‖sa16v2_T d k p j G‖ ^ p ≤ (‖sa16v2_T d k p j‖ * ‖G‖) ^ p :=
          Real.rpow_le_rpow (norm_nonneg (sa16v2_T d k p j G)) ((sa16v2_T d k p j).le_opNorm G) hp0.le
      _ = ‖sa16v2_T d k p j‖ ^ p * ‖G‖ ^ p :=
          Real.mul_rpow (norm_nonneg (sa16v2_T d k p j)) (norm_nonneg G)
  have hsum : ∑ j : Fin (k+1), ‖sa16v2_T d k p j G‖ ^ p
      ≤ (∑ j : Fin (k+1), ‖sa16v2_T d k p j‖ ^ p) * ‖G‖ ^ p := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => hterm j
  rw [sa16v2c_jetNorm_eq, one_div]
  calc (∑ j : Fin (k+1), ‖sa16v2_T d k p j G‖ ^ p) ^ p⁻¹
      ≤ ((∑ j : Fin (k+1), ‖sa16v2_T d k p j‖ ^ p) * ‖G‖ ^ p) ^ p⁻¹ :=
        Real.rpow_le_rpow (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg (sa16v2_T d k p j G)) _)
          hsum (inv_nonneg.2 hp0.le)
    _ = (∑ j : Fin (k+1), ‖sa16v2_T d k p j‖ ^ p) ^ p⁻¹ * ‖G‖ := by
        rw [Real.mul_rpow hA0 (Real.rpow_nonneg (norm_nonneg _) _), ← Real.rpow_mul (norm_nonneg _),
          mul_inv_cancel₀ hp0.ne', Real.rpow_one]

lemma sa16v2c_smul (a : ℝ) (G : WmpSpace d k p) :
    jetNorm d k p (a • G) = |a| * jetNorm d k p G := by
  have hp0 := sa16v2c_p_pos p
  have hT : ∀ j : Fin (k+1), ‖sa16v2_T d k p j (a • G)‖ ^ p = |a| ^ p * ‖sa16v2_T d k p j G‖ ^ p := by
    intro j
    rw [map_smul, norm_smul, Real.norm_eq_abs, Real.mul_rpow (abs_nonneg a) (norm_nonneg _)]
  rw [sa16v2c_jetNorm_eq, sa16v2c_jetNorm_eq]
  simp only [hT]
  rw [← Finset.mul_sum, one_div, Real.mul_rpow (Real.rpow_nonneg (abs_nonneg a) _)
    (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) _),
    Real.rpow_rpow_inv (abs_nonneg a) hp0.ne']

lemma sa16v2c_add (G H : WmpSpace d k p) :
    jetNorm d k p (G + H) ≤ jetNorm d k p G + jetNorm d k p H := by
  have hp0 := sa16v2c_p_pos p
  have hp1 : (1 : ℝ) ≤ p := by
    have : (2 : ℝ) ≤ p := Fact.out
    linarith
  have hterm : ∀ j : Fin (k+1), ‖sa16v2_T d k p j (G + H)‖ ≤ ‖sa16v2_T d k p j G‖ + ‖sa16v2_T d k p j H‖ :=
    fun j => by rw [map_add]; exact norm_add_le _ _
  have hsum : ∑ j : Fin (k+1), ‖sa16v2_T d k p j (G + H)‖ ^ p
      ≤ ∑ j : Fin (k+1), (‖sa16v2_T d k p j G‖ + ‖sa16v2_T d k p j H‖) ^ p :=
    Finset.sum_le_sum fun j _ => Real.rpow_le_rpow (norm_nonneg _) (hterm j) hp0.le
  rw [sa16v2c_jetNorm_eq, sa16v2c_jetNorm_eq, sa16v2c_jetNorm_eq]
  calc (∑ j : Fin (k+1), ‖sa16v2_T d k p j (G + H)‖ ^ p) ^ (1 / p)
      ≤ (∑ j : Fin (k+1), (‖sa16v2_T d k p j G‖ + ‖sa16v2_T d k p j H‖) ^ p) ^ (1 / p) :=
        Real.rpow_le_rpow (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) _) hsum
          (one_div_nonneg.2 hp0.le)
    _ ≤ (∑ j : Fin (k+1), ‖sa16v2_T d k p j G‖ ^ p) ^ (1 / p)
          + (∑ j : Fin (k+1), ‖sa16v2_T d k p j H‖ ^ p) ^ (1 / p) :=
        Real.Lp_add_le_of_nonneg (s := Finset.univ) (f := fun j : Fin (k+1) => ‖sa16v2_T d k p j G‖)
          (g := fun j : Fin (k+1) => ‖sa16v2_T d k p j H‖) hp1
          (fun j _ => norm_nonneg _) (fun j _ => norm_nonneg _)

theorem closed_jet_energy_calculus (d k : ℕ) (p : ℝ) [Fact (2 ≤ p)] :
    IsSmoothNorm p (jetNorm d k p) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ G : WmpSpace d k p,
      ‖G‖ ≤ jetNorm d k p G ∧ jetNorm d k p G ≤ C*‖G‖) ∧
    (∀ G : WmpSpace d k p, (jetNorm d k p G)^p=jetEnergy d k p G) ∧
    (∀ G H : WmpSpace d k p,
      Integrable (fun x => closedPairDensity d k p G H x) volume ∧
      fderiv ℝ (jetEnergy d k p) G H=p*∫ x, closedPairDensity d k p G H x) := by
  have hA0 : (0 : ℝ) ≤ (∑ j : Fin (k+1), ‖sa16v2_T d k p j‖ ^ p) ^ (1 / p) :=
    Real.rpow_nonneg (sa16v2c_sumT_nonneg d k p) _
  have hfun : (fun G : WmpSpace d k p => (jetNorm d k p G) ^ p) = jetEnergy d k p :=
    funext fun G => sa16v2c_pow_eq d k p G
  have hderiv : fderiv ℝ (jetEnergy d k p) = fun G => sa16v2_Dj d k p G :=
    funext fun G => (sa16v2_jetEnergy_hasFDerivAt d k p G).fderiv
  refine ⟨?_, ⟨(∑ j : Fin (k+1), ‖sa16v2_T d k p j‖ ^ p) ^ (1 / p) + 1, by linarith,
    fun G => ⟨sa16v2c_lower d k p G, ?_⟩⟩, sa16v2c_pow_eq d k p, fun G H => ?_⟩
  · refine
      { nonneg := fun G => sa16v2c_jetNorm_nonneg d k p G
        zero := fun G => ⟨fun h => ?_, fun h => ?_⟩
        smul := fun a G => sa16v2c_smul d k p a G
        add := fun G H => sa16v2c_add d k p G H
        equivalent := ⟨1, (∑ j : Fin (k+1), ‖sa16v2_T d k p j‖ ^ p) ^ (1 / p) + 1, one_pos, by linarith, fun G => ⟨by rw [one_mul]; exact sa16v2c_lower d k p G, ?_⟩⟩
        differentiable := ?_
        cont_deriv := ?_ }
    · have h1 := sa16v2c_lower d k p G
      rw [h] at h1
      exact norm_le_zero_iff.1 h1
    · subst h
      have h2 := sa16v2c_upper d k p 0
      rw [norm_zero, mul_zero] at h2
      exact le_antisymm h2 (sa16v2c_jetNorm_nonneg d k p 0)
    · exact le_trans (sa16v2c_upper d k p G)
        (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
    · show Differentiable ℝ (fun x => (jetNorm d k p x) ^ p)
      rw [hfun]
      exact fun G => (sa16v2_jetEnergy_hasFDerivAt d k p G).differentiableAt
    · show Continuous (fderiv ℝ (fun x => (jetNorm d k p x) ^ p))
      rw [hfun, hderiv]
      exact sa16v2_Dj_continuous d k p
  · exact le_trans (sa16v2c_upper d k p G)
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  · obtain ⟨h1, h2⟩ := sa16v2_pairDensity d k p G H
    refine ⟨h1, ?_⟩
    rw [(sa16v2_jetEnergy_hasFDerivAt d k p G).fderiv]
    exact h2

end Calc

end HRS.Whole.AppendixA.Phase2SA16Transfer
