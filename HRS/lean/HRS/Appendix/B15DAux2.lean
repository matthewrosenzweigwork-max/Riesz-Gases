import HRS.Appendix.B15DAux1
import HRS.PDE.TorusFPCompare

/-!
# Packet D2 (proofs, part 2): relocated proofs of the `b15d_*` and `d1_*` D2 targets

Each `theorem <name>_proof` restates the frozen sorried statement of `HRS/Appendix/B15DAux1.lean` verbatim
(the frozen sorried copies are left in place).  Helpers are prefixed `b15d2_`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

section D2proofs

variable {d N : ℕ}

/-- Proof of `b15d_liftedDriftReg_continuous`: the drift is the frozen `b15c_liftedDriftReg`, which is
globally Lipschitz (`b15c_liftedDriftReg_isLipschitz_proof`), hence continuous. -/
theorem b15d_liftedDriftReg_continuous_proof (D : DynData d) (hV : Torus.IsCk 2 D.V) (M : ℝ) :
    Continuous (d1_liftDrift (b15d_configDriftReg (N := N) D M)) := by
  change Continuous (b15c_liftedDriftReg D M : (Fin N → Euc d) → Fin N → Euc d)
  obtain ⟨L, hL⟩ := (b15c_liftedDriftReg_isLipschitz_proof (N := N) D hV M).lip 0
  exact (hL 0 ⟨le_rfl, le_rfl⟩).continuous

example := (@b15d_liftedDriftReg_continuous_proof : type_of% @b15d_liftedDriftReg_continuous)

/-- Proof of `b15d_U_isSmooth`: `d1_cl (b15d_U D M)` is the regularised potential on the covering space,
which is `C^∞` by `b15c_potentialReg_contDiff` (at `n = ⊤`) when `V` is `C^∞`. -/
theorem b15d_U_isSmooth_proof (D : DynData d) (hV : Torus.IsSmooth D.V) (M : ℝ) :
    Torus.IsSmooth (b15d_U (N := N) D M) := by
  refine (d1_isCk_iff (N := N) _ _).2 ?_
  rw [b15d_cl_U]
  exact b15c_potentialReg_contDiff D (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) le_rfl hV M

example := (@b15d_U_isSmooth_proof : type_of% @b15d_U_isSmooth)

/-- Lattice-invariance of the second derivative of a lifted test function: if the lifts of `Y` and `Y'`
agree on the torus, `D²(configLift Φ r)` agrees at `Y` and `Y'`. -/
theorem b15d2_fderiv2_eq_of_mk (Φ : ℝ → Config d N → ℝ) (r : ℝ) {Y Y' : Fin N → Euc d}
    (h : ∀ i, Torus.mk (Y i) = Torus.mk (Y' i)) :
    fderiv ℝ (fderiv ℝ (configLift Φ r)) Y = fderiv ℝ (fderiv ℝ (configLift Φ r)) Y' := by
  obtain ⟨v, hv, rfl⟩ := exists_lattice_shift h
  exact (fderiv2_configLift_add_lattice Φ r hv Y).symm

/-- Proof of `d1_itoGen_eq_configGen`: the time derivative is `d1_isC12On_of_isC12Test`, the second-order
part uses `σ_k = √(2κ) e_k` and `Real.mul_self_sqrt`, and the spatial derivatives are moved from `Y` to
`rep ∘ mk ∘ Y` by lattice invariance. -/
theorem d1_itoGen_eq_configGen_proof {κ : ℝ} (hκ : 0 ≤ κ) {bC : Config d N → Fin N → Euc d} {τ : ℝ}
    (hτ : 0 < τ) {Φ Φt : ℝ → Config d N → ℝ}
    (hΦ : IsC12Test τ (fun r => Φ r ∘ (d1_configEquiv d N).symm)
      (fun r => Φt r ∘ (d1_configEquiv d N).symm))
    {s : ℝ} (hs : s ∈ Set.Icc 0 τ) (Y : Fin N → Euc d) :
    d1_itoGen κ bC τ (fun r => d1_cl (Φ r ∘ (d1_configEquiv d N).symm)) s Y =
      Φt s (fun i => Torus.mk (Y i)) + d1_configGen κ bC (Φ s) (fun i => Torus.mk (Y i)) := by
  have hf : ∀ r, d1_cl (Φ r ∘ (d1_configEquiv d N).symm) = configLift Φ r := by
    intro r
    funext Z
    simp [d1_cl, configLift]
  have ht := (d1_isC12On_of_isC12Test_proof hτ hΦ).2 s hs Y
  have hT : derivWithin (fun r => configLift Φ r Y) (Set.Icc 0 τ) s
      = Φt s (fun i => Torus.mk (Y i)) := by
    have h' := ht
    simp only [hf, Function.comp_apply, MeasurableEquiv.symm_apply_apply] at h'
    exact h'
  have hmk : ∀ i, Torus.mk (Y i) = Torus.mk (Torus.rep (Torus.mk (Y i))) :=
    fun i => (Torus.mk_rep _).symm
  have hF1 : fderiv ℝ (configLift Φ s) Y
      = fderiv ℝ (configLift Φ s) (fun i => Torus.rep (Torus.mk (Y i))) :=
    fderiv_configLift_eq_of_mk Φ s hmk
  have hF2 : fderiv ℝ (fderiv ℝ (configLift Φ s)) Y
      = fderiv ℝ (fderiv ℝ (configLift Φ s)) (fun i => Torus.rep (Torus.mk (Y i))) :=
    b15d2_fderiv2_eq_of_mk Φ s hmk
  have hc : configLift (fun _ : ℝ => Φ s) 0 = configLift Φ s := rfl
  have hsq : ∀ k, fderiv ℝ (fderiv ℝ (configLift Φ s)) Y (d1_noise d N κ k) (d1_noise d N κ k)
      = 2 * κ * fderiv ℝ (fderiv ℝ (configLift Φ s)) Y (configBasis d N k) (configBasis d N k) := by
    intro k
    have hsn : d1_noise d N κ k = Real.sqrt (2 * κ) • configBasis d N k := rfl
    have h2 : Real.sqrt (2 * κ) * Real.sqrt (2 * κ) = 2 * κ := Real.mul_self_sqrt (by linarith)
    rw [hsn]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    linear_combination (fderiv ℝ (fderiv ℝ (configLift Φ s)) Y (configBasis d N k) (configBasis d N k)) * h2
  simp only [d1_itoGen, d1_configGen, hf, d1_liftDrift]
  rw [hT, hc]
  simp only [hsq]
  simp only [← hF1, ← hF2]
  rw [← Finset.mul_sum]
  ring

example := (@d1_itoGen_eq_configGen_proof : type_of% @d1_itoGen_eq_configGen)

end D2proofs

end HRS
