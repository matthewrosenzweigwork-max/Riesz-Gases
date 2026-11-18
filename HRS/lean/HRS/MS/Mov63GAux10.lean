import HRS.MS.Mov63GAux9

/-!
# S6.3, packet N8 (part 10): the abstract system for the N5-N7 solution

Namespace `HRS.MS.Mov63`, prefix `mng_`.  `mng_jc_lin`: joint continuity of all iterated partial derivatives of a linear family `u ↦ Φ(u)` along a
continuous path; `mng_proj_iter_le`: coordinates of vector fields; **`mng_conc_sys`**: for the mild solution `v` with `‖v_t‖ ≤ C_v K e^{-ct}` the data
`Q_t = mneQ (v_t)`, `b_k = (ν∇log ρ + F_t)_k`, `A_t = div F_t + ⟨∇log ρ, F_t⟩`, `a(t) = K e^{-ct}` form an `MngSys` of order `N`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

lemma mng_jc_lin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → Euc d → ℝ} {r : ℕ}
    (hlin : ∀ u u' x, Φ (u - u') x = Φ u x - Φ u' x) (hcd : ∀ u, ContDiff ℝ r (Φ u)) (C : ℝ)
    (hb : ∀ u (k : ℕ), k ≤ r → ∀ x, ‖iteratedFDeriv ℝ k (Φ u) x‖ ≤ C * ‖u‖) {v : ℝ → E}
    (hv : ContinuousOn v (Ici 0)) : mngJC r (fun t => Φ (v t)) := by
  refine mngJC_of_iter r _ (fun t => hcd (v t)) (fun k hk => ?_)
  refine mne_joint_lin (Ψ := fun u x => iteratedFDeriv ℝ k (Φ u) x) C ?_ (fun u x => hb u k hk x)
    (fun u => ((hcd u).continuous_iteratedFDeriv (by exact_mod_cast hk))) hv
  intro u u' x
  have e : Φ (u - u') = fun y => Φ u y - Φ u' y := funext (hlin u u')
  rw [e]
  exact (iteratedFDeriv_sub_apply (((hcd u).of_le (by exact_mod_cast hk)).contDiffAt)
    (((hcd u').of_le (by exact_mod_cast hk)).contDiffAt)).symm

lemma mng_proj_iter_le {F : Euc d → Euc d} {k : ℕ} (hF : ContDiff ℝ k F) (j : Fin d) (x : Euc d) :
    ‖iteratedFDeriv ℝ k (fun y => F y j) x‖ ≤ ‖iteratedFDeriv ℝ k F x‖ := by
  have h := (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).iteratedFDeriv_comp_left (f := F) hF.contDiffAt (by exact_mod_cast le_refl k)
    (x := x)
  have e : (fun y => F y j) = (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ) ∘ F := rfl
  rw [e, h]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  have : ‖(EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
    simpa using PiLp.norm_apply_le z j
  calc _ ≤ 1 * ‖iteratedFDeriv ℝ k F x‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
    _ = _ := one_mul _

lemma mng_proj_cd {F : Euc d → Euc d} {k : ℕ} (hF : ContDiff ℝ k F) (j : Fin d) :
    ContDiff ℝ k (fun y => F y j) :=
  (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).contDiff.comp hF
section Unif

variable {m : ℕ} (H : Mov2dTh d s β q ρ) (hm : (d : ℝ) / 2 + 3 < m)

include H hm in
/-- Uniform (in `u`) regularity and bounds of `V_u`, `F_u`, `A_u`. -/
lemma mng_unif {N : ℕ} (hN : (d : ℝ) / 2 + N + 2 < m) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ u : OscSpace d (m : ℝ),
      ContDiff ℝ ((N + 2 : ℕ) : WithTop ℕ∞) (mneV hm u) ∧
      (∀ k ≤ N + 2, ∀ x, ‖iteratedFDeriv ℝ k (mneV hm u) x‖ ≤ C0 * ‖u‖) ∧
      ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) (mneFo d s ρ hm u) ∧
      (∀ k ≤ N + 1, ∀ x, ‖iteratedFDeriv ℝ k (mneFo d s ρ hm u) x‖ ≤ C0 * ‖u‖) ∧
      ContDiff ℝ (N : WithTop ℕ∞) (mnfA d s ρ hm u) ∧
      (∀ k ≤ N, ∀ x, ‖iteratedFDeriv ℝ k (mnfA d s ρ hm u) x‖ ≤ C0 * ‖u‖) := by
  obtain ⟨C, hC0, hC⟩ := mn_force_bound H.hd H.hs0 H.hsd β q H.hβ H.hq ρ H.hρ N m hN
  refine ⟨C, hC0, fun u => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hC (mneV hm u) (mneV_cd hm u).continuous (mneV_memOsc hm u)
  rw [mneV_norm hm u] at h2 h5
  have hB : 0 ≤ C * ‖u‖ := mul_nonneg hC0 (norm_nonneg _)
  refine ⟨h1, h2, h3, fun k hk x => mne_cbVec_le hB h5 k hk x, h4.1, fun k hk x => ?_⟩
  have h6 : ENNReal.ofReal (HRS.cbNorm N (fun x => movDiv (movForce d s (fun y => Real.sqrt (ρ y) * mneV hm u y)) x +
        inner ℝ (gradient (fun y => Real.log (ρ y)) x)
          (movForce d s (fun y => Real.sqrt (ρ y) * mneV hm u y) x))) ≤ ENNReal.ofReal (C * ‖u‖) :=
    le_trans le_add_self h5
  have h7 := (ENNReal.ofReal_le_ofReal_iff hB).1 h6
  have h8 := mnf_norm_le_cbNorm h4 hk x
  exact h8.trans h7

end Unif

lemma mng_dlog_unif (H : Mov2dTh d s β q ρ) (N : ℕ) : ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ l, 1 ≤ l → l ≤ N → ∀ x,
    ‖iteratedFDeriv ℝ l (fun y => gradient (fun z => Real.log (ρ z)) y) x‖ ≤ Cg := by
  obtain ⟨hC, -⟩ := mng_dlog H
  choose C hC using hC
  refine ⟨∑ k ∈ Finset.range (N + 1), |C k|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun l hl hlN x => ?_⟩
  rw [mng_norm_iter_grad]
  exact (hC l hl x).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun k => |C k|) (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (by omega))))

section Conc

variable {m : ℕ} (H : Mov2dTh d s β q ρ) (hm : (d : ℝ) / 2 + 3 < m)

include H in
lemma mng_Q_eq (u : OscSpace d (m : ℝ)) : mneQ ρ hm u = fun z => 1 + mngW ρ z * mneV hm u z := by
  funext z
  rw [mnf_Q_eq hm H u z, mngW_eq H z, div_eq_inv_mul]

lemma mng_mnfb_coord (u : OscSpace d (m : ℝ)) (k : Fin d) (x : Euc d) :
    (mnfb d s β ρ hm u x) k = β⁻¹ * (gradient (fun y => Real.log (ρ y)) x) k + (mneFo d s ρ hm u x) k := by
  simp [mnfb]

lemma mng_mnfA_sub (H : Mov2dTh d s β q ρ) (hm : (d : ℝ) / 2 + 3 < m) (u u' : OscSpace d (m : ℝ)) (x : Euc d)
    (hu : Differentiable ℝ (mneFo d s ρ hm u)) (hu' : Differentiable ℝ (mneFo d s ρ hm u')) :
    mnfA d s ρ hm (u - u') x = mnfA d s ρ hm u x - mnfA d s ρ hm u' x := by
  have e : mneFo d s ρ hm (u - u') = fun y => mneFo d s ρ hm u y - mneFo d s ρ hm u' y :=
    funext (mne_Fo_sub hm H u u')
  simp only [mnfA]
  rw [e, mne_movDiv_sub (hu x) (hu' x), inner_sub_right]
  ring

end Conc


end HRS.MS.Mov63

end
