import HRS.MS.MfeConfAux123

/-!
# S.B.1 (SB5), R1b (part 1): the one-body remainder in terms of the force defect `e = u^k - v`

`sb1_Bone_eq`: for `r ∈ [0,T]`, `Bone(x) = ∑_j [cv(h_jj) - ∂_jF_j](x) + θ⁻¹ ∑_j e_j(x)(U_j(x) - ∂_jV(x))`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section Main

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ) (hT : 0 ≤ T)
  {r₀ : ℝ} {k : Euc d → ℝ}

include H hT

theorem sb1_Bone_eq (hk4 : IsP4Kernel d D.s r₀ k) (hθ : 0 < D.invβ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T)
    (x : Euc d) :
    sb1_lv_Bone D k hT ρ r x =
      (∑ j, sb1_lv_cv (sb1_lv_hjj k j) (ρ r) x - ∑ j, fderiv ℝ (sb1F d D.s (ρ r) j) x (sb1e j)) +
        D.invβ⁻¹ * ∑ j, sb1_lv_e D k hT ρ r x j * (sb1_lv_U D k hT ρ r x j - fderiv ℝ D.V x (sb1e j)) := by
  obtain ⟨Lg, hRg⟩ := sb1_lv_kerR hk4 H.tr.hs0
  obtain ⟨L2, -, hL2⟩ := sb1_lv_hess_bound hk4
  have hrb : sb1_lv_rb hT ρ r = ρ r := sb1_lv_rb_mem hT ρ hr
  have hTh := sb1_lv_Theta_eq H.tr.V hk4 H.tr.hd H.tr.hs0 H.tr.hsd hRg hRg.gbd hL2 (sb1_lv_rb_rho H hT r)
    (sb1_lv_rb_slice H hT r) (sb1_lv_rb_pos H hT r) (fun x => sb1_lv_cv k (sb1At D hT ρ r) x) x
  have hGv : fderiv ℝ (sb1G k (sb1_lv_rb hT ρ r)) x (Whole.mfeTransportW D (sb1_lv_rb hT ρ r) x) =
      ∑ j, sb1_lv_a k (sb1_lv_rb hT ρ r) j x * Whole.mfeTransportW D (sb1_lv_rb hT ρ r) x j := by
    rw [sb1_clm_expand]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hee : ∀ j, sb1_lv_e D k hT ρ r x j = sb1_lv_a k (sb1_lv_rb hT ρ r) j x - sb1F d D.s (sb1_lv_rb hT ρ r) j x := by
    intro j
    unfold sb1_lv_e sb1_lv_U
    exact sb1_lv_u_sub_v hk4 H.tr.hd H.tr.hs0 H.tr.hsd hRg H.tr.V (sb1_lv_rb_rho H hT r)
      (sb1_lv_rb_slice H hT r) (sb1_lv_rb_pos H hT r) x j
  unfold sb1_lv_Bone sb1_lv_Th
  rw [hTh, hGv]
  simp only [hee, hrb]
  have hθ0 := hθ.ne'
  have hU : ∀ j, sb1_lv_U D k hT ρ r x j = sb1_lv_u D k (ρ r) x j := fun j => by
    unfold sb1_lv_U; rw [hrb]
  simp only [hU]
  field_simp
  ring

end Main

end HRS.MS.MfeConf
