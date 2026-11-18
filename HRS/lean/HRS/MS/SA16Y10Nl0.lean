import HRS.MS.SA16Y10Hm1

/-!
# S.A.16 (SA16Y10) Nl0: scaling lemmas for the difference operator `W^{m+2} → W^m`
-/

set_option autoImplicit false

noncomputable section
open scoped ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA MeasureTheory Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- `T : W^{m+2} → W^m` represents the nonlocal operator of the coefficient `a` on `C_c^∞` -/
def SA16NlRep (d m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ)
    (T : WmpSpace d (m + 2) p →L[ℝ] WmpSpace d m p) (a : Euc d → ℝ) : Prop :=
  ∀ φ : ccSub d, wrep d m p (T (sa16r_Jcc d (m + 2) p φ)) =ᵐ[volume] HRS.MH.AdjointRd.eucNonlocal s M a φ.1

lemma sa16y10_rep_smul {m : ℕ} {s : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {T : WmpSpace d (m + 2) p →L[ℝ] WmpSpace d m p}
    {a : Euc d → ℝ} (h : SA16NlRep d m p s M T a) (c : ℝ) :
    SA16NlRep d m p s M (c • T) (fun y => c * a y) := by
  intro φ
  filter_upwards [h φ, sa16r_wrep_smul d m p c (T (sa16r_Jcc d (m + 2) p φ))] with x e1 e2
  rw [ContinuousLinearMap.smul_apply, e2, e1, sa16y10_euc_smul]

lemma sa16y10_SB_smul {a : Euc d → ℝ} (h : sa16q_SB a) (c : ℝ) : sa16q_SB (fun y => c * a y) := by
  refine ⟨contDiff_const.mul h.1, fun n => ?_⟩
  obtain ⟨B, hB⟩ := h.2 n
  refine ⟨|c| * B, fun x => ?_⟩
  have hc : ContDiffAt ℝ n (fun y => a y) x := (h.1.of_le (by exact_mod_cast le_top)).contDiffAt
  have e : iteratedFDeriv ℝ n (fun y => c * a y) x = c • iteratedFDeriv ℝ n a x :=
    iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := c) (f := a) (x := x) (i := n) hc
  rw [e, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hB x) (abs_nonneg c)

end HRS.Whole.AppendixA.Phase2SA16R

end
