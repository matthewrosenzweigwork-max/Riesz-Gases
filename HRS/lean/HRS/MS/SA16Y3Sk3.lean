import HRS.MS.SA16Y3Sk2
import HRS.MS.SA16ZR5

/-!
# S.A.16 (SA16Y3) Sk3: Leibniz remainder of `∂^idx Q^i(b φ)` (packet P7, Hilbert corner)

`sa16y3_R s i b φ j idx = ∂^idx Q^i(bφ) - Q^i(b ∂^idxφ)`; exact recursion `sa16y3_R_cons`
`R_{j+1}(b,φ,l::idx) = Q^i(∂_l b ∂^idxφ) + R_j(∂_l b,φ,idx) + R_j(b,∂_lφ,idx)` and the bound
`sa16y3_R_bound`: `‖R_j(b,φ,idx)‖_p ≤ K Λ S_j(φ)` for `‖D^k b‖ ≤ Λ` (`k ≤ j+1`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.MH.AdjointRd

section Sk3
variable {d : ℕ} {s : ℝ}

/-- the remainder -/
def sa16y3_R (s : ℝ) (i : Fin d) (b φ : Euc d → ℝ) (j : ℕ) (idx : Fin j → Fin d) (x : Euc d) : ℝ :=
  partialDeriv idx (sa16y3_Q s i (fun y => b y * φ y)) x -
    sa16y3_Q s i (fun y => b y * partialDeriv idx φ y) x

lemma sa16y3_Q_smooth (hs0 : 0 ≤ s) (hsd : s < d) {f : Euc d → ℝ} (hf : IsCcInfty f) (i : Fin d) :
    ContDiff ℝ ∞ (sa16y3_Q s i f) :=
  sa16so_dir_smooth (sa16z_conv_smooth hs0 hsd hf) _

lemma sa16y3_bmul_cc {b φ : Euc d → ℝ} (hb : ContDiff ℝ ∞ b) (hφ : IsCcInfty φ) :
    IsCcInfty (fun y => b y * φ y) := ⟨hb.mul hφ.1, hφ.2.mul_left⟩

lemma sa16y3_F_deriv (hs0 : 0 ≤ s) (hsd : s < d) {b φ : Euc d → ℝ} (hb : ContDiff ℝ ∞ b) (hφ : IsCcInfty φ)
    (i l : Fin d) (x : Euc d) :
    sa16z_dm (sa16y3_Q s i (fun y => b y * φ y)) l x =
      sa16y3_Q s i (fun y => sa16z_dm b l y * φ y) x + sa16y3_Q s i (fun y => b y * sa16z_dm φ l y) x := by
  unfold sa16z_dm
  rw [sa16y3_Q_deriv hs0 hsd (sa16y3_bmul_cc hb hφ) i l x]
  have hfun : sa16z_dm (fun y => b y * φ y) l = (fun y => sa16z_dm b l y * φ y) +
      (fun y => b y * sa16z_dm φ l y) := by
    funext y
    have hd1 : DifferentiableAt ℝ b y := (hb.differentiable (by simp)) y
    have hd2 : DifferentiableAt ℝ φ y := (hφ.1.differentiable (by simp)) y
    simp only [sa16z_dm, Pi.add_apply]
    rw [fderiv_fun_mul hd1 hd2]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  rw [hfun]
  exact sa16y3_Q_add hs0 hsd (sa16y3_dm_mul_cc hb hφ l) (sa16y3_bmul_cc hb (sa16z_dm_cc hφ l)) i x

lemma sa16y3_R_zero (i : Fin d) (b φ : Euc d → ℝ) (idx : Fin 0 → Fin d) :
    (fun x => sa16y3_R s i b φ 0 idx x) = 0 := by
  funext x
  have : partialDeriv idx φ = φ := funext fun y => sa16j_pd_zero idx φ y
  simp only [sa16y3_R, sa16j_pd_zero, Pi.zero_apply]
  ring

lemma sa16y3_R_cons (hs0 : 0 ≤ s) (hsd : s < d) {b φ : Euc d → ℝ} (hb : ContDiff ℝ ∞ b) (hφ : IsCcInfty φ)
    (i : Fin d) {j : ℕ} (l : Fin d) (idx : Fin j → Fin d) (x : Euc d) :
    sa16y3_R s i b φ (j + 1) (Fin.cons l idx) x =
      sa16y3_Q s i (fun y => sa16z_dm b l y * partialDeriv idx φ y) x +
        sa16y3_R s i (sa16z_dm b l) φ j idx x + sa16y3_R s i b (sa16z_dm φ l) j idx x := by
  have hF := sa16y3_Q_smooth hs0 hsd (sa16y3_bmul_cc hb hφ) i
  have h1 : partialDeriv (Fin.cons l idx : Fin (j + 1) → Fin d) (sa16y3_Q s i (fun y => b y * φ y)) x =
      partialDeriv idx (fun y => sa16y3_Q s i (fun z => sa16z_dm b l z * φ z) y +
        sa16y3_Q s i (fun z => b z * sa16z_dm φ l z) y) x := by
    rw [sa16s_pd_cons hF l idx x]
    have := congrFun (sa16sy_pd_comm hF l idx) x
    rw [← this]
    congr 1
    funext y
    exact sa16y3_F_deriv hs0 hsd hb hφ i l y
  have hA : ContDiff ℝ ∞ (sa16y3_Q s i (fun z => sa16z_dm b l z * φ z)) :=
    sa16y3_Q_smooth hs0 hsd (sa16y3_dm_mul_cc hb hφ l) i
  have hB : ContDiff ℝ ∞ (sa16y3_Q s i (fun z => b z * sa16z_dm φ l z)) :=
    sa16y3_Q_smooth hs0 hsd (sa16y3_bmul_cc hb (sa16z_dm_cc hφ l)) i
  have h2 : partialDeriv (Fin.cons l idx : Fin (j + 1) → Fin d) φ = partialDeriv idx (sa16z_dm φ l) :=
    sa16z_pd_cons_eq hφ.1 l idx
  unfold sa16y3_R
  rw [h1, sa16sy_pd_add hA hB, h2]
  ring

end Sk3

end HRS.Whole.AppendixA.Phase2SA16R
