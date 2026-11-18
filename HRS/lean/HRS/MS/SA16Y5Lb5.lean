import HRS.MS.SA16Y5Lb4
import HRS.MS.SA16Y5Cv4

/-!
# S.A.16 (SA16Y5) Lb5: the bilinear heat-composed operator `T(P,Q)` (K2 jets, part 1)

`sa16y5_T a ε i j P Q = rn_ε ⋆ (∂_j∂_i g_a ⋆ P) - rn_ε ⋆ (∂_i g_a ⋆ Q) + V_{ε,i} ⋆ (∂_j g_a ⋆ P) - V_{ε,i} ⋆ (g_a ⋆ Q)`.
For `P, Q ∈ C_c^∞` it is smooth, commutes with partial derivatives (`sa16y5_T_pd`) and
`‖T(P,Q)‖_p ≤ C a^{-(s+2-d)/2} (‖P‖_p + ‖Q‖_p)` for `ε = √a`, `a ≤ 1` (`sa16y5_T_bound`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Lb5
variable {d : ℕ} {s : ℝ}

def sa16y5_T (d : ℕ) (s a ε : ℝ) (i j : Fin d) (P Q : Euc d → ℝ) : Euc d → ℝ :=
  fun x => sa16r_cv (sa16y5_rn d s ε) (sa16r_cv (sa16y5_ddg d a j i) P) x
    - sa16r_cv (sa16y5_rn d s ε) (sa16r_cv (sa16r_dg d a i) Q) x
    + sa16r_cv (sa16y5_V d s ε i) (sa16r_cv (sa16r_dg d a j) P) x
    - sa16r_cv (sa16y5_V d s ε i) (sa16r_cv (sa16r_g d a) Q) x

theorem sa16y5_Tm_eq_T (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hsd1 : (d : ℝ) < s + 1) {a : ℝ} (ha : 0 < a)
    {ε : ℝ} (hε : 0 < ε) {μ' v : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ') (hv : IsCcInfty v) (i j : Fin d) :
    sa16y5_Tm d s a μ' i j v = sa16y5_T d s a ε i j (fun y => μ' y * v y)
      (fun y => fderiv ℝ μ' y (sa16z_e j) * v y) := by
  funext x
  exact sa16y5_Tm_eq hd hs hsd hsd1 ha hε hμ hv i j x

lemma sa16y5_pd_add {f g : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {j : ℕ} (idx : Fin j → Fin d) :
    partialDeriv idx (f + g) = partialDeriv idx f + partialDeriv idx g := by
  funext x
  unfold partialDeriv
  rw [iteratedFDeriv_add_apply (hf.contDiffAt.of_le (by exact_mod_cast le_top))
    (hg.contDiffAt.of_le (by exact_mod_cast le_top))]
  rfl

lemma sa16y5_pd_sub {f g : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {j : ℕ} (idx : Fin j → Fin d) :
    partialDeriv idx (f - g) = partialDeriv idx f - partialDeriv idx g := by
  funext x
  unfold partialDeriv
  rw [iteratedFDeriv_sub_apply (hf.contDiffAt.of_le (by exact_mod_cast le_top))
    (hg.contDiffAt.of_le (by exact_mod_cast le_top))]
  rfl

lemma sa16y5_kernels_int (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hsd1 : (d : ℝ) < s + 1) {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) (i j : Fin d) :
    Integrable (sa16y5_rn d s ε) ∧ Integrable (sa16y5_ddg d a j i) ∧ Integrable (sa16r_dg d a i) ∧
      Integrable (sa16r_dg d a j) ∧ Integrable (sa16y5_V d s ε i) ∧ Integrable (sa16r_g d a) := by
  obtain ⟨Cf, -, hCf⟩ := sa16y5_V_L1 hd hs hsd1 (s := s)
  exact ⟨(sa16y5_rn_L1 hd hs hsd hε).1, (sa16y5_ddg_L1 ha j i).1, sa16r_dg_int ha i, sa16r_dg_int ha j,
    (hCf ε hε i).1, sa16r_g_int ha⟩

lemma sa16y5_T_smooth (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hsd1 : (d : ℝ) < s + 1) {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) (i j : Fin d) {P Q : Euc d → ℝ}
    (hP : IsCcInfty P) (hQ : IsCcInfty Q) : ContDiff ℝ ∞ (sa16y5_T d s a ε i j P Q) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := sa16y5_kernels_int hd hs hsd hsd1 ha hε i j
  have e : sa16y5_T d s a ε i j P Q =
      sa16r_cv (sa16y5_rn d s ε) (sa16r_cv (sa16y5_ddg d a j i) P)
        - sa16r_cv (sa16y5_rn d s ε) (sa16r_cv (sa16r_dg d a i) Q)
        + sa16r_cv (sa16y5_V d s ε i) (sa16r_cv (sa16r_dg d a j) P)
        - sa16r_cv (sa16y5_V d s ε i) (sa16r_cv (sa16r_g d a) Q) := rfl
  rw [e]
  exact (((sa16y5_cv_cv_contDiff h1 h2 hP).sub (sa16y5_cv_cv_contDiff h1 h3 hQ)).add
    (sa16y5_cv_cv_contDiff h5 h4 hP)).sub (sa16y5_cv_cv_contDiff h5 h6 hQ)

lemma sa16y5_T_pd (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hsd1 : (d : ℝ) < s + 1) {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) (i j : Fin d) {P Q : Euc d → ℝ}
    (hP : IsCcInfty P) (hQ : IsCcInfty Q) {l : ℕ} (idx : Fin l → Fin d) :
    partialDeriv idx (sa16y5_T d s a ε i j P Q) =
      sa16y5_T d s a ε i j (partialDeriv idx P) (partialDeriv idx Q) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := sa16y5_kernels_int hd hs hsd hsd1 ha hε i j
  have e : ∀ P Q, sa16y5_T d s a ε i j P Q =
      sa16r_cv (sa16y5_rn d s ε) (sa16r_cv (sa16y5_ddg d a j i) P)
        - sa16r_cv (sa16y5_rn d s ε) (sa16r_cv (sa16r_dg d a i) Q)
        + sa16r_cv (sa16y5_V d s ε i) (sa16r_cv (sa16r_dg d a j) P)
        - sa16r_cv (sa16y5_V d s ε i) (sa16r_cv (sa16r_g d a) Q) := fun P Q => rfl
  rw [e, e]
  set FA : Euc d → ℝ := sa16r_cv (sa16y5_rn d s ε) (sa16r_cv (sa16y5_ddg d a j i) P) with hFA
  set FB : Euc d → ℝ := sa16r_cv (sa16y5_rn d s ε) (sa16r_cv (sa16r_dg d a i) Q) with hFB
  set FC : Euc d → ℝ := sa16r_cv (sa16y5_V d s ε i) (sa16r_cv (sa16r_dg d a j) P) with hFC
  set FD : Euc d → ℝ := sa16r_cv (sa16y5_V d s ε i) (sa16r_cv (sa16r_g d a) Q) with hFD
  have sA : ContDiff ℝ ∞ FA := sa16y5_cv_cv_contDiff h1 h2 hP
  have sB : ContDiff ℝ ∞ FB := sa16y5_cv_cv_contDiff h1 h3 hQ
  have sC : ContDiff ℝ ∞ FC := sa16y5_cv_cv_contDiff h5 h4 hP
  have sD : ContDiff ℝ ∞ FD := sa16y5_cv_cv_contDiff h5 h6 hQ
  have sAB : ContDiff ℝ ∞ (FA - FB) := sA.sub sB
  have sABC : ContDiff ℝ ∞ (FA - FB + FC) := sAB.add sC
  rw [sa16y5_pd_sub sABC sD, sa16y5_pd_add sAB sC, sa16y5_pd_sub sA sB,
    hFA, hFB, hFC, hFD, sa16y5_pd_cv_cv h1 h2 hP idx, sa16y5_pd_cv_cv h1 h3 hQ idx,
    sa16y5_pd_cv_cv h5 h4 hP idx, sa16y5_pd_cv_cv h5 h6 hQ idx]

end Lb5

end HRS.Whole.AppendixA.Phase2SA16R
