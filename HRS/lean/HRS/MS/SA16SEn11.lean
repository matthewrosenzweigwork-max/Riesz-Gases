import HRS.MS.SA16SEn10

/-!
# S.A.16 (SA16S) En11: the energy inequality of the generator (packet P7, step 12)

`sa16sz_gen_energy`: see `SA16SEn10`.  Proof: the three terms are estimated on jets of `C_c^∞` functions
(`sa16sz_diffusion`, `sa16sz_transport`, `sa16sz_fderiv_le`) and extended to `W^{m+2,p}` by density.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16V2

section En11
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- the double truncation `W^{m+2,p} → W^{m,p}` -/
def sa16sz_iota2 (d m : ℕ) (p : ℝ) [Fact (2 ≤ p)] : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p :=
  (sa16r_iota d m p).comp (sa16r_iota d (m + 1) p)

lemma sa16sz_iota2_Jcc (m : ℕ) (φ : ccSub d) :
    sa16sz_iota2 d m p (sa16r_Jcc d (m + 1 + 1) p φ) = sa16r_Jcc d m p φ := by
  unfold sa16sz_iota2
  rw [ContinuousLinearMap.comp_apply, sa16r_iota_Jcc, sa16r_iota_Jcc]

lemma sa16sz_cc_transport {k : ℕ} {B : ℝ} {bc : Fin d → Euc d → ℝ} (hb : SA16BddCoef k B bc) {φ : Euc d → ℝ}
    (hφ : IsCcInfty φ) : IsCcInfty (sa16so_transportFun bc φ) := by
  have h : sa16so_transportFun bc φ = ∑ l : Fin d, fun x => bc l x * fderiv ℝ φ x (EuclideanSpace.single l 1) := by
    funext x; simp [sa16so_transportFun, Finset.sum_apply]
  rw [h]
  exact (ccSub d).sum_mem (fun l _ => (⟨(hb.smooth l).mul (sa16s_cc_fderiv hφ _).1,
    (sa16s_cc_fderiv hφ _).2.mul_left⟩ : IsCcInfty (fun x => bc l x * fderiv ℝ φ x (EuclideanSpace.single l 1))))

lemma sa16sz_Lap_Jcc (m : ℕ) (φ : ccSub d) :
    sa16so_Lap d m p (sa16r_Jcc d (m + 1 + 1) p φ) = sa16r_Jcc d m p ⟨sa16r_lap φ.1, sa16sw_cc_lap φ.2⟩ := by
  refine sa16r_wrep_inj d m p _ _ ?_
  rw [sa16r_Jcc_eq (d := d) m p ⟨sa16r_lap φ.1, sa16sw_cc_lap φ.2⟩]
  filter_upwards [sa16so_Lap_Jcc (p := p) m φ, sa16r_cc_elt_wrep (p := p) (sa16sw_cc_lap φ.2) m] with x h1 h2
  rw [h1, h2]

lemma sa16sz_B_Jcc (m : ℕ) {B : ℝ} {bc : Fin d → Euc d → ℝ} (hb : SA16BddCoef (m + 1) B bc) (φ : ccSub d) :
    sa16r_iota d m p (sa16so_B d (m + 1) p bc (sa16r_Jcc d (m + 1 + 1) p φ)) =
      sa16r_Jcc d m p ⟨sa16so_transportFun bc φ.1, sa16sz_cc_transport hb φ.2⟩ := by
  refine sa16r_wrep_inj d m p _ _ ?_
  rw [sa16r_Jcc_eq (d := d) m p ⟨sa16so_transportFun bc φ.1, sa16sz_cc_transport hb φ.2⟩]
  filter_upwards [sa16r_iota_wrep (p := p) m (sa16so_B d (m + 1) p bc (sa16r_Jcc d (m + 1 + 1) p φ)),
    sa16so_B_Jcc (p := p) hb φ, sa16r_cc_elt_wrep (p := p) (sa16sz_cc_transport hb φ.2) m] with x h1 h2 h3
  rw [h1, h2, h3]

/-- compatibility of the nonlocal operators at consecutive levels -/
lemma sa16sz_nl_compat (m : ℕ) {s : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {μ : Euc d → ℝ}
    {T1 : WmpSpace d (m + 1) p →L[ℝ] WmpSpace d (m + 1) p} {T0 : WmpSpace d m p →L[ℝ] WmpSpace d m p}
    (h1 : SA16SubOp d (m + 1) p s M μ T1) (h0 : SA16SubOp d m p s M μ T0) :
    (sa16r_iota d m p).comp T1 = T0.comp (sa16r_iota d m p) := by
  refine sa16so_clm_ext fun φ => sa16r_wrep_inj d m p _ _ ?_
  simp only [ContinuousLinearMap.comp_apply]
  rw [sa16r_iota_Jcc]
  filter_upwards [sa16r_iota_wrep (p := p) m (T1 (sa16r_Jcc d (m + 1) p φ)), h1 φ, h0 φ] with x e1 e2 e3
  rw [e1, e2, e3]

end En11

end HRS.Whole.AppendixA.Phase2SA16R
