import HRS.MS.R26T8AP22d

/-!
# S8.2 local Newton layer, packet T8A.P22 (part e): the cutoff `chi`, its flatness and the scaled cutoff `theta_eps = 1 - chi(w/eps)`
`r26t8a_p22_chi_flat`: `∇chi = 0` and `Δchi = 0` on `{|u| <= 1} ∪ {|u| >= 2}`. `r26t8a_p22_theta_fderiv`, `r26t8a_p22_theta_lap`: first and second
derivatives of the scaled cutoff.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open HRS HRS.Whole HRS.MS.Phase2S82

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_p22_chi_c2 {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) : ContDiff ℝ 2 chi := by
  have h : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) chi := contDiff_infty.1 hchi.1 2
  exact_mod_cast h

theorem r26t8a_p22_chi_flat {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {u : Euc d}
    (hu : ‖u‖ ≤ 1 ∨ 2 ≤ ‖u‖) : fderiv ℝ chi u = 0 ∧ Laplacian.laplacian chi u = 0 := by
  have hc2 := r26t8a_p22_chi_c2 hchi
  set Z : Set (Euc d) := {u | fderiv ℝ chi u = 0 ∧ Laplacian.laplacian chi u = 0} with hZ
  have hcl : IsClosed Z :=
    (isClosed_eq (hc2.continuous_fderiv (by norm_num)) continuous_const).inter
      (isClosed_eq (HRS.Parx.continuous_laplacian hc2) continuous_const)
  have hmem : ∀ v : Euc d, (‖v‖ < 1 ∨ 2 < ‖v‖) → v ∈ Z := by
    intro v hv
    have hev : ∃ c : ℝ, chi =ᶠ[𝓝 v] fun _ => c := by
      rcases hv with h | h
      · refine ⟨1, ?_⟩
        filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds (show ‖v‖ < 1 from h)] with y hy
        exact hchi.2.2.2.1 y (le_of_lt hy)
      · refine ⟨0, ?_⟩
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds (show 2 < ‖v‖ from h)] with y hy
        exact hchi.2.2.2.2 y (le_of_lt hy)
    obtain ⟨c, hc⟩ := hev
    refine ⟨?_, ?_⟩
    · rw [hc.fderiv_eq]; simp
    · rw [(InnerProductSpace.laplacian_congr_nhds hc).eq_of_nhds]; simp
  have : u ∈ Z := by
    rcases hu with h | h
    · -- approach from inside
      refine hcl.mem_of_tendsto (f := fun t : ℝ => (1 - t) • u) (b := 𝓝[>] (0 : ℝ)) ?_ ?_
      · have hc : Continuous (fun t : ℝ => (1 - t) • u) := by fun_prop
        have : Tendsto (fun t : ℝ => (1 - t) • u) (𝓝 0) (𝓝 (((1 : ℝ) - 0) • u)) := hc.tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
        refine hmem _ (Or.inl ?_)
        rw [norm_smul, Real.norm_of_nonneg (by linarith [ht.2])]
        nlinarith [ht.1, ht.2, norm_nonneg u]
    · refine hcl.mem_of_tendsto (f := fun t : ℝ => (1 + t) • u) (b := 𝓝[>] (0 : ℝ)) ?_ ?_
      · have hc : Continuous (fun t : ℝ => (1 + t) • u) := by fun_prop
        have : Tendsto (fun t : ℝ => (1 + t) • u) (𝓝 0) (𝓝 (((1 : ℝ) + 0) • u)) := hc.tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        refine hmem _ (Or.inr ?_)
        rw [norm_smul, Real.norm_of_nonneg (by linarith [(Set.mem_Ioi.1 ht)])]
        nlinarith [(Set.mem_Ioi.1 ht), norm_nonneg u]
  exact this

/-- The scaled cutoff `1 - chi(w/eps)`. -/
def r26t8a_p22_theta (chi : Euc d → ℝ) (ε : ℝ) (w : Euc d) : ℝ := 1 - chi (ε⁻¹ • w)

theorem r26t8a_p22_theta_contDiff {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (ε : ℝ) :
    ContDiff ℝ 2 (r26t8a_p22_theta chi ε) :=
  contDiff_const.sub ((r26t8a_p22_chi_c2 hchi).comp (contDiff_const_smul _))

theorem r26t8a_p22_theta_fderiv {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {ε : ℝ} (hε : 0 < ε) (w : Euc d) :
    ‖fderiv ℝ (r26t8a_p22_theta chi ε) w‖ ≤ ε⁻¹ * ‖fderiv ℝ chi (ε⁻¹ • w)‖ := by
  have hd : DifferentiableAt ℝ chi (ε⁻¹ • w) :=
    ((r26t8a_p22_chi_c2 hchi).differentiable (by norm_num)).differentiableAt
  have hh : HasFDerivAt (fun w : Euc d => ε⁻¹ • w) (ε⁻¹ • ContinuousLinearMap.id ℝ (Euc d)) w :=
    (hasFDerivAt_id w).const_smul ε⁻¹
  have h1 := (hd.hasFDerivAt.comp w hh)
  have h2 := (hasFDerivAt_const (1 : ℝ) w).sub h1
  have h3 : fderiv ℝ (r26t8a_p22_theta chi ε) w =
      -((fderiv ℝ chi (ε⁻¹ • w)).comp (ε⁻¹ • ContinuousLinearMap.id ℝ (Euc d))) := by
    have e : r26t8a_p22_theta chi ε = (fun _ => (1 : ℝ)) - chi ∘ (fun w : Euc d => ε⁻¹ • w) := by
      funext x; simp [r26t8a_p22_theta]
    rw [e]
    simpa using h2.fderiv
  rw [h3, norm_neg]
  calc ‖(fderiv ℝ chi (ε⁻¹ • w)).comp (ε⁻¹ • ContinuousLinearMap.id ℝ (Euc d))‖
      ≤ ‖fderiv ℝ chi (ε⁻¹ • w)‖ * ‖ε⁻¹ • ContinuousLinearMap.id ℝ (Euc d)‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ chi (ε⁻¹ • w)‖ * ε⁻¹ := by
        gcongr
        calc ‖ε⁻¹ • ContinuousLinearMap.id ℝ (Euc d)‖ ≤ ‖ε⁻¹‖ * ‖ContinuousLinearMap.id ℝ (Euc d)‖ :=
              ContinuousLinearMap.opNorm_smul_le _ _
          _ ≤ ε⁻¹ * 1 := by
              rw [Real.norm_of_nonneg (inv_nonneg.2 hε.le)]
              exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le) (inv_nonneg.2 hε.le)
          _ = ε⁻¹ := mul_one _
    _ = _ := mul_comm _ _

theorem r26t8a_p22_theta_lap {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {ε : ℝ} (hε : 0 < ε) (w : Euc d) :
    Laplacian.laplacian (r26t8a_p22_theta chi ε) w = -((ε⁻¹) ^ 2 * Laplacian.laplacian chi (ε⁻¹ • w)) := by
  have hc2 := r26t8a_p22_chi_c2 hchi
  have hcomp : ContDiff ℝ 2 (fun w : Euc d => chi (ε⁻¹ • w)) := hc2.comp (contDiff_const_smul _)
  have h1 : Laplacian.laplacian (r26t8a_p22_theta chi ε) w = -Laplacian.laplacian (fun w : Euc d => chi (ε⁻¹ • w)) w := by
    have e : r26t8a_p22_theta chi ε = (fun _ => (1 : ℝ)) - fun w : Euc d => chi (ε⁻¹ • w) := by
      funext x; simp [r26t8a_p22_theta]
    rw [e]
    simpa using (contDiffAt_const (c := (1 : ℝ))).laplacian_sub hcomp.contDiffAt (x := w)
  rw [h1]
  congr 1
  let L : Euc d →L[ℝ] Euc d := ε⁻¹ • ContinuousLinearMap.id ℝ (Euc d)
  have hL : (fun w : Euc d => chi (ε⁻¹ • w)) = chi ∘ L := by funext x; simp [L]
  rw [hL, InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only
  rw [L.iteratedFDeriv_comp_right hc2 w (by norm_num)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have : (fun j => L (![(stdOrthonormalBasis ℝ (Euc d)) i, (stdOrthonormalBasis ℝ (Euc d)) i] j)) =
      fun j => ε⁻¹ • ![(stdOrthonormalBasis ℝ (Euc d)) i, (stdOrthonormalBasis ℝ (Euc d)) i] j := by
    funext j; simp [L]
  rw [this, ContinuousMultilinearMap.map_smul_univ]
  simp [L]

end HRS.MS.R26T8A
