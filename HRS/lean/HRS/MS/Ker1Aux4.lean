import HRS.MS.Ker1Aux3
import HRS.Kernel.SymbolClass

/-!
# MS-KER1, helper file 4: scaling of iterated derivatives and derivative bounds of the Euclidean kernel
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise ContDiff

namespace HRS.MS.Ker1

open HRS HRS.Whole

variable {d : ℕ}

/-- Scaling of iterated derivatives: `D^n (f(c ·))(x) = c^n D^n f (c x)` (no regularity needed). -/
theorem ker1_iteratedFDeriv_comp_smul {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (f : Euc d → E') {c : ℝ} (hc : c ≠ 0) (n : ℕ) (x : Euc d) :
    iteratedFDeriv ℝ n (fun y => f (c • y)) x = c ^ n • iteratedFDeriv ℝ n f (c • x) := by
  set e : Euc d ≃L[ℝ] Euc d := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc) with he
  have heapp : ∀ y, e y = c • y := fun y => by simp [he]
  have h1 := e.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (x := x) (mem_univ _) n
  rw [preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h1
  have hfe : (f ∘ e) = fun y => f (c • y) := funext fun y => by simp [heapp]
  rw [hfe] at h1
  rw [h1, heapp]
  ext v
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousMultilinearMap.smul_apply]
  have : (fun i => (e : Euc d →L[ℝ] Euc d) (v i)) = fun i => c • v i := by
    funext i; exact heapp (v i)
  rw [this, ContinuousMultilinearMap.map_smul_univ]
  simp

theorem ker1_contDiffAt_log_norm {ξ : Euc d} (hξ : ξ ≠ 0) :
    ContDiffAt ℝ ∞ (fun x : Euc d => -Real.log ‖x‖) ξ :=
  ((contDiffAt_norm ℝ hξ).log (norm_ne_zero_iff.mpr hξ)).neg

/-- homogeneity of the derivatives of order `≥ 1` of `-log ‖x‖` -/
theorem ker1_iteratedFDeriv_log_smul {lam : ℝ} (hlam : 0 < lam) {ξ : Euc d} (hξ : ξ ≠ 0) {m : ℕ}
    (hm : 1 ≤ m) :
    iteratedFDeriv ℝ m (fun x : Euc d => -Real.log ‖x‖) (lam • ξ) =
      (lam ^ m)⁻¹ • iteratedFDeriv ℝ m (fun x : Euc d => -Real.log ‖x‖) ξ := by
  set f : Euc d → ℝ := fun x => -Real.log ‖x‖ with hf
  have h1 := ker1_iteratedFDeriv_comp_smul f hlam.ne' m ξ
  have hev : (fun y : Euc d => f (lam • y)) =ᶠ[𝓝 ξ] fun y => f y + (-Real.log lam) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (show ξ ∈ ({(0 : Euc d)}ᶜ : Set (Euc d)) from hξ)]
      with y hy
    have hy' : y ≠ 0 := hy
    simp only [hf, norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
    rw [Real.log_mul hlam.ne' (norm_ne_zero_iff.mpr hy')]
    ring
  have h2 : iteratedFDeriv ℝ m (fun y : Euc d => f (lam • y)) ξ = iteratedFDeriv ℝ m f ξ := by
    rw [(hev.iteratedFDeriv ℝ m).eq_of_nhds]
    have hcd : ContDiffAt ℝ m f ξ := (ker1_contDiffAt_log_norm hξ).of_le (by exact_mod_cast le_top)
    have := iteratedFDeriv_add_apply (i := m) (f := f) (g := fun _ : Euc d => -Real.log lam)
      hcd contDiffAt_const (x := ξ)
    rw [show (fun y => f y + (-Real.log lam)) = f + fun _ => -Real.log lam from rfl, this,
      iteratedFDeriv_const_of_ne (by omega)]
    simp
  rw [h2] at h1
  have hlm : (0 : ℝ) < lam ^ m := pow_pos hlam m
  rw [h1, smul_smul, inv_mul_cancel₀ hlm.ne', one_smul]


theorem ker1_norm_iteratedFDeriv_log_le {m : ℕ} (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Euc d, ξ ≠ 0 →
      ‖iteratedFDeriv ℝ m (fun x : Euc d => -Real.log ‖x‖) ξ‖ ≤ C * ‖ξ‖ ^ (-(m : ℝ)) := by
  set f : Euc d → ℝ := fun x => -Real.log ‖x‖ with hf
  set s : Set (Euc d) := {(0 : Euc d)}ᶜ with hs
  have hso : IsOpen s := isOpen_compl_singleton
  have hcdo : ContDiffOn ℝ ∞ f s := fun x hx => (ker1_contDiffAt_log_norm hx).contDiffWithinAt
  have hcont : ContinuousOn (iteratedFDeriv ℝ m f) s := by
    have h1 := hcdo.continuousOn_iteratedFDerivWithin (m := m)
      (by exact_mod_cast le_top) hso.uniqueDiffOn
    exact h1.congr (iteratedFDerivWithin_of_isOpen m hso).symm
  have hsph : Metric.sphere (0 : Euc d) 1 ⊆ s := fun x hx => by
    simp only [hs, Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl; simp at hx
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Euc d) 1).exists_bound_of_continuousOn (hcont.mono hsph)
  refine ⟨max C 0, le_max_right _ _, fun ξ hξ => ?_⟩
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  set u : Euc d := ‖ξ‖⁻¹ • ξ with hu
  have hu1 : u ∈ Metric.sphere (0 : Euc d) 1 := by
    simp [hu, norm_smul, hn.ne']
  have hu0 : u ≠ 0 := by
    intro h; rw [h] at hu1; simp at hu1
  have hξu : ξ = ‖ξ‖ • u := by
    simp [hu, smul_smul, hn.ne']
  have := ker1_iteratedFDeriv_log_smul hn hu0 hm
  rw [← hξu] at this
  rw [this, norm_smul, norm_inv, norm_pow, Real.norm_eq_abs, abs_of_pos hn, Real.rpow_neg hn.le,
    Real.rpow_natCast, mul_comm]
  have h2 := hC u hu1
  calc ‖iteratedFDeriv ℝ m f u‖ * (‖ξ‖ ^ m)⁻¹ ≤ max C 0 * (‖ξ‖ ^ m)⁻¹ :=
        mul_le_mul_of_nonneg_right (h2.trans (le_max_left _ _)) (by positivity)
    _ = _ := by ring

/-- bound on the derivatives of the Euclidean kernel `rieszKernel d s` away from `0` -/
theorem ker1_E_bound {s : ℝ} (hs0 : 0 ≤ s) (n : ℕ) (hn : 0 < (n : ℝ) + s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Euc d, ξ ≠ 0 →
      ‖iteratedFDeriv ℝ n (rieszKernel d s) ξ‖ ≤ C * ‖ξ‖ ^ (-s - n) := by
  by_cases hs : s = 0
  · subst hs
    have hn1 : 1 ≤ n := by
      by_contra h
      have : n = 0 := by omega
      subst this; simp at hn
    obtain ⟨C, hC0, hC⟩ := ker1_norm_iteratedFDeriv_log_le (d := d) hn1
    refine ⟨C, hC0, fun ξ hξ => ?_⟩
    have : rieszKernel d 0 = fun x : Euc d => -Real.log ‖x‖ := by
      funext x; simp [rieszKernel]
    rw [this]
    simpa using hC ξ hξ
  · obtain ⟨C, hC0, hC⟩ := norm_iteratedFDeriv_rpow_norm_le (V := Euc d) (-s) n
    refine ⟨C, hC0, fun ξ hξ => ?_⟩
    have : rieszKernel d s = fun x : Euc d => ‖x‖ ^ (-s) := by
      funext x; simp [rieszKernel, hs]
    rw [this]
    exact hC ξ hξ

end HRS.MS.Ker1
