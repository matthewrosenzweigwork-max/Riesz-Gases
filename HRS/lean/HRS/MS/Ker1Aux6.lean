import HRS.MS.Ker1Aux5

/-!
# MS-KER1, helper file 6: the explicit kernel `γ_L` off the lattice, and its pointwise bounds
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise ContDiff

namespace HRS.MS.Ker1

open HRS HRS.Whole HRS.Whole.AppendixALemmas

variable {d : ℕ}

theorem ker1_offLattice_iff {L : ℝ} (hL : 0 < L) (x : Euc d) :
    (∀ z : Fin d → ℤ, x ≠ L • latticePt z) ↔ Torus.mk (L⁻¹ • x) ≠ 0 := by
  constructor
  · intro h h0
    obtain ⟨n, hn⟩ := ker1_mk_eq_zero h0
    apply h n
    have : x = L • (L⁻¹ • x) := (smul_inv_smul₀ hL.ne' x).symm
    rw [this, hn]; rfl
  · intro h z hz
    apply h
    have : L⁻¹ • x = Lattice.toEuc z := by
      rw [hz, inv_smul_smul₀ hL.ne']; rfl
    rw [this]; exact ker1_mk_toEuc z

theorem ker1_isOpen_offLattice {L : ℝ} (hL : 0 < L) :
    IsOpen {x : Euc d | ∀ z : Fin d → ℤ, x ≠ L • latticePt z} := by
  have : {x : Euc d | ∀ z : Fin d → ℤ, x ≠ L • latticePt z} =
      (fun x : Euc d => L⁻¹ • x) ⁻¹' {y : Euc d | Torus.mk y ≠ 0} := by
    ext x; exact ker1_offLattice_iff hL x
  rw [this]
  exact HRS.KernelGrad.isOpen_mk_ne_zero.preimage (continuous_const_smul _)

theorem ker1_offLattice_of_half {L : ℝ} (hL : 0 < L) {x : Euc d} (hx0 : x ≠ 0) (hx : ‖x‖ ≤ L / 2) :
    ∀ z : Fin d → ℤ, x ≠ L • latticePt z := by
  rw [ker1_offLattice_iff hL]
  apply ker1_mk_ne_zero_of_norm (smul_ne_zero (inv_ne_zero hL.ne') hx0)
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hL, inv_mul_le_iff₀ hL]
  linarith

theorem ker1_eventually_eq_gam (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {L : ℝ} (hL : 0 < L)
    {γ : Euc d → ℝ} (hγ : IsPeriodicRieszKernel d s L γ) {x : Euc d}
    (hx : ∀ z : Fin d → ℤ, x ≠ L • latticePt z) : γ =ᶠ[𝓝 x] ker1_gam d s L :=
  Filter.eventuallyEq_of_mem ((ker1_isOpen_offLattice hL).mem_nhds hx)
    (fun y hy => ker1_eq_gam hd hs0 hsd hL hγ y hy)

theorem ker1_gam_bound_a (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (n : ℕ)
    (hn : 0 < (n : ℝ) + s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 < L → ∀ x : Euc d, x ≠ 0 → ‖x‖ ≤ L / 2 →
      ‖iteratedFDeriv ℝ n (ker1_gam d s L) x‖ ≤ C * ‖x‖ ^ (-s - n) := by
  obtain ⟨C, hC0, hC⟩ := ker1_g1_bound hd hs0 hsd n hn
  refine ⟨C, hC0, fun L hL x hx0 hx => ?_⟩
  have hoff := ker1_offLattice_of_half hL hx0 hx
  have hmk := (ker1_offLattice_iff hL x).1 hoff
  rw [ker1_gam_iter hd hs0 hsd hL hmk, norm_smul, ker1_gam_scale_pow hL, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hL.le _)]
  have hxp : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hy0 : L⁻¹ • x ≠ 0 := smul_ne_zero (inv_ne_zero hL.ne') hx0
  have hnorm : ‖L⁻¹ • x‖ = ‖x‖ / L := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hL, inv_mul_eq_div]
  have hyle : ‖L⁻¹ • x‖ ≤ 1 / 2 := by
    rw [hnorm, div_le_iff₀ hL]; linarith
  have h1 := hC _ hy0 hyle
  rw [hnorm, Real.div_rpow hxp.le hL.le] at h1
  have hLe : 0 < L ^ (-s - (n : ℝ)) := Real.rpow_pos_of_pos hL _
  have e : -(s + (n : ℝ)) = -s - n := by ring
  calc L ^ (-(s + (n : ℝ))) * ‖iteratedFDeriv ℝ n (ker1_g1 d s) (L⁻¹ • x)‖
      ≤ L ^ (-(s + (n : ℝ))) * (C * (‖x‖ ^ (-s - (n : ℝ)) / L ^ (-s - (n : ℝ)))) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hL.le _)
    _ = C * ‖x‖ ^ (-s - (n : ℝ)) := by
        rw [e]; field_simp

theorem ker1_gam_bound_b (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 < L → ∀ x : Euc d, x ≠ 0 → ‖x‖ ≤ L / 2 →
      |ker1_gam d 0 L x - Real.log L| ≤ C + |Real.log ‖x‖| := by
  obtain ⟨C, hC0, hC⟩ := ker1_g1_log_bound hd
  refine ⟨C, hC0, fun L hL x hx0 hx => ?_⟩
  have hxp : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hy0 : L⁻¹ • x ≠ 0 := smul_ne_zero (inv_ne_zero hL.ne') hx0
  have hnorm : ‖L⁻¹ • x‖ = ‖x‖ / L := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hL, inv_mul_eq_div]
  have hyle : ‖L⁻¹ • x‖ ≤ 1 / 2 := by
    rw [hnorm, div_le_iff₀ hL]; linarith
  have h1 := hC _ hy0 hyle
  rw [hnorm, Real.log_div hxp.ne' hL.ne'] at h1
  have e : ker1_gam d 0 L x - Real.log L =
      (ker1_g1 d 0 (L⁻¹ • x) + (Real.log ‖x‖ - Real.log L)) - Real.log ‖x‖ := by
    simp only [ker1_gam, neg_zero, Real.rpow_zero, one_mul]; ring
  rw [e]
  calc |(ker1_g1 d 0 (L⁻¹ • x) + (Real.log ‖x‖ - Real.log L)) - Real.log ‖x‖|
      ≤ |ker1_g1 d 0 (L⁻¹ • x) + (Real.log ‖x‖ - Real.log L)| + |Real.log ‖x‖| := abs_sub _ _
    _ ≤ C + |Real.log ‖x‖| := by linarith

end HRS.MS.Ker1
