import HRS.MS.Ker1Aux1
import HRS.Whole.AppendixALemmas

/-!
# MS-KER1, helper file 2: existence of the periodic Riesz kernel on `ℝ^d / Lℤ^d`

`ker1_gam d s L x = L^{-s} g₁(x/L)` with `g₁ = periodicRiesz d s ∘ mk` satisfies
`IsPeriodicRieszKernel d s L`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise ContDiff

namespace HRS.MS.Ker1

open HRS HRS.Whole HRS.Whole.AppendixALemmas

variable {d : ℕ}

/-- the unit-period kernel lifted to `ℝ^d` -/
def ker1_g1 (d : ℕ) (s : ℝ) (y : Euc d) : ℝ := periodicRiesz d s (Torus.mk y)

/-- the kernel `γ_L(x) = L^{-s} g₁(x/L)` -/
def ker1_gam (d : ℕ) (s L : ℝ) (x : Euc d) : ℝ := L ^ (-s) * ker1_g1 d s (L⁻¹ • x)

theorem ker1_mk_zero : Torus.mk (0 : Euc d) = 0 := by
  funext i; simp [Torus.mk]

theorem ker1_mk_eq_zero {y : Euc d} (h : Torus.mk y = 0) : ∃ n : Lattice d, y = Lattice.toEuc n := by
  obtain ⟨m, hm⟩ := HRS.KernelGrad.exists_lattice_of_mk_eq (x := y) (y := 0) (by rw [h, ker1_mk_zero])
  exact ⟨m, by simpa using hm⟩

theorem ker1_mk_toEuc (n : Lattice d) : Torus.mk (Lattice.toEuc n) = 0 := HRS.KernelGrad.mk_toEuc n

theorem ker1_g1_periodic (s : ℝ) (y : Euc d) (n : Lattice d) :
    ker1_g1 d s (y + Lattice.toEuc n) = ker1_g1 d s y := by
  simp [ker1_g1, ker1_mk_add, ker1_mk_toEuc]

theorem ker1_gam_periodic (s : ℝ) {L : ℝ} (hL : 0 < L) (x : Euc d) (z : Fin d → ℤ) :
    ker1_gam d s L (x + L • latticePt z) = ker1_gam d s L x := by
  unfold ker1_gam
  have : L⁻¹ • (x + L • latticePt z) = L⁻¹ • x + Lattice.toEuc z := by
    rw [smul_add, inv_smul_smul₀ hL.ne']; rfl
  rw [this, ker1_g1_periodic]

theorem ker1_gam_smooth (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {L : ℝ} (hL : 0 < L) :
    ContDiffOn ℝ ∞ (ker1_gam d s L) {x : Euc d | ∀ z : Fin d → ℤ, x ≠ L • latticePt z} := by
  intro x₀ hx₀
  have hne : Torus.mk (L⁻¹ • x₀) ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := ker1_mk_eq_zero h
    apply hx₀ n
    have : x₀ = L • (L⁻¹ • x₀) := (smul_inv_smul₀ hL.ne' x₀).symm
    rw [this, hn]; rfl
  have h1 := KernelD1Aux.contDiffAt_lift_g hd hs0 hsd (L⁻¹ • x₀)
    (HRS.KernelGrad.wsq_pos_of_mk_ne_zero hne)
  have h2 : ContDiffAt ℝ ∞ (fun x : Euc d => L ^ (-s) * ker1_g1 d s (L⁻¹ • x)) x₀ :=
    contDiffAt_const.mul (h1.comp x₀ ((contDiff_const_smul L⁻¹).contDiffAt))
  exact h2.contDiffWithinAt

theorem ker1_g1_integrable (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    Integrable (periodicRiesz d s : Torus d → ℝ) := KernelD1Aux.integrable_d1 hd hs0 hsd

theorem ker1_gam_locInt (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {L : ℝ} (hL : 0 < L) :
    LocallyIntegrable (ker1_gam d s L) volume := by
  have h1 := ker1_locInt_comp_mk (ker1_g1_integrable hd hs0 hsd)
  have h2 := ker1_locInt_smul h1 (inv_ne_zero hL.ne')
  exact h2.smul (L ^ (-s))


theorem ker1_gam_coeff_aux (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {L : ℝ} (hL : 0 < L)
    (k : Lattice d) :
    ∫ x in ker1_box d L, (ker1_gam d s L x : ℂ) *
        Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, ((k i : ℝ) / L) * x i : ℝ) : ℂ))) =
      (L : ℂ) ^ d * ((L ^ (-s) * rieszCoeff d s k : ℝ) : ℂ) := by
  have hG : Integrable (fun z : Torus d => L ^ (-s) * periodicRiesz d s z) :=
    (ker1_g1_integrable hd hs0 hsd).const_mul _
  have h := ker1_box_coeff hL (fun z : Torus d => L ^ (-s) * periodicRiesz d s z) hG k
  have e1 : ∀ x : Euc d, ker1_gam d s L x = L ^ (-s) * periodicRiesz d s (Torus.mk (L⁻¹ • x)) :=
    fun x => rfl
  simp_rw [e1]
  rw [h]
  congr 1
  have h2 := KernelD1Aux.integral_mode_d1 hd hs0 hsd k
  have : ∀ z : Torus d, Torus.mode (-k) z * ((L ^ (-s) * periodicRiesz d s z : ℝ) : ℂ) =
      ((L ^ (-s) : ℝ) : ℂ) * (Torus.mode (-k) z * ((periodicRiesz d s z : ℝ) : ℂ)) := by
    intro z; push_cast; ring
  simp_rw [this]
  rw [integral_const_mul, h2]
  push_cast; ring

theorem ker1_gam_isKernel (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {L : ℝ} (hL : 0 < L) :
    IsPeriodicRieszKernel d s L (ker1_gam d s L) where
  periodic := ker1_gam_periodic s hL
  smooth := ker1_gam_smooth hd hs0 hsd hL
  locInt := ker1_gam_locInt hd hs0 hsd hL
  meanZero := by
    have h := ker1_gam_coeff_aux hd hs0 hsd hL (0 : Lattice d)
    have h0 : rieszCoeff d s 0 = 0 := by simp [rieszCoeff]
    rw [h0] at h
    simp only [Pi.zero_apply, Int.cast_zero, zero_div, zero_mul, Finset.sum_const_zero,
      Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one, mul_zero] at h
    have h' : ∫ x in ker1_box d L, ker1_gam d s L x = 0 := by
      have h3 := integral_complex_ofReal (μ := volume.restrict (ker1_box d L))
        (f := ker1_gam d s L)
      rw [h] at h3
      exact_mod_cast h3.symm
    exact h'
  coeff := by
    intro k hk
    have h := ker1_gam_coeff_aux hd hs0 hsd hL k
    show ∫ x in ker1_box d L, (ker1_gam d s L x : ℂ) *
        Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, ((k i : ℝ) / L) * x i : ℝ) : ℂ))) = _
    rw [h]
    have hk1 : 1 ≤ Lattice.enorm k := one_le_enorm k hk
    have hv : ‖(WithLp.toLp 2 fun i => (k i : ℝ) : Euc d)‖ = Lattice.enorm k := rfl
    rw [hv]
    have hrc : rieszCoeff d s k = rieszConst d s * (2 * Real.pi * Lattice.enorm k) ^ (s - (d : ℝ)) := by
      simp [rieszCoeff, hk]
    rw [hrc]
    have hpos : 0 < 2 * Real.pi * Lattice.enorm k := by positivity
    have hreal : (L : ℝ) ^ d * (L ^ (-s) * (rieszConst d s * (2 * Real.pi * Lattice.enorm k) ^ (s - (d : ℝ)))) =
        rieszConst d s * (2 * Real.pi * (Lattice.enorm k / L)) ^ (s - (d : ℝ)) := by
      have e1 : 2 * Real.pi * (Lattice.enorm k / L) = (2 * Real.pi * Lattice.enorm k) * L⁻¹ := by
        field_simp
      rw [e1, Real.mul_rpow hpos.le (inv_nonneg.2 hL.le), Real.inv_rpow hL.le, ← Real.rpow_neg hL.le,
        neg_sub, ← Real.rpow_natCast]
      have hLL : L ^ (d : ℝ) * L ^ (-s) = L ^ ((d : ℝ) - s) := by
        rw [← Real.rpow_add hL]; ring_nf
      have key : ∀ a c : ℝ, L ^ (d : ℝ) * (L ^ (-s) * (c * a)) = c * (a * L ^ ((d : ℝ) - s)) :=
        fun a c => by linear_combination (c * a) * hLL
      exact key _ _
    have := congrArg (fun r : ℝ => (r : ℂ)) hreal
    simp only [Complex.ofReal_mul, Complex.ofReal_pow] at this
    push_cast at this ⊢
    linear_combination this

end HRS.MS.Ker1
