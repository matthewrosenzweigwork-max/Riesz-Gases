import HRS.MC.CepK1
import HRS.MC.CepE1Aux1

/-!
# Packet CEPE1, auxiliary 2: the primitive `r` of the smooth remainder `ρ` and the one-dimensional potential
-/

open Set Real
open scoped NNReal

noncomputable section

namespace HRS.MC.CepE1

open HRS HRS.MC.CepK1

theorem cepe1_ρ_lip : ∃ C : ℝ≥0, LipschitzWith C cepk1_ρ := by
  have hd : Differentiable ℝ cepk1_ρ := cepk1_ρ_contDiff.differentiable (by simp)
  have hc : Continuous (deriv cepk1_ρ) := cepk1_ρ_contDiff.continuous_deriv (by exact_mod_cast le_top)
  have hper : Function.Periodic (deriv cepk1_ρ) 1 := by
    intro x
    have := deriv_comp_add_const (f := cepk1_ρ) (a := (1 : ℝ)) (x := x)
    have e : (fun u => cepk1_ρ (u + 1)) = cepk1_ρ := funext cepk1_ρ_add_one
    rw [e] at this
    exact this.symm
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := deriv cepk1_ρ) (s := Icc (0 : ℝ) 1)
    hc.continuousOn
  refine ⟨Real.toNNReal C, lipschitzWith_of_nnnorm_deriv_le hd fun x => ?_⟩
  have hx : deriv cepk1_ρ x = deriv cepk1_ρ (Int.fract x) := by
    have := hper.sub_int_mul_eq (⌊x⌋) (x := x)
    rw [Int.fract]
    simpa using this.symm
  rw [hx]
  have h1 := hC (Int.fract x) ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  rw [← NNReal.coe_le_coe, coe_nnnorm]
  exact h1.trans (Real.le_coe_toNNReal C)

theorem cepe1_kernel : ∃ r : ℝ → ℝ, ContDiff ℝ 1 r ∧ (∀ u, HasDerivAt r (cepk1_ρ u) u) ∧
    ∀ u ∈ Ioo (0 : ℝ) 1,
      periodicRiesz 1 0 (Torus.mk (cepk1_ι u)) = -Real.log (2 * Real.sin (π * u)) + r u := by
  have hρc : Continuous cepk1_ρ := cepk1_ρ_contDiff.continuous
  set c : ℝ → ℝ := fun u => ∫ x in (0 : ℝ)..u, cepk1_ρ x with hc
  have hcd : ∀ u, HasDerivAt c (cepk1_ρ u) u := fun u =>
    (hρc.integral_hasStrictDerivAt 0 u).hasDerivAt
  set G : ℝ → ℝ := fun u => periodicRiesz 1 0 (Torus.mk (cepk1_ι u)) with hG
  have hnint : ∀ u ∈ Ioo (0 : ℝ) 1, ∀ n : ℤ, u ≠ n := by
    intro u hu n hn
    rcases le_or_gt n 0 with h | h
    · have : (n : ℝ) ≤ 0 := by exact_mod_cast h
      linarith [hu.1]
    · have : (1 : ℝ) ≤ n := by exact_mod_cast h
      linarith [hu.2]
  have hGd : ∀ u ∈ Ioo (0 : ℝ) 1, HasDerivAt G
      (-(π * (Real.cos (π * u) / Real.sin (π * u))) + cepk1_ρ u) u := by
    intro u hu
    have h := KernelD1Aux.hasDerivAt_g_ev (s := 0) le_rfl (by norm_num) (hnint u hu)
    have e : (periodicRieszGrad 1 0 (Torus.mk (KernelD1Aux.ev u))) 0 =
        -(π * (Real.cos (π * u) / Real.sin (π * u))) + cepk1_ρ u := by
      have := cepk1_ρ_eq_off (y := cepk1_ι u) (fun n => hnint u hu n)
      simpa [cepk1_ι, KernelD1Aux.ev] using this
    rw [e] at h
    exact h
  have hLd : ∀ u ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun u => Real.log (2 * Real.sin (π * u)))
      (π * (Real.cos (π * u) / Real.sin (π * u))) u := by
    intro u hu
    have hs : Real.sin (π * u) ≠ 0 := cepk1_sin_ne_zero (hnint u hu)
    have h1 : HasDerivAt (fun u : ℝ => 2 * Real.sin (π * u)) (2 * (Real.cos (π * u) * π)) u := by
      have := ((Real.hasDerivAt_sin (π * u)).comp u ((hasDerivAt_id u).const_mul π))
      simpa using this.const_mul 2
    have := h1.log (by simpa using hs)
    convert this using 1
    field_simp
  set D : ℝ → ℝ := fun u => G u + Real.log (2 * Real.sin (π * u)) - c u with hD
  have hDd : ∀ u ∈ Ioo (0 : ℝ) 1, HasDerivAt D 0 u := by
    intro u hu
    have := ((hGd u hu).add (hLd u hu)).sub (hcd u)
    convert this using 1
    ring
  have hconst : ∀ u ∈ Ioo (0 : ℝ) 1, D u = D (1 / 2) := by
    intro u hu
    exact isOpen_Ioo.is_const_of_deriv_eq_zero (isPreconnected_Ioo)
      (fun x hx => (hDd x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hDd x hx).deriv) hu ⟨by norm_num, by norm_num⟩
  refine ⟨fun u => D (1 / 2) + c u, ?_, fun u => ?_, fun u hu => ?_⟩
  · rw [contDiff_one_iff_deriv]
    refine ⟨fun u => ((hcd u).const_add _).differentiableAt, ?_⟩
    have : deriv (fun u => D (1 / 2) + c u) = cepk1_ρ := funext fun u => ((hcd u).const_add _).deriv
    rw [this]; exact hρc
  · exact (hcd u).const_add _
  · have := hconst u hu
    simp only [hD] at this
    linarith

end HRS.MC.CepE1
