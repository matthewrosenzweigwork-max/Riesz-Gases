import HRS.MC.QRPHdAux2
import HRS.Kernel.GradConv
import HRS.Kernel.GradFourier

/-!
# Packet HD, part 3: Fourier analysis of the commutator kernel

* `hdF_coeff`: the Fourier coefficient of the `i`-th component of `∇g` is `2πi c_i ĝ(c)`
  (dominated convergence from the heat regularisations).
* `hdJ`: `∫_y H_λ(x,y) e_β(y) dy = K(λ,β) e_{λ+β}(x)`, `H_λ(x,y) = ∑_i 2πiλ_i (e_λ(x) - e_λ(y)) ∂_ig(x-y)`.
* `hdI`: `∫_x e_α(x) ∫_y H_λ(x,y) e_β(y) dy dx = 1_{α+λ+β=0} K(λ,β)`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped BigOperators ComplexConjugate

namespace HRS.MC.QRSpec.Hd

open HRS HRS.KernelGrad

variable {d : ℕ} {s : ℝ}

/-- The `i`-th component of `∇g`, as a complex number. -/
def hdGc (d : ℕ) (s : ℝ) (i : Fin d) (z : Torus d) : ℂ := (((periodicRieszGrad d s z) i : ℝ) : ℂ)

theorem hd_mode_neg_arg (l : Lattice d) (y : Torus d) :
    Torus.mode l (-y) = starRingEnd ℂ (Torus.mode l y) := by
  simp only [Torus.mode, UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [fourier_apply, fourier_apply, smul_neg, fourier_neg']
  rfl

theorem hd_mode_sub (l : Lattice d) (x y : Torus d) :
    Torus.mode l (x - y) = Torus.mode l x * Torus.mode (-l) y := by
  rw [sub_eq_add_neg, mode_add_arg, hd_mode_neg_arg, ← Torus.mode_neg]

theorem hd_measurable_mode (l : Lattice d) : Measurable (Torus.mode l) :=
  (Torus.continuous_mode l).measurable

theorem hdGc_integrable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs1 : s + 1 < d) (i : Fin d) :
    Integrable (hdGc d s i) := by
  obtain ⟨C, hG⟩ := goodKernel_periodicRieszGrad hd hs0 (by linarith)
  have hGi := hG.integrable_G hs1
  have h1 : Integrable (fun z : Torus d => (periodicRieszGrad d s z) i) :=
    ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).integrable_comp hGi)
  exact h1.ofReal

theorem hdGc_measurable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs1 : s + 1 < d) (i : Fin d) :
    Measurable (hdGc d s i) := by
  obtain ⟨C, hG⟩ := goodKernel_periodicRieszGrad hd hs0 (by linarith)
  have := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.measurable.comp hG.meas
  exact Complex.measurable_ofReal.comp this

/-- Fourier coefficients of the components of `∇g`. -/
theorem hdF_coeff (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs1 : s + 1 < d) (c : Lattice d) (i : Fin d) :
    ∫ z, Torus.mode (-c) z * hdGc d s i z =
      (2 * Real.pi * Complex.I * ((c i : ℤ) : ℂ)) * ((rieszCoeff d s c : ℝ) : ℂ) := by
  have hsd : s < d := by linarith
  obtain ⟨C, hC0, hGε⟩ := goodKernel_heat hd hs0 hsd
  obtain ⟨C', hG⟩ := goodKernel_periodicRieszGrad hd hs0 hsd
  set l : Filter ℝ := 𝓝[>] (0 : ℝ) with hl
  set bd : Torus d → ℝ := fun z => C * (‖z‖ ^ (-(s + 1)) + 1) with hbd
  have hbdi : Integrable bd :=
    ((integrable_norm_rpow_neg (by omega) hs1).add (integrable_const (1 : ℝ))).const_mul C
  have hLHS : Tendsto (fun ε : ℝ => ∫ z, Torus.mode (-c) z * ((heatRieszGrad d s ε z i : ℝ) : ℂ)) l
      (𝓝 (∫ z, Torus.mode (-c) z * hdGc d s i z)) := by
    refine tendsto_integral_filter_of_dominated_convergence bd ?_ ?_ hbdi ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have : Continuous fun z : Torus d => Torus.mode (-c) z * ((heatRieszGrad d s ε z i : ℝ) : ℂ) :=
        (Torus.continuous_mode _).mul (Complex.continuous_ofReal.comp
          (continuous_heatRieszGrad_apply hsd hε i))
      exact this.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards [torus_ae_ne' (by omega : 0 < d)] with z hz
      rw [norm_mul, Torus.norm_mode, one_mul, Complex.norm_real, Real.norm_eq_abs]
      refine le_trans ?_ ((hGε ε hε).bound_norm z hz |>.trans ?_)
      · have := PiLp.norm_apply_le (heatRieszGrad d s ε z) i
        simpa using this
      · rw [show -s - 1 = -(s + 1) by ring]
    · refine Eventually.of_forall fun z => ?_
      have h2 := ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.tendsto _).comp (heat_tendsto hsd z)
      exact tendsto_const_nhds.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp h2)
  set R : ℝ → ℂ := fun ε => (2 * Real.pi * Complex.I * ((c i : ℤ) : ℂ)) *
      ((rieszCoeff d s c * Real.exp (-ε * Lattice.enorm c ^ 2) : ℝ) : ℂ) with hR
  have hRc : Continuous R := by
    simp only [hR]
    fun_prop
  have hRHS : Tendsto R l (𝓝 ((2 * Real.pi * Complex.I * ((c i : ℤ) : ℂ)) *
      ((rieszCoeff d s c : ℝ) : ℂ))) := by
    have := (hRc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa [hR] using this
  have hEq : (fun ε : ℝ => ∫ z, Torus.mode (-c) z * ((heatRieszGrad d s ε z i : ℝ) : ℂ)) =ᶠ[l] R := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact integral_mode_heat_component hsd hε c i
  exact tendsto_nhds_unique (hLHS.congr' hEq) hRHS

/-- Convolution of a mode with a component of `∇g`. -/
theorem hdConv (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs1 : s + 1 < d) (i : Fin d) (β : Lattice d) (x : Torus d) :
    ∫ y, hdGc d s i (x - y) * Torus.mode β y =
      ((2 * Real.pi * Complex.I * ((β i : ℤ) : ℂ)) * ((rieszCoeff d s β : ℝ) : ℂ)) * Torus.mode β x := by
  have e1 : ∫ y, hdGc d s i (x - y) * Torus.mode β y = ∫ y, hdGc d s i y * Torus.mode β (x - y) := by
    rw [← integral_sub_left_eq_self (fun y => hdGc d s i y * Torus.mode β (x - y)) volume x]
    simp only [sub_sub_cancel]
  rw [e1]
  have e2 : ∀ y, hdGc d s i y * Torus.mode β (x - y) =
      Torus.mode β x * (Torus.mode (-β) y * hdGc d s i y) := by
    intro y; rw [hd_mode_sub]; ring
  simp_rw [e2]
  rw [integral_const_mul, hdF_coeff hd hs0 hs1]
  ring

/-- The pair kernel of the complex mode `e_λ`. -/
def hdH (d : ℕ) (s : ℝ) (lam : Lattice d) (x y : Torus d) : ℂ :=
  ∑ i, (2 * Real.pi * Complex.I * ((lam i : ℤ) : ℂ)) * (Torus.mode lam x - Torus.mode lam y) *
    hdGc d s i (x - y)

/-- The multiplier `K(λ,β)`. -/
def hdK (d : ℕ) (s : ℝ) (lam β : Lattice d) : ℂ :=
  ∑ i, (2 * Real.pi * Complex.I * ((lam i : ℤ) : ℂ)) *
    ((2 * Real.pi * Complex.I * ((β i : ℤ) : ℂ)) * ((rieszCoeff d s β : ℝ) : ℂ) -
      (2 * Real.pi * Complex.I * (((lam + β) i : ℤ) : ℂ)) * ((rieszCoeff d s (lam + β) : ℝ) : ℂ))

theorem hd_integrable_Gmode (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs1 : s + 1 < d) (i : Fin d) (γ : Lattice d)
    (x : Torus d) : Integrable (fun y => hdGc d s i (x - y) * Torus.mode γ y) := by
  have h1 : Integrable (fun y => hdGc d s i (x - y)) := (hdGc_integrable hd hs0 hs1 i).comp_sub_left x
  exact h1.mul_bdd (Torus.continuous_mode γ).aestronglyMeasurable
    (Eventually.of_forall fun y => (Torus.norm_mode γ y).le)

theorem hdJ (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs1 : s + 1 < d) (lam β : Lattice d) (x : Torus d) :
    ∫ y, hdH d s lam x y * Torus.mode β y = hdK d s lam β * Torus.mode (lam + β) x := by
  set c : Fin d → ℂ := fun i => 2 * Real.pi * Complex.I * ((lam i : ℤ) : ℂ) with hc
  have e : ∀ y, hdH d s lam x y * Torus.mode β y = ∑ i, c i *
      (Torus.mode lam x * (hdGc d s i (x - y) * Torus.mode β y) -
        hdGc d s i (x - y) * Torus.mode (lam + β) y) := by
    intro y
    unfold hdH
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Torus.mode_add]
    simp only [hc]
    ring
  simp_rw [e]
  rw [integral_finset_sum _ (fun i _ => ?_)]
  · unfold hdK
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, integral_sub ((hd_integrable_Gmode hd hs0 hs1 i β x).const_mul _)
      (hd_integrable_Gmode hd hs0 hs1 i (lam + β) x), integral_const_mul, hdConv hd hs0 hs1,
      hdConv hd hs0 hs1, Torus.mode_add]
    simp only [hc]
    ring
  · exact (((hd_integrable_Gmode hd hs0 hs1 i β x).const_mul _).sub
      (hd_integrable_Gmode hd hs0 hs1 i (lam + β) x)).const_mul _

theorem hdI (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs1 : s + 1 < d) (α lam β : Lattice d) :
    ∫ x, Torus.mode α x * ∫ y, hdH d s lam x y * Torus.mode β y =
      if α + lam + β = 0 then hdK d s lam β else 0 := by
  have e : ∀ x, Torus.mode α x * ∫ y, hdH d s lam x y * Torus.mode β y =
      hdK d s lam β * Torus.mode (α + (lam + β)) x := by
    intro x
    rw [hdJ hd hs0 hs1, Torus.mode_add α]
    ring
  simp_rw [e]
  rw [integral_const_mul, Torus.integral_mode, add_assoc]
  split_ifs <;> simp

end HRS.MC.QRSpec.Hd

end
