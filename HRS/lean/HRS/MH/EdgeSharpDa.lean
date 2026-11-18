import HRS.PDE.Hadamard
import HRS.PDE.MeanFieldDefs
import HRS.Main.Q42Aux1

/-!
# EdgeSharp Group D (packets D1, D2, D3, D5a)

Statements copied verbatim from `HRS/MH/EdgeSharpSpec.lean`.  Routes: see the packet docstrings there.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.EdgeSharp

open HRS

variable {d : ℕ}

/-- [D1] The forward generator at density `1`, `V = 0` is diagonal for every datum `F` (generalizes `PDE.forwardGen_const_density`
from `deltaCoeff k`).  Route: copy the proof of `PDE.forwardGen_const_density` (`HRS/PDE/Hadamard.lean:170`): `driftCoeff_const`, `nonlocalCoeff_const`
(already general in `F`), `quadS_eq_sum'`, `laplaceCoeff`; `Finset.sum_congr`/`ring` with `Complex.I_sq`. -/
theorem forwardGen_const_density_all (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (M : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (hν : 0 ≤ ν) (F : PDE.Coeff d) (k : Lattice d) :
    PDE.forwardGen (PDE.modelData d s hs0 hsd M ν hν) (fun _ => 1) F k =
      ((PDE.modelEigenvalue d s ν M k : ℝ) : ℂ) * F k := by
  have hV : (PDE.modelData d s hs0 hsd M ν hν).V = fun _ => 0 := rfl
  have hT : PDE.transportCoeff (PDE.modelData d s hs0 hsd M ν hν) (fun _ => 1) F k = 0 := by
    simp only [PDE.transportCoeff, PDE.driftCoeff_const _ hV, PDE.mulCoeff]
    simp
  have hN : PDE.nonlocalCoeff (PDE.modelData d s hs0 hsd M ν hν) (fun _ => 1) F k =
      ((1 : ℝ) : ℂ) * ∑ i : Fin d, ∑ j : Fin d, ((M j i : ℝ) : ℂ) *
        ((2 * Real.pi * Complex.I * (k i : ℂ)) *
          (((rieszCoeff d s k : ℝ) : ℂ) * (2 * Real.pi * Complex.I * (k j : ℂ) * F k))) :=
    PDE.nonlocalCoeff_const _ 1 F k
  have key : ∀ i j' : Fin d, ((M j' i : ℝ) : ℂ) * ((2 * Real.pi * Complex.I * (k i : ℂ)) *
      (((rieszCoeff d s k : ℝ) : ℂ) * (2 * Real.pi * Complex.I * (k j' : ℂ) * F k))) =
      -(4 * (Real.pi : ℂ) ^ 2 * ((rieszCoeff d s k : ℝ) : ℂ) *
        ((k i : ℂ) * ((M j' i : ℝ) : ℂ) * (k j' : ℂ)) * F k) := by
    intro i j'
    linear_combination (4 * (Real.pi : ℂ) ^ 2 * ((rieszCoeff d s k : ℝ) : ℂ) *
        ((k i : ℂ) * ((M j' i : ℝ) : ℂ) * (k j' : ℂ)) * F k) * Complex.I_sq
  simp only [PDE.forwardGen]
  rw [hT, hN]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j' _ => key i j'))]
  simp only [PDE.modelData, PDE.laplaceCoeff, PDE.modelEigenvalue, PDE.quadS_eq_sum' M k]
  push_cast
  have hsum : ∑ x : Fin d, ∑ x_1 : Fin d, 4 * (Real.pi : ℂ) ^ 2 * ((rieszCoeff d s k : ℝ) : ℂ) *
      ((k x : ℂ) * ((M x_1 x : ℝ) : ℂ) * (k x_1 : ℂ)) * F k =
      4 * (Real.pi : ℂ) ^ 2 * ((rieszCoeff d s k : ℝ) : ℂ) *
        (∑ x : Fin d, ∑ i : Fin d, (k x : ℂ) * ((M i x : ℝ) : ℂ) * (k i : ℂ)) * F k := by
    simp only [Finset.mul_sum, Finset.sum_mul]
  simp only [Finset.sum_neg_distrib]
  linear_combination hsum

/-- [D2] Scalar ODE: a function on `[0,t]` continuous with `G τ = c + λ ∫_0^τ G` is `c e^{λτ}`.  Route: `G` is `C¹` on `(0,t)` with `G' = λ G`
(`intervalIntegral.integral_hasDerivAt_right`, `ContinuousOn.intervalIntegrable`); `τ ↦ e^{-λτ} G τ` has zero derivative on `Ioo 0 t`,
continuous on `Icc 0 t`, so it is constant (`constant_of_has_deriv_right_zero` or `constant_of_derivWithin_zero`, `Mathlib/Analysis/Calculus/MeanValue.lean:360,366`);
value `c` at `τ = 0`. -/
theorem eq_exp_mul_of_integral_eq {t : ℝ} (lam : ℝ) (c : ℂ) (G : ℝ → ℂ) (hG : ContinuousOn G (Set.Icc 0 t))
    (h : ∀ τ ∈ Set.Icc 0 t, G τ = c + (lam : ℂ) * ∫ σ in (0 : ℝ)..τ, G σ) :
    ∀ τ ∈ Set.Icc 0 t, G τ = ((Real.exp (lam * τ) : ℝ) : ℂ) * c := by
  intro τ hτ
  have ht0 : (0 : ℝ) ≤ t := hτ.1.trans hτ.2
  have hG0 : G 0 = c := by
    have h0 := h 0 ⟨le_refl 0, ht0⟩
    simpa using h0
  rcases ht0.eq_or_lt with ht | htpos
  · have hτ0 : τ = 0 := by linarith [hτ.1, hτ.2]
    subst hτ0
    simp [hG0]
  -- derivative of the integral on the open interval
  have hint : ∀ u ∈ Set.Ioo 0 t, HasDerivAt (fun v => ∫ σ in (0 : ℝ)..v, G σ) (G u) u := by
    intro u hu
    have hIcc : u ∈ Set.Icc 0 t := Set.Ioo_subset_Icc_self hu
    have hGi : IntervalIntegrable G MeasureTheory.volume 0 u :=
      (hG.mono (Set.uIcc_subset_Icc (Set.left_mem_Icc.2 ht0) hIcc)).intervalIntegrable
    have hmeas : StronglyMeasurableAtFilter G (nhds u) :=
      (hG.mono Set.Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo u hu
    have hcont : ContinuousAt G u := hG.continuousAt (Icc_mem_nhds hu.1 hu.2)
    exact intervalIntegral.integral_hasDerivAt_right hGi hmeas hcont
  -- derivative of G on the open interval
  have hGd : ∀ u ∈ Set.Ioo 0 t, HasDerivAt G ((lam : ℂ) * G u) u := by
    intro u hu
    have hev : G =ᶠ[nhds u] fun v => c + (lam : ℂ) * ∫ σ in (0 : ℝ)..v, G σ := by
      filter_upwards [Ioo_mem_nhds hu.1 hu.2] with v hv
      exact h v (Set.Ioo_subset_Icc_self hv)
    exact ((hint u hu).const_mul (lam : ℂ) |>.const_add c).congr_of_eventuallyEq hev
  -- the function H(v) = exp(-λ v) G(v) has zero derivative on the open interval
  have hHd : ∀ u ∈ Set.Ioo 0 t,
      HasDerivAt (fun v => ((Real.exp (-(lam * v)) : ℝ) : ℂ) * G v) 0 u := by
    intro u hu
    have hexp : HasDerivAt (fun v : ℝ => Real.exp (-(lam * v)))
        (Real.exp (-(lam * u)) * (-(lam * 1))) u :=
      (((hasDerivAt_id' u).const_mul lam).neg).exp
    have := hexp.ofReal_comp.mul (hGd u hu)
    convert this using 1
    push_cast
    ring
  have hconst : ∀ u ∈ Set.Ioo 0 t, ∀ v ∈ Set.Ioo 0 t,
      ((Real.exp (-(lam * u)) : ℝ) : ℂ) * G u = ((Real.exp (-(lam * v)) : ℝ) : ℂ) * G v := by
    have hdiff : DifferentiableOn ℝ (fun v => ((Real.exp (-(lam * v)) : ℝ) : ℂ) * G v)
        (Set.Ioo 0 t) := fun u hu => (hHd u hu).differentiableAt.differentiableWithinAt
    have hder : Set.EqOn (deriv fun v => ((Real.exp (-(lam * v)) : ℝ) : ℂ) * G v) 0
        (Set.Ioo 0 t) := fun u hu => (hHd u hu).deriv
    exact fun u hu v hv => IsOpen.is_const_of_deriv_eq_zero isOpen_Ioo isPreconnected_Ioo hdiff hder hu hv
  -- extend the constancy to the closed interval by continuity
  have hHc : ContinuousOn (fun v => ((Real.exp (-(lam * v)) : ℝ) : ℂ) * G v) (Set.Icc 0 t) :=
    (Continuous.continuousOn (by fun_prop)).mul hG
  have hcl : closure (Set.Ioo (0 : ℝ) t) = Set.Icc 0 t := closure_Ioo htpos.ne
  have hmid : t / 2 ∈ Set.Ioo (0 : ℝ) t := ⟨by linarith, by linarith⟩
  have hEq : Set.EqOn (fun v => ((Real.exp (-(lam * v)) : ℝ) : ℂ) * G v)
      (fun _ => ((Real.exp (-(lam * (t / 2))) : ℝ) : ℂ) * G (t / 2)) (Set.Icc 0 t) := by
    refine Set.EqOn.of_subset_closure (s := Set.Ioo 0 t) ?_ hHc continuousOn_const
      Set.Ioo_subset_Icc_self hcl.symm.subset
    intro v hv
    exact hconst v hv (t / 2) hmid
  have h0 := hEq (⟨le_refl 0, ht0⟩ : (0 : ℝ) ∈ Set.Icc 0 t)
  have h1 := hEq hτ
  simp only [hG0, mul_zero, neg_zero, Real.exp_zero, Complex.ofReal_one, one_mul] at h0
  simp only at h1
  rw [← h0] at h1
  have hprod : ((Real.exp (lam * τ) : ℝ) : ℂ) * ((Real.exp (-(lam * τ)) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp
  calc G τ = ((Real.exp (lam * τ) : ℝ) : ℂ) * (((Real.exp (-(lam * τ)) : ℝ) : ℂ) * G τ) := by
        rw [← mul_assoc, hprod, one_mul]
    _ = ((Real.exp (lam * τ) : ℝ) : ℂ) * c := by rw [h1]

/-- [D3] The model eigenvalue is even in `k`.  Route: unfold `PDE.modelEigenvalue`, `PDE.quadS`; `Lattice.enorm (-k) = Lattice.enorm k`
(`HRS.enorm_neg`, `HRS/Energy/Commutator/FourierAux.lean:359`), `rieszCoeff_neg` (`HRS/Kernel/Riesz.lean:769`), `(-k i)*M*(-k j) = k i * M * k j` (`neg_mul_neg`). -/
theorem modelEigenvalue_neg (d : ℕ) (s ν : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (k : Lattice d) :
    PDE.modelEigenvalue d s ν M (-k) = PDE.modelEigenvalue d s ν M k := by
  unfold PDE.modelEigenvalue
  rw [PDE.quadS_eq_sum' M (-k), PDE.quadS_eq_sum' M k, HRS.enorm_neg, HRS.rieszCoeff_neg]
  simp only [Pi.neg_apply, Int.cast_neg, neg_mul, mul_neg, neg_neg]

/-- [D5a] Pairing of a continuous function with a real cosine mode through the Fourier coefficients:
`∫ f ψ_k = (√2/2)(f̂(k) + f̂(-k))`.  Route: `PDE.cosTest`, `q42_cos_complex` (`HRS/Main/Q42Aux1.lean:52`), `PDE.funFourierCoeff_eq_int`
(`mFourier (-j) x = Torus.mode (-j) x`), `Torus.mode_neg`, `integral_add`, `integral_const_mul`, `integral_ofReal`; integrability of
continuous functions on the compact torus. -/
theorem integral_mul_cosTest_eq_coeff (k : Lattice d) {f : Torus d → ℝ} (hf : Continuous f) :
    (((∫ x, f x * PDE.cosTest k x : ℝ)) : ℂ) =
      ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (PDE.coeffOf f k + PDE.coeffOf f (-k)) := by
  have hcoeff : ∀ j : Lattice d, PDE.coeffOf f j = ∫ x, (f x : ℂ) * Torus.mode (-j) x := by
    intro j
    show Torus.funFourierCoeff (fun x => (f x : ℂ)) j = _
    rw [PDE.funFourierCoeff_eq_int]
    congr 1
    funext x
    exact mul_comm _ _
  have hpt : ∀ x : Torus d, ((f x * PDE.cosTest k x : ℝ) : ℂ) =
      ((Real.sqrt 2 / 2 : ℝ) : ℂ) * ((f x : ℂ) * (Torus.mode k x + Torus.mode (-k) x)) := by
    intro x
    have hc := HRS.q42_cos_complex k x
    unfold PDE.cosTest
    push_cast
    rw [hc]
    ring
  have hfc : Continuous fun x => (f x : ℂ) := Complex.continuous_ofReal.comp hf
  have hint : ∀ j : Lattice d, MeasureTheory.Integrable (fun x => (f x : ℂ) * Torus.mode j x) :=
    fun j => Continuous.integrable_of_hasCompactSupport (hfc.mul (Torus.continuous_mode j))
      (HasCompactSupport.of_compactSpace _)
  rw [← integral_complex_ofReal]
  simp only [hpt]
  rw [MeasureTheory.integral_const_mul]
  simp only [mul_add]
  rw [MeasureTheory.integral_add (hint k) (hint (-k)), hcoeff k, hcoeff (-k), neg_neg]
  ring

end HRS.MH.EdgeSharp
