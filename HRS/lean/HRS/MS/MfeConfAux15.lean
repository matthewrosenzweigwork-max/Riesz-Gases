import HRS.MS.MfeConfAux14

/-!
# S.B.1, packet F3 (reductions): `A(h) = Div(h u_V)` and the integrated normaliser identity from its derivative

* `sb1A_eq_div`: for a positive slice, `A(h) = ∑_k ∂_k(h (u_V)_k)` with `u_V = β⁻¹∇log h + ∇g*h + ∇V = mfeTransportW`.
  So the classical time derivative of `sb1_traj_classical` is `Div(ρ_r u_V^r)`, the form used by the normaliser identity and by
  the Itô calculus of the moving reference.
* `sb1_logK_of_deriv`: `SbLogK` follows from the pointwise derivative `(log K_r)' = βN E_{Q_r}[C_N]` on `(0,T)` plus continuity of
  `log K` on `[0,T]` and integrability of `E_Q C_N` (FTC); the open analytic content of F3 is the derivative statement.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d : ℕ}

theorem sb1_transport_apply (D : Whole.WholeDyn d) {h : Euc d → ℝ} (hh : Differentiable ℝ h)
    (hpos : ∀ y, 0 < h y) (k : Fin d) (y : Euc d) :
    h y * (Whole.mfeTransportW D h y) k =
      D.invβ * fderiv ℝ h y (sb1e k) + sb1Flux D h k y := by
  have hlog : HasFDerivAt (fun y => Real.log (h y)) ((h y)⁻¹ • fderiv ℝ h y) y :=
    (hh y).hasFDerivAt.log (hpos y).ne'
  have hg : gradient (fun y => Real.log (h y)) y k = (h y)⁻¹ * fderiv ℝ h y (sb1e k) := by
    rw [sb1_grad_apply, hlog.fderiv]
    simp
  unfold Whole.mfeTransportW Whole.mfeTransport0W sb1Flux sb1F
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hg, sb1_grad_apply]
  have := (hpos y).ne'
  field_simp
  ring

theorem sb1A_eq_div (D : Whole.WholeDyn d) {B : ℝ} (P : Sb1Pot D.V B) (hd : 1 ≤ d)
    (hs0 : 0 ≤ D.s) (hsd : D.s < d) {C : ℝ} {h : Euc d → ℝ} (S : Sb1Slice d C h) (hpos : ∀ y, 0 < h y)
    (x : Euc d) :
    sb1A D h x = ∑ k, fderiv ℝ (fun y => h y * (Whole.mfeTransportW D h y) k) x (sb1e k) := by
  have hh : ContDiff ℝ 3 h := S.decay.1
  have e : ∀ k : Fin d, (fun y => h y * (Whole.mfeTransportW D h y) k) =
      fun y => D.invβ * fderiv ℝ h y (sb1e k) + sb1Flux D h k y := fun k =>
    funext fun y => sb1_transport_apply D (hh.differentiable (by norm_num)) hpos k y
  have hd1 : ∀ k : Fin d, DifferentiableAt ℝ (fun y => fderiv ℝ h y (sb1e k)) x := fun k =>
    ((hh.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const |>.differentiable
      (by norm_num)) x
  have hd2 : ∀ k : Fin d, DifferentiableAt ℝ (sb1Flux D h k) x := fun k =>
    ((sb1_flux_contDiff D P hd hs0 hsd S k).differentiable (by norm_num)) x
  unfold sb1A
  simp_rw [e]
  have : ∀ k : Fin d, fderiv ℝ (fun y => D.invβ * fderiv ℝ h y (sb1e k) + sb1Flux D h k y) x =
      D.invβ • fderiv ℝ (fun y => fderiv ℝ h y (sb1e k)) x + fderiv ℝ (sb1Flux D h k) x := fun k => by
    rw [fderiv_fun_add ((hd1 k).const_mul _) (hd2 k), fderiv_const_mul (hd1 k)]
  simp_rw [this]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, Finset.mul_sum]

/-- **F3 (reduction)**: the integrated normaliser identity from the pointwise derivative of `log K_r`. -/
theorem sb1_logK_of_deriv {D : Whole.WholeDyn d} {N : ℕ} {T : ℝ} {ρ : ℝ → Euc d → ℝ} (hT : 0 ≤ T)
    (hcont : ContinuousOn (fun r => Real.log (Whole.gibbsNormalizer (Whole.rieszKernel d D.s) N D.invβ⁻¹
      (Whole.withDensityReal (ρ r)))) (Set.Icc 0 T))
    (hder : ∀ r ∈ Set.Ioo (0 : ℝ) T, HasDerivAt (fun r' => Real.log (Whole.gibbsNormalizer
      (Whole.rieszKernel d D.s) N D.invβ⁻¹ (Whole.withDensityReal (ρ r'))))
      (D.invβ⁻¹ * N * sb1EQ D N ρ r) r)
    (hint : IntegrableOn (sb1EQ D N ρ) (Set.Icc 0 T)) : SbLogK D N T ρ := by
  refine ⟨hint, fun t ht => ?_⟩
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl ht.2
  have hint' : IntervalIntegrable (fun r => D.invβ⁻¹ * N * sb1EQ D N ρ r) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht.1]
    exact (hint.mono_set hsub).const_mul _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (hcont.mono hsub) (fun r hr => hder r ⟨hr.1, lt_of_lt_of_le hr.2 ht.2⟩) hint'
  rw [intervalIntegral.integral_of_le ht.1, ← integral_Icc_eq_integral_Ioc, integral_const_mul] at hFTC
  exact hFTC.symm

end HRS.MS.MfeConf
