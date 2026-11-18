import HRS.Whole.MovtrAux5

/-!
# MOVTR auxiliary 6: the velocity of the translated equilibrium is `q a`
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

lemma movtr_gradient_comp_sub (f : Euc d → ℝ) (a x : Euc d) :
    gradient (fun y => f (y - a)) x = gradient f (x - a) := by
  unfold gradient
  rw [fderiv_comp_sub]

lemma movtr_force_comp_sub (s : ℝ) (ρ : Euc d → ℝ) (a x : Euc d) :
    convGradConvW (rieszKernelGrad d s) (fun y => ρ (y - a)) x =
      convGradConvW (rieszKernelGrad d s) ρ (x - a) := by
  unfold convGradConvW
  rw [← integral_sub_right_eq_self (fun y => if ‖x - a - y‖ ≤ 1 / 4 then
    (ρ y - ρ (x - a)) • rieszKernelGrad d s (x - a - y) else
    ρ y • rieszKernelGrad d s (x - a - y)) a]
  congr 1
  funext y
  rw [sub_sub_sub_cancel_right]

lemma movtr_movU_translate (s q β : ℝ) (ρ₀ : Euc d → ℝ)
    (hforce : ∀ y, β⁻¹ • gradient (fun y => Real.log (ρ₀ y)) y + q • y +
      convGradConvW (rieszKernelGrad d s) ρ₀ y = 0) (a x : Euc d) :
    movU d s q β (fun y => ρ₀ (y - a)) x = q • a := by
  unfold movU movForce
  rw [show (fun y => Real.log (ρ₀ (y - a))) = fun y => (fun z => Real.log (ρ₀ z)) (y - a) from rfl,
    movtr_gradient_comp_sub (fun z => Real.log (ρ₀ z)), movtr_force_comp_sub]
  have h := hforce (x - a)
  have : q • x = q • (x - a) + q • a := by rw [← smul_add]; simp
  rw [this]
  calc β⁻¹ • gradient (fun z => Real.log (ρ₀ z)) (x - a) + (q • (x - a) + q • a) +
        convGradConvW (rieszKernelGrad d s) ρ₀ (x - a)
      = (β⁻¹ • gradient (fun z => Real.log (ρ₀ z)) (x - a) + q • (x - a) +
          convGradConvW (rieszKernelGrad d s) ρ₀ (x - a)) + q • a := by abel
    _ = q • a := by rw [h, zero_add]


lemma movtr_cbNormVecE_const (k : ℕ) (v : Euc d) :
    cbNormVecE k (fun _ => v) = ENNReal.ofReal ‖v‖ := by
  unfold cbNormVecE
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    simp [iteratedFDeriv_const_of_ne hj]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos k)) h

lemma movtr_lintegral_decay {q : ℝ} (hq : 0 < q) (a₀ : Euc d) :
    ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal ‖q • (Real.exp (-q * t) • a₀)‖ = ENNReal.ofReal ‖a₀‖ := by
  have hfun : ∀ t : ℝ, ‖q • (Real.exp (-q * t) • a₀)‖ = ‖a₀‖ * q * Real.exp (-q * t) := by
    intro t
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hq,
      abs_of_pos (Real.exp_pos _)]
    ring
  simp_rw [hfun]
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-q * t)) (Set.Ioi 0) := by
    simpa using integrableOn_exp_mul_Ioi (a := -q) (by linarith) 0
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] fun t => ‖a₀‖ * q * Real.exp (-q * t) :=
    Filter.Eventually.of_forall fun t => by positivity
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _) hnn, integral_const_mul,
    integral_exp_mul_Ioi (by linarith : -q < 0)]
  congr 1
  field_simp
  simp

end HRS.Whole
