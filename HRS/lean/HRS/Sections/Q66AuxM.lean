import HRS.Sections.Q66AuxL

/-!
# Packet Q66: the one-body integral of the transport kernel
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Q66

open HRS.Q84d HRS.PDE HRS.PDE.MFAux HRS.PDE.MFSchauder

variable {d : ℕ} {s : ℝ} {N : ℕ}

theorem q66_integrable_G_comp (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) (x : Torus d)
    (k : Fin d) : Integrable (fun y : Torus d => (periodicRieszGrad d s (x - y)) k) := by
  have h1 : Integrable (fun y => periodicRieszGrad d s (x - y)) :=
    (q66_gradKernel_integrable hd hs0 hs1).comp_sub_left x
  exact (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).integrable_comp h1

theorem q66_integrable_mulG (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) (x : Torus d)
    (k : Fin d) {f : Torus d → ℝ} (hf : Continuous f) :
    Integrable (fun y : Torus d => f y * (periodicRieszGrad d s (x - y)) k) := by
  obtain ⟨B, hB⟩ := exists_bound_of_cont hf
  exact (q66_integrable_G_comp hd hs0 hs1 x k).bdd_mul hf.aestronglyMeasurable
    (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hB y)

theorem q66_conv_sum {g : Torus d → ℝ} (hg : Integrable g) {ι : Type*} (t : Finset ι)
    (f : ι → Torus d → ℝ) (hf : ∀ i, Continuous (f i)) (x : Torus d) :
    convFun g (fun y => ∑ i ∈ t, f i y) x = ∑ i ∈ t, convFun g (f i) x := by
  unfold convFun
  have hint : ∀ i ∈ t, Integrable (fun y => g (x - y) * f i y) := by
    intro i _
    obtain ⟨B, hB⟩ := exists_bound_of_cont (hf i)
    have := (hg.comp_sub_left x).bdd_mul (hf i).aestronglyMeasurable
      (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hB y)
    exact this.congr (Eventually.of_forall fun y => by simp [mul_comm])
  rw [← integral_finsetSum _ hint]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [Finset.mul_sum]

theorem q66_int_hv (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) {v : Fin d → Torus d → ℝ} (hv : ∀ j, Torus.IsSmooth (v j))
    {r : Torus d → ℝ} (hr : Torus.IsSmooth r)
    (hdiv : ∀ x, ∑ j, Torus.partialDeriv j (fun y => ρ y * v j y) x = -(ρ x * r x)) (x : Torus d) :
    ∫ y, q66_hv d s v x y ∂(withDensityReal ρ) =
      ∑ k, v k x * (∫ y, ρ y * (periodicRieszGrad d s (x - y)) k) +
        convFun (periodicRiesz d s) (fun y => ρ y * r y) x := by
  have hsd : s < d := by linarith
  have F : MFInputs.MFKernelFacts d s := MFInputs.mfKernelFacts_of_two hd s hs0 hsd
  have hρc : Continuous ρ := q66_cont_of_smooth hρ.smooth
  have haS : ∀ k, Torus.IsSmooth (fun y => ρ y * v k y) := fun k => q66_isSmooth_mul hρ.smooth (hv k)
  have haC : ∀ k, Continuous (fun y => ρ y * v k y) := fun k => q66_cont_of_smooth (haS k)
  have hpdS : ∀ k, Torus.IsSmooth (Torus.partialDeriv k (fun y => ρ y * v k y)) := fun k =>
    q66_isSmooth_partialDeriv (haS k) k
  have hpdC : ∀ k, Continuous (Torus.partialDeriv k (fun y => ρ y * v k y)) := fun k =>
    q66_cont_of_smooth (hpdS k)
  rw [integral_withDensityReal_eq ρ hρ.density.measurable (fun y => (hρ.pos y).le)]
  have e1 : ∀ y, ρ y * q66_hv d s v x y =
      ∑ k, (v k x * (ρ y * (periodicRieszGrad d s (x - y)) k) -
        (ρ y * v k y) * (periodicRieszGrad d s (x - y)) k) := by
    intro y
    unfold q66_hv
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  simp_rw [e1]
  have hi1 : ∀ k ∈ (Finset.univ : Finset (Fin d)), Integrable (fun y : Torus d =>
      v k x * (ρ y * (periodicRieszGrad d s (x - y)) k)) := fun k _ =>
    (q66_integrable_mulG hd hs0 hs1 x k hρc).const_mul _
  have hi2 : ∀ k ∈ (Finset.univ : Finset (Fin d)), Integrable (fun y : Torus d =>
      (ρ y * v k y) * (periodicRieszGrad d s (x - y)) k) := fun k _ =>
    q66_integrable_mulG hd hs0 hs1 x k (haC k)
  have hi3 : ∀ k ∈ (Finset.univ : Finset (Fin d)), Integrable (fun y : Torus d =>
      v k x * (ρ y * (periodicRieszGrad d s (x - y)) k) -
        (ρ y * v k y) * (periodicRieszGrad d s (x - y)) k) := fun k hk => (hi1 k hk).sub (hi2 k hk)
  rw [integral_finsetSum _ hi3]
  have e4 : ∀ k : Fin d, ∫ y : Torus d, (v k x * (ρ y * (periodicRieszGrad d s (x - y)) k) -
        (ρ y * v k y) * (periodicRieszGrad d s (x - y)) k) =
      v k x * (∫ y, ρ y * (periodicRieszGrad d s (x - y)) k) -
        ∫ y, (ρ y * v k y) * (periodicRieszGrad d s (x - y)) k := fun k => by
    rw [integral_sub (hi1 k (Finset.mem_univ _)) (hi2 k (Finset.mem_univ _)), integral_const_mul]
  simp_rw [e4]
  rw [Finset.sum_sub_distrib]
  congr 1
  -- the second sum
  have e2 : ∀ k, ∫ y, (ρ y * v k y) * (periodicRieszGrad d s (x - y)) k =
      convFun (periodicRiesz d s) (Torus.partialDeriv k (fun y => ρ y * v k y)) x := by
    intro k
    rw [q66_grad_conv hd hs0 hs1 (q66_isCk_of_smooth (haS k) 1) k x,
      convFun_partialDeriv F.integrable (q66_isCk_of_smooth (haS k) 1) k x]
  simp_rw [e2]
  rw [← q66_conv_sum F.integrable Finset.univ _ hpdC x]
  have e3 : (fun y => ∑ k, Torus.partialDeriv k (fun y => ρ y * v k y) y) = fun y => -(ρ y * r y) :=
    funext hdiv
  rw [e3]
  unfold convFun
  simp only [mul_neg, integral_neg, sub_neg_eq_add]

end HRS.Q66

end
