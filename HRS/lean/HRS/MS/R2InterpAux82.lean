import HRS.MS.R2InterpAux81
import HRS.MS.R2InterpAux79
import HRS.MH.DualityRdB1Aux
import HRS.MS.R2WfmAux3
import HRS.MS.Comm

/-!
# S10.2 (worker S10R), part 82 (packet F5b): the commutator kernels of the orbits `U^{r,t}φ`

For a classical adjoint solution `f` on `[0,t]`: the gradient field is jointly measurable in `(r,x)` (truncated outside `[0,t]`), the commutator kernels
of `∇f_r` are bounded pair kernels with a constant uniform in `r ∈ [0,t]`, and the kernel family is jointly measurable.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d : ℕ} {C : WholeCoeff d}

theorem s102_gradJoint_cont {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW C t φ f) :
    Continuous fun p : Icc (0 : ℝ) t × Euc d => gradient (f p.1) p.2 := by
  have key : Continuous fun p : Icc (0 : ℝ) t × Euc d =>
      (EuclideanSpace.equiv (Fin d) ℝ).symm (fun a => gradient (f p.1) p.2 a) :=
    (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.comp (continuous_pi fun a => s102_grad_jointCont hf a)
  exact key.congr fun p => rfl

theorem s102_gradJoint_meas {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW C t φ f) :
    Measurable fun p : ℝ × Euc d => if p.1 ∈ Icc (0 : ℝ) t then gradient (f p.1) p.2 else 0 := by
  classical
  have hcont : ContinuousOn (fun p : ℝ × Euc d => gradient (f p.1) p.2) (Icc (0 : ℝ) t ×ˢ univ) := by
    rw [continuousOn_iff_continuous_restrict]
    have h1 : Continuous fun p : (Icc (0 : ℝ) t ×ˢ (univ : Set (Euc d))) =>
        ((⟨p.1.1, (mem_prod.1 p.2).1⟩ : Icc (0 : ℝ) t), p.1.2) :=
      (continuous_subtype_val.fst.subtype_mk _).prodMk (continuous_subtype_val.snd)
    exact (s102_gradJoint_cont hf).comp h1
  have hset : MeasurableSet (Icc (0 : ℝ) t ×ˢ (univ : Set (Euc d))) := measurableSet_Icc.prod MeasurableSet.univ
  have := ContinuousOn.measurable_piecewise (f := fun p : ℝ × Euc d => gradient (f p.1) p.2)
    (g := fun _ => (0 : Euc d)) (s := Icc (0 : ℝ) t ×ˢ univ) hcont continuousOn_const hset
  have e : (fun p : ℝ × Euc d => if p.1 ∈ Icc (0 : ℝ) t then gradient (f p.1) p.2 else 0) =
      Set.piecewise (Icc (0 : ℝ) t ×ˢ (univ : Set (Euc d))) (fun p : ℝ × Euc d => gradient (f p.1) p.2)
        (fun _ => (0 : Euc d)) := by
    funext p
    simp only [Set.piecewise, mem_prod, mem_univ, and_true]
  rw [e]
  exact this

theorem s102_kernelFam_meas (s : ℝ) (V : ℝ → Euc d → Euc d) (hV : Measurable fun p : ℝ × Euc d => V p.1 p.2) :
    Measurable fun q : ℝ × Euc d × Euc d => commutatorKernel d s (V q.1) q.2.1 q.2.2 := by
  unfold commutatorKernel
  have h1 : Measurable fun q : ℝ × Euc d × Euc d => V q.1 q.2.1 :=
    hV.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have h2 : Measurable fun q : ℝ × Euc d × Euc d => V q.1 q.2.2 :=
    hV.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  exact (h1.sub h2).inner ((movtr_rieszKernelGrad_measurable (d := d) s).comp
    ((measurable_fst.comp measurable_snd).sub (measurable_snd.comp measurable_snd)))

/-- Uniform Lipschitz bound of the gradients of the orbit. -/
theorem s102_grad_lip_unif {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW C t φ f) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ r ∈ Icc (0 : ℝ) t, ∀ x y : Euc d, ‖gradient (f r) x - gradient (f r) y‖ ≤ L * ‖x - y‖ := by
  obtain ⟨B, hB⟩ := hf.bdd 2 le_rfl
  refine ⟨max B 0, le_max_right _ _, fun r hr x y => ?_⟩
  have hb : ∀ z ∈ (Set.univ : Set (Euc d)), ‖fderiv ℝ (gradient (f r)) z‖ ≤ max B 0 := by
    intro z _
    refine (HRS.MH.DualityRd.db1_fderiv_gradient_le (hf.c2 r hr) z).trans ?_
    have h1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f r) (x := z) (n := 1)
    have h2 := norm_iteratedFDeriv_one (𝕜 := ℝ) (x := z) (fderiv ℝ (f r))
    rw [← h2, h1]
    exact (hB r hr z).trans (le_max_left _ _)
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => HRS.MH.DualityRd.db1_gradient_differentiable (hf.c2 r hr) z) hb convex_univ (Set.mem_univ x)
    (Set.mem_univ y)
  rw [norm_sub_rev (gradient (f r) x), norm_sub_rev x y] at *
  exact h

/-- The commutator kernels of the orbit are bounded pair kernels, uniformly in `r ∈ [0,t]`. -/
theorem s102_orbit_kernel_bdd {s : ℝ} (hs0 : 0 ≤ s) {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) :
    ∃ B : ℝ, ∀ r ∈ Icc (0 : ℝ) t, IsBoundedPairKernel s B (commutatorKernel d s (fun x => gradient (f r) x)) := by
  obtain ⟨L, hL0, hL⟩ := s102_grad_lip_unif hf
  refine ⟨max s 1 * L, fun r hr => ⟨?_, ?_, ?_⟩⟩
  · exact HRS.MS.Comm.comm_meas _ (HRS.MH.DualityRd.db1_gradient_continuous (hf.c2 r hr)).measurable
  · exact fun x y => HRS.MS.Comm.comm_symm _ x y
  · intro x y hxy
    exact HRS.MS.R2Wfm.s97_comm_bound hs0 hL0 x y hxy (hL r hr x y)

end HRS.MS.R2Interp

end
