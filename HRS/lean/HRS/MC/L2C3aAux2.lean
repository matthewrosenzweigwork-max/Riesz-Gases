import HRS.MC.L2C3aAux1
import HRS.Dynamics.Setup
import HRS.Kernel.GradReg
import HRS.PDE.MeanFieldLinearLoss

/-!
# Packet L2C-3a, helper 2: plain form of the backward generator for `M = -I`

For `M = -I`, `s + 1 < d` and bounded measurable `ρ`:
`𝓛_ρ f(x) = β⁻¹Δf(x) + ⟨-(∫ ρ(x-z) ∇g(z) dz) - ∇V(x), ∇f(x)⟩ + ∫ ρ(x-z) ⟨∇f(x-z), ∇g(z)⟩ dz`.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.MC.L2C3a

variable {d : ℕ}

theorem l2c3a_bdd_of_cont {E : Type*} [NormedAddCommGroup E] (g : Torus d → E) (hg : Continuous g) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖g x‖ ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
  exact ⟨max B 0, le_max_right _ _, fun x => (hB x (Set.mem_univ x)).trans (le_max_left _ _)⟩

/-- Kernel facts: `∇g` is a good kernel and in `L¹` when `s + 1 < d`. -/
theorem l2c3a_kernel (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s + 1 < d) :
    ∃ C : ℝ, HRS.KernelGrad.GoodKernel d s C (periodicRieszGrad d s) ∧
      Integrable (periodicRieszGrad d s : Torus d → Euc d) := by
  obtain ⟨C, hG⟩ := HRS.KernelGrad.goodKernel_periodicRieszGrad hd hs0 (by linarith)
  exact ⟨C, hG, hG.integrable_G hs⟩

theorem l2c3a_conv_plain (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s + 1 < d) {h : Torus d → ℝ}
    (hm : Measurable h) {B : ℝ} (hB : ∀ x, |h x| ≤ B) (x : Torus d) :
    convGradConv (periodicRieszGrad d s) h x = ∫ z, h (x - z) • periodicRieszGrad d s z := by
  obtain ⟨C, hG, -⟩ := l2c3a_kernel hd hs0 hs
  rw [hG.eq_plain hs hm hB x]
  rw [← integral_sub_left_eq_self (fun y => h y • periodicRieszGrad d s (x - y)) volume x]
  simp only [sub_sub_cancel]

theorem l2c3a_matVec_neg_one (v : Euc d) : Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ) v = -v := by
  simp [Torus.matVec]

theorem l2c3a_integrable_smul {ρ : Torus d → ℝ} (hm : Measurable ρ) {B : ℝ} (hB : ∀ x, |ρ x| ≤ B)
    {G : Torus d → Euc d} (hGm : Measurable G) (hG : Integrable G) (x : Torus d) :
    Integrable (fun z => ρ (x - z) • G z) := by
  refine Integrable.mono' (hG.norm.const_mul B) ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact ((hm.comp (measurable_const.sub measurable_id)).smul hGm).aestronglyMeasurable
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)

theorem l2c3a_bg_plain (D : DynData d) (hd : 2 ≤ d) (hM : D.M = -1) (hs : D.s + 1 < d)
    {ρ : Torus d → ℝ} (hm : Measurable ρ) {B : ℝ} (hB : ∀ x, |ρ x| ≤ B)
    {f : Torus d → ℝ} (hf : Torus.IsCk 1 f) (x : Torus d) :
    backwardGenerator D ρ f x = D.invβ * Torus.laplacian f x +
      inner ℝ (-(∫ z, ρ (x - z) • periodicRieszGrad d D.s z) - Torus.grad D.V x) (Torus.grad f x) +
      ∫ z, ρ (x - z) * inner ℝ (Torus.grad f (x - z)) (periodicRieszGrad d D.s z) := by
  obtain ⟨C, hG, hGi⟩ := l2c3a_kernel hd D.hs0 hs
  have hgc : Continuous (Torus.grad f) := HRS.PDE.MFLinear.continuous_grad hf
  obtain ⟨Bg, hBg0, hBg⟩ := l2c3a_bdd_of_cont _ hgc
  have hcoord : ∀ j : Fin d, Continuous fun y => Torus.grad f y j := fun j =>
    (continuous_apply j).comp (PiLp.continuous_ofLp 2 _ |>.comp hgc)
  have hcomp : ∀ j : Fin d, (convGradConv (periodicRieszGrad d D.s) (fun y => ρ y *
      (Torus.matVec D.M.transpose (Torus.grad f y)) j) x) j =
      ∫ z, -(ρ (x - z) * (Torus.grad f (x - z) j * periodicRieszGrad d D.s z j)) := by
    intro j
    have e : ∀ y, ρ y * (Torus.matVec D.M.transpose (Torus.grad f y)) j =
        -(ρ y * Torus.grad f y j) := by
      intro y; rw [hM]; simp [Torus.matVec, Matrix.transpose_neg, Matrix.transpose_one]
    simp_rw [e]
    have hmj : Measurable fun y => -(ρ y * Torus.grad f y j) :=
      (hm.mul (hcoord j).measurable).neg
    have hbj : ∀ y, |-(ρ y * Torus.grad f y j)| ≤ B * Bg := by
      intro y
      rw [abs_neg, abs_mul]
      have h2 : |Torus.grad f y j| ≤ Bg := by
        have := PiLp.norm_apply_le (Torus.grad f y) j
        rw [Real.norm_eq_abs] at this
        exact this.trans (hBg y)
      exact mul_le_mul (hB y) h2 (abs_nonneg _) ((abs_nonneg _).trans (hB y))
    rw [l2c3a_conv_plain hd D.hs0 hs hmj hbj x]
    rw [eval_integral_piLp]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [PiLp.smul_apply, smul_eq_mul]
      ring
    · intro i
      have := l2c3a_integrable_smul hmj hbj hG.meas hGi x
      exact Integrable.eval_piLp this i
  unfold backwardGenerator meanFieldDrift
  simp_rw [hcomp]
  rw [hM, l2c3a_conv_plain hd D.hs0 hs hm hB x, l2c3a_matVec_neg_one]
  have hsum : ∑ j : Fin d, ∫ z, -(ρ (x - z) * (Torus.grad f (x - z) j * periodicRieszGrad d D.s z j)) =
      -∫ z, ρ (x - z) * inner ℝ (Torus.grad f (x - z)) (periodicRieszGrad d D.s z) := by
    have hint : ∀ j : Fin d, Integrable (fun z => -(ρ (x - z) *
        (Torus.grad f (x - z) j * periodicRieszGrad d D.s z j))) := by
      intro j
      refine Integrable.mono' (hGi.norm.const_mul (B * Bg)) ?_
        (Filter.Eventually.of_forall fun z => ?_)
      · have h1 : Measurable fun z => ρ (x - z) := hm.comp (measurable_const.sub measurable_id)
        have h2 : Measurable fun z => Torus.grad f (x - z) j :=
          ((hcoord j).measurable.comp (measurable_const.sub measurable_id))
        have h3 : Measurable fun z => periodicRieszGrad d D.s z j :=
          (measurable_pi_apply j).comp (PiLp.continuous_ofLp 2 _).measurable |>.comp hG.meas
        exact (h1.mul (h2.mul h3)).neg.aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_mul]
        have h1 := hB (x - z)
        have h2 : |Torus.grad f (x - z) j| ≤ Bg := by
          have := PiLp.norm_apply_le (Torus.grad f (x - z)) j
          rw [Real.norm_eq_abs] at this
          exact this.trans (hBg _)
        have h3 : |periodicRieszGrad d D.s z j| ≤ ‖periodicRieszGrad d D.s z‖ := by
          simpa using PiLp.norm_apply_le (periodicRieszGrad d D.s z) j
        calc |ρ (x - z)| * (|Torus.grad f (x - z) j| * |periodicRieszGrad d D.s z j|)
            ≤ B * (Bg * ‖periodicRieszGrad d D.s z‖) :=
              mul_le_mul h1 (mul_le_mul h2 h3 (abs_nonneg _) hBg0) (by positivity)
                ((abs_nonneg _).trans h1)
          _ = B * Bg * ‖periodicRieszGrad d D.s z‖ := by ring
    rw [← integral_finsetSum _ (fun j _ => hint j), ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.mul_sum,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum]
  ring
