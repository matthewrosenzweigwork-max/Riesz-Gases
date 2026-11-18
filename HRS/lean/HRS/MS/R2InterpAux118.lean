import HRS.MS.R2InterpAux110
import HRS.MS.MainRdFieldAux3
import HRS.MS.R2WfmAux3
import HRS.MS.SuppU15Aux2

/-!
# S10.2 (worker S10R), part 118 (packet M1c): the pointwise envelope of the commutator kernel of a weighted test

For `f ∈ C^r` with finite `weightedSobolevE r Pw f` (`d/2 + 2 < r`):
`|(∇f(x) - ∇f(y))·∇g(x-y)| ≤ c₁ ‖f‖_{E_{r,P}} (⟨x⟩+⟨y⟩)^P (1 + W_s(x-y))`, `x ≠ y` (the "direct bound" (ii) of the M1 packet), with `c₁ = c₁(d,s,P,r)`.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d : ℕ}

/-- Lipschitz bound of the gradient along a segment from the entrywise bound of the second derivatives on the segment. -/
theorem s102_grad_lip_seg {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) {B : ℝ} (x y : Euc d)
    (hB : ∀ (i : Fin 2 → Fin d), ∀ z ∈ segment ℝ x y, |HRS.Whole.partialDeriv i f z| ≤ B) :
    ‖gradient f x - gradient f y‖ ≤ (d * d * B) * ‖x - y‖ := by
  have hfd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hgb : ∀ b : Fin d, |fderiv ℝ f x (EuclideanSpace.single b 1) - fderiv ℝ f y (EuclideanSpace.single b 1)| ≤
        (d * B) * ‖x - y‖ := by
    intro b
    set g : Euc d → ℝ := fun z => fderiv ℝ f z (EuclideanSpace.single b 1) with hg
    have hgd : Differentiable ℝ g := fun z => (hfd z).clm_apply (differentiableAt_const _)
    have hbound : ∀ z ∈ segment ℝ x y, ‖fderiv ℝ g z‖ ≤ d * B := by
      intro z hz
      refine (HRS.MS.MainRdField.sa6_clm_norm_le_sum _).trans ?_
      have h1 : fderiv ℝ g z = (fderiv ℝ (fderiv ℝ f) z).flip (EuclideanSpace.single b 1) := by
        simp only [hg]
        rw [fderiv_clm_apply (hfd z) (differentiableAt_const _)]
        simp
      have e : ∀ a : Fin d, fderiv ℝ g z (EuclideanSpace.single a 1) =
          HRS.Whole.partialDeriv (![a, b]) f z := by
        intro a
        rw [h1]
        unfold partialDeriv
        rw [iteratedFDeriv_two_apply]
        simp
      calc ∑ a, |fderiv ℝ g z (EuclideanSpace.single a 1)| ≤ ∑ _a : Fin d, B :=
            Finset.sum_le_sum fun a _ => by rw [e a]; exact hB _ z hz
        _ = d * B := by simp
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (f := g) (fun z _ => hgd z) hbound
      (convex_segment x y) (right_mem_segment ℝ x y) (left_mem_segment ℝ x y)
    simpa [Real.norm_eq_abs, hg] using h
  refine (HRS.MS.SuppU15.u15_norm_le_sum _).trans ?_
  calc ∑ b, |(gradient f x - gradient f y) b| ≤ ∑ _b : Fin d, (d * B) * ‖x - y‖ := by
        refine Finset.sum_le_sum fun b _ => ?_
        have : (gradient f x - gradient f y) b = fderiv ℝ f x (EuclideanSpace.single b 1) -
            fderiv ℝ f y (EuclideanSpace.single b 1) := by
          simp only [PiLp.sub_apply]
          rw [HRS.MP.RdMart.mrm_grad_component, HRS.MP.RdMart.mrm_grad_component]
        rw [this]; exact hgb b
    _ = (d * d * B) * ‖x - y‖ := by simp [mul_assoc]

theorem s102_jb_segment {x y z : Euc d} (hz : z ∈ segment ℝ x y) (P : ℝ) (hP : 0 ≤ P) :
    jbracket z ^ P ≤ (jbracket x + jbracket y) ^ P := by
  have hjx : 0 ≤ jbracket x := by unfold jbracket; positivity
  have hjy : 0 ≤ jbracket y := by unfold jbracket; positivity
  have hjz : 0 ≤ jbracket z := by unfold jbracket; positivity
  have hnorm : ‖z‖ ≤ max ‖x‖ ‖y‖ := by
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
    calc ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * max ‖x‖ ‖y‖ + b * max ‖x‖ ‖y‖ := by
          gcongr <;> simp
      _ = max ‖x‖ ‖y‖ := by rw [← add_mul, hab, one_mul]
  have hjz' : jbracket z ≤ jbracket x + jbracket y := by
    unfold jbracket at *
    rcases le_total ‖x‖ ‖y‖ with h | h
    · rw [max_eq_right h] at hnorm
      have : Real.sqrt (1 + ‖z‖ ^ 2) ≤ Real.sqrt (1 + ‖y‖ ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [norm_nonneg z, norm_nonneg y])
      linarith [Real.sqrt_nonneg (1 + ‖x‖ ^ 2)]
    · rw [max_eq_left h] at hnorm
      have : Real.sqrt (1 + ‖z‖ ^ 2) ≤ Real.sqrt (1 + ‖x‖ ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [norm_nonneg z, norm_nonneg x])
      linarith [Real.sqrt_nonneg (1 + ‖y‖ ^ 2)]
  exact Real.rpow_le_rpow hjz hjz' hP

/-- **The direct bound of M1**: the pair kernel of a weighted test is controlled by its `E_{r,P}` norm. -/
theorem s102_comm_envelope (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) {Pw : ℝ} (hP0 : 0 ≤ Pw) (r : ℕ)
    (hr : (d : ℝ) / 2 + 2 < r) :
    ∃ c1 : ℝ, 0 ≤ c1 ∧ ∀ f : Euc d → ℝ, ContDiff ℝ r f → weightedSobolevE r Pw f < ⊤ → ∀ x y : Euc d, x ≠ y →
      |commutatorKernel d s (fun z => gradient f z) x y| ≤
        c1 * (weightedSobolevE r Pw f).toReal * (jbracket x + jbracket y) ^ Pw * (1 + rieszWeight s (x - y)) := by
  obtain ⟨C2, hC2, hemb⟩ := s102_embed_Cr hd hP0 r 2 (by simpa using hr)
  refine ⟨max s 1 * (d * d * C2), by positivity, fun f hf hE x y hxy => ?_⟩
  have hEn : 0 ≤ (weightedSobolevE r Pw f).toReal := ENNReal.toReal_nonneg
  have hjx : 0 ≤ jbracket x := by unfold jbracket; positivity
  have hjy : 0 ≤ jbracket y := by unfold jbracket; positivity
  have hq : 0 ≤ (jbracket x + jbracket y) ^ Pw := Real.rpow_nonneg (by linarith) _
  have hB : ∀ i : Fin 2 → Fin d, ∀ z ∈ segment ℝ x y,
      |HRS.Whole.partialDeriv i f z| ≤ C2 * (jbracket x + jbracket y) ^ Pw * (weightedSobolevE r Pw f).toReal := by
    intro i z hz
    have h1 := hemb i z f hf
    have hjz : 0 ≤ C2 * jbracket z ^ Pw := mul_nonneg hC2.le (Real.rpow_nonneg (by unfold jbracket; positivity) _)
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE.ne) h1
    rw [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul, ENNReal.toReal_ofReal hjz] at h2
    calc |HRS.Whole.partialDeriv i f z| ≤ C2 * jbracket z ^ Pw * (weightedSobolevE r Pw f).toReal := h2
      _ ≤ C2 * (jbracket x + jbracket y) ^ Pw * (weightedSobolevE r Pw f).toReal :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (s102_jb_segment hz Pw hP0) hC2.le) hEn
  have hlip := s102_grad_lip_seg (hf.of_le (by
      have h2 : (2 : ℝ) < r := by have : 0 ≤ (d : ℝ) / 2 := by positivity
                                  linarith
      exact_mod_cast h2.le)) x y hB
  have hΛ : 0 ≤ (d : ℝ) * d * (C2 * (jbracket x + jbracket y) ^ Pw * (weightedSobolevE r Pw f).toReal) := by positivity
  have := HRS.MS.R2Wfm.s97_comm_bound hs0 hΛ x y hxy hlip
  calc |commutatorKernel d s (fun z => gradient f z) x y|
      ≤ max s 1 * ((d : ℝ) * d * (C2 * (jbracket x + jbracket y) ^ Pw * (weightedSobolevE r Pw f).toReal)) *
        (1 + rieszWeight s (x - y)) := this
    _ = _ := by ring

end HRS.MS.R2Interp

end
