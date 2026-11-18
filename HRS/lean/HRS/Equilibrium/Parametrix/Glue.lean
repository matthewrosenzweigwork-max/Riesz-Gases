import HRS.Equilibrium.Parametrix.Packets
import HRS.Equilibrium.Parametrix.PXSAuxGlue
import HRS.Equilibrium.Parametrix.PXSAuxCoef
import HRS.Equilibrium.Parametrix.PXSAuxJpair

/-!
# Prop 4.13 (`pair_poisson`): glue lemmas for the global step (packet PARX-PLAN)

Small lemmas turning the gap lemma `parx_gap` and the pair inverse `PairInverseSpec` into
`pair_poisson`: monotonicity of `posSeminorm`, stability of `PsiSize` under adding a `C²` kernel,
the convention bridge `projGen = centeredGen`, the bounds on `Jpair` and `a_f` for smooth data.
Proved: `posSeminorm_mono'`, `PsiSize.add_ck2`, `PsiSize.mono`, `projGen_eq_centeredGen`, `jpair_smooth`,
`aCoef_bound` (helpers in `PXSAux*.lean`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ} {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ}

theorem posSeminorm_mono' {K K' : ℕ} (h : K ≤ K') (f : Torus d → ℝ) :
    posSeminorm K f ≤ posSeminorm K' f := by
  unfold posSeminorm
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
  intro j hj
  rw [Finset.mem_Icc] at hj ⊢
  exact ⟨hj.1, hj.2.trans h⟩

theorem rTrunc_nonneg' (x y : Torus d) : 0 ≤ rTrunc x y :=
  le_min zero_le_one (Real.sqrt_nonneg _)

theorem isOpen_offDiag' (d : ℕ) : IsOpen (offDiag d) := by
  have hc : Continuous fun p : Euc d × Euc d => (Torus.mk p.1, Torus.mk p.2) := by
    have := (Torus.continuous_mk (d := d))
    exact (this.comp continuous_fst).prodMk (this.comp continuous_snd)
  have ho : IsOpen {q : Torus d × Torus d | q.1 ≠ q.2} := isOpen_ne_fun continuous_fst continuous_snd
  exact ho.preimage hc

theorem abs_le_cbNorm2 {Ψ : Torus d → Torus d → ℝ} (hΨ : PDE.IsCk2 2 Ψ) (x y : Torus d) :
    |Ψ x y| ≤ PDE.cbNorm2 2 Ψ := by
  have h := PDE.MFPair.norm_iteratedFDeriv_le_cbNorm2 hΨ (i := 0) (by norm_num)
    (Torus.rep x, Torus.rep y)
  rw [norm_iteratedFDeriv_zero] at h
  simpa [PDE.lift2, Torus.mk_rep] using h

/-- `PsiSize` is stable under adding a `C²` kernel (with the constant increased by its `C²` norm);
the `C^∞` field is supplied separately (it is the smoothness bootstrap `parx_psi_smooth`). -/
theorem PsiSize.add_ck2 {K₁ M : ℝ} {Φ Ψ : Torus d → Torus d → ℝ} (hΦ : PsiSize s K₁ Φ)
    (hΨ : PDE.IsCk2 2 Ψ) (hM : PDE.cbNorm2 2 Ψ ≤ M)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 (fun x y => Φ x y + Ψ x y)) (offDiag d)) :
    PsiSize s (K₁ + M) (fun x y => Φ x y + Ψ x y) := by
  have hM0 : 0 ≤ M := (PDE.MFPair.cbNorm2_nonneg 2 Ψ).trans hM
  have hsum : lift2 (fun x y => Φ x y + Ψ x y) = lift2 Φ + lift2 Ψ := rfl
  have hΨc : ContDiff ℝ 2 (lift2 Ψ) := hΨ
  refine ⟨hsm, ?_, ?_, ?_⟩
  · intro x y hxy
    have h1 := hΦ.size x y hxy
    have h2 := abs_le_cbNorm2 hΨ x y
    set W : ℝ := 1 + rTrunc x y ^ (2 - s) +
      (if s = 2 then |Real.log (rTrunc x y)| else 0) with hW
    have hW1 : 1 ≤ W := by
      have h3 : 0 ≤ rTrunc x y ^ (2 - s) := Real.rpow_nonneg (rTrunc_nonneg' x y) _
      have h4 : 0 ≤ (if s = 2 then |Real.log (rTrunc x y)| else (0 : ℝ)) := by
        split_ifs <;> positivity
      linarith
    calc |Φ x y + Ψ x y| ≤ |Φ x y| + |Ψ x y| := abs_add_le _ _
      _ ≤ K₁ * W + M := add_le_add h1 (h2.trans hM)
      _ ≤ (K₁ + M) * W := by nlinarith
  · intro p hp
    have hd1 : DifferentiableAt ℝ (lift2 Φ) p :=
      ((hΦ.smooth.contDiffAt ((isOpen_offDiag' d).mem_nhds hp)).differentiableAt (by simp))
    have hd2 : DifferentiableAt ℝ (lift2 Ψ) p := hΨc.differentiable (by norm_num) p
    have h1 := hΦ.grad p hp
    have h2 : ‖fderiv ℝ (lift2 Ψ) p‖ ≤ M := by
      have : ‖iteratedFDeriv ℝ 1 (lift2 Ψ) p‖ ≤ PDE.cbNorm2 2 Ψ :=
        PDE.MFPair.norm_iteratedFDeriv_le_cbNorm2 hΨ (i := 1) (by norm_num) p
      have e : ‖fderiv ℝ (lift2 Ψ) p‖ = ‖iteratedFDeriv ℝ 1 (lift2 Ψ) p‖ := by
        have := (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := lift2 Ψ) (x := p) (n := 0))
        rw [norm_iteratedFDeriv_zero] at this
        exact this
      linarith [hM]
    have hr : 0 ≤ rTrunc (Torus.mk p.1) (Torus.mk p.2) ^ (1 - s) :=
      Real.rpow_nonneg (rTrunc_nonneg' _ _) _
    rw [hsum, fderiv_add hd1 hd2]
    calc ‖fderiv ℝ (lift2 Φ) p + fderiv ℝ (lift2 Ψ) p‖
        ≤ ‖fderiv ℝ (lift2 Φ) p‖ + ‖fderiv ℝ (lift2 Ψ) p‖ := norm_add_le _ _
      _ ≤ K₁ * (1 + rTrunc (Torus.mk p.1) (Torus.mk p.2) ^ (1 - s)) + M := add_le_add h1 h2
      _ ≤ (K₁ + M) * (1 + rTrunc (Torus.mk p.1) (Torus.mk p.2) ^ (1 - s)) := by nlinarith
  · intro p hp
    have hc1 : ContDiffAt ℝ 2 (lift2 Φ) p :=
      (hΦ.smooth.contDiffAt ((isOpen_offDiag' d).mem_nhds hp)).of_le
        (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from WithTop.coe_le_coe.mpr le_top)
    have hc2 : ContDiffAt ℝ 2 (lift2 Ψ) p := hΨc.contDiffAt
    have h1 := hΦ.hess p hp
    have h2 : ‖iteratedFDeriv ℝ 2 (lift2 Ψ) p‖ ≤ M :=
      (PDE.MFPair.norm_iteratedFDeriv_le_cbNorm2 hΨ (i := 2) le_rfl p).trans hM
    have hr : 0 ≤ rTrunc (Torus.mk p.1) (Torus.mk p.2) ^ (-s) :=
      Real.rpow_nonneg (rTrunc_nonneg' _ _) _
    rw [hsum, iteratedFDeriv_add_apply hc1 hc2]
    calc ‖iteratedFDeriv ℝ 2 (lift2 Φ) p + iteratedFDeriv ℝ 2 (lift2 Ψ) p‖
        ≤ ‖iteratedFDeriv ℝ 2 (lift2 Φ) p‖ + ‖iteratedFDeriv ℝ 2 (lift2 Ψ) p‖ := norm_add_le _ _
      _ ≤ K₁ * (1 + rTrunc (Torus.mk p.1) (Torus.mk p.2) ^ (-s)) + M := add_le_add h1 h2
      _ ≤ (K₁ + M) * (1 + rTrunc (Torus.mk p.1) (Torus.mk p.2) ^ (-s)) := by nlinarith

theorem PsiSize.mono {K₁ K₂ : ℝ} {ψ : Torus d → Torus d → ℝ} (h : PsiSize s K₁ ψ) (hK : K₁ ≤ K₂) :
    PsiSize s K₂ ψ := by
  refine ⟨h.smooth, fun x y hxy => ?_, fun p hp => ?_, fun p hp => ?_⟩
  · have h1 := h.size x y hxy
    have hW : 0 ≤ 1 + rTrunc x y ^ (2 - s) + (if s = 2 then |Real.log (rTrunc x y)| else 0) := by
      have h3 : 0 ≤ rTrunc x y ^ (2 - s) := Real.rpow_nonneg (rTrunc_nonneg' x y) _
      have h4 : 0 ≤ (if s = 2 then |Real.log (rTrunc x y)| else (0 : ℝ)) := by
        split_ifs <;> positivity
      linarith
    exact h1.trans (mul_le_mul_of_nonneg_right hK hW)
  · have hr : 0 ≤ 1 + rTrunc (Torus.mk p.1) (Torus.mk p.2) ^ (1 - s) := by
      have := Real.rpow_nonneg (rTrunc_nonneg' (Torus.mk p.1) (Torus.mk p.2)) (1 - s); linarith
    exact (h.grad p hp).trans (mul_le_mul_of_nonneg_right hK hr)
  · have hr : 0 ≤ 1 + rTrunc (Torus.mk p.1) (Torus.mk p.2) ^ (-s) := by
      have := Real.rpow_nonneg (rTrunc_nonneg' (Torus.mk p.1) (Torus.mk p.2)) (-s); linarith
    exact (h.hess p hp).trans (mul_le_mul_of_nonneg_right hK hr)

/-- The convention bridge (source lines 4709-4715 with `convGradConv_coeff`): for `C²` `f`, the
`PairCorrection` generator `projGen = P_μ[Bf + Jf]` (`forceField = ∇(g*μ)`,
`Jop = ∑_j ∂_j[g*(ρ∂_jf)]`) equals the generator `centeredGen = P_μ 𝓛f` of the PDE layer
(`backwardGenerator`, cancellation convention).  Proof: `Bop + Jop = backwardGenerator` pointwise for
`M = -I` once `∇(g*ρ) = ∇g * ρ` and `∂_j(g*h) = (∂_jg)*h` (Fourier coefficients of continuous
functions: `convGradConv_coeff`, `convGradConv_continuous`, `convFun_isCk_one`,
`convFun_partialDeriv`). -/
theorem projGen_eq_centeredGen (H : ParxHyp d s V β ρ) (f : Torus d → ℝ) (hf : Torus.IsCk 2 f) :
    projGen d s V β ρ f = PDE.centeredGen H.dyn ρ f :=
  pxS_projGen_eq_centeredGen H f hf

/-- `𝒥Ψ = (P_xJ_x + P_yJ_y)Ψ` of a doubly centred `C²` kernel is canonical and bounded by
`CJ ‖Ψ‖_{C²}`: `|Jop f| ≤ ‖g‖_{L¹} ‖ρ∂f‖_{C¹}`; canonicity by `∫_y J_xΨ(·,y)μ(dy) = J_x[∫Ψ(·,y)μ(dy)]
= 0` (Fubini and differentiation under the integral; `g` integrable). -/
theorem jpair_smooth (H : ParxHyp d s V β ρ) :
    ∃ CJ : ℝ, 0 ≤ CJ ∧ ∀ Ψ : Torus d → Torus d → ℝ, PDE.IsCk2 2 Ψ →
      PDE.DoublyCentered (withDensityReal ρ) Ψ →
        IsCanonicalPair (withDensityReal ρ) (Jpair d s ρ Ψ) ∧
        ∀ x y, |Jpair d s ρ Ψ x y| ≤ CJ * PDE.cbNorm2 2 Ψ :=
  pxS_jpair_smooth H

/-- `a_f` is bounded by `Ca |f|_2`: `|h_f(x,y)| ≤ ‖D²f‖_∞ r |∇g(r)| ≤ C ‖D²f‖(r^{-s} + r)`, `ρ`
bounded and `r^{-s}` integrable (`s < d`). -/
theorem aCoef_bound (H : ParxHyp d s V β ρ) :
    ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ f : Torus d → ℝ, Torus.IsSmooth f →
      AEStronglyMeasurable (aCoef d s ρ f) (withDensityReal ρ) ∧
      ∀ x, |aCoef d s ρ f x| ≤ Ca * posSeminorm 2 f :=
  pxS_aCoef_bound H

end HRS.Parx

end
