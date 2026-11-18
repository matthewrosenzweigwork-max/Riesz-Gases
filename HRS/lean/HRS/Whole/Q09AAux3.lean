import HRS.PDE.ToolboxRd.Fourier

/-!
# Packet Q09-A, part 3: weak derivatives on `ℝ^d` and their Fourier characterization

Complex-valued `L²` functions, `WD i f g` ("`g = ∂_i f` weakly", tested against Schwartz functions),
the Plancherel transform `fcL`, and the two directions of "`g = ∂_i f` iff `ĝ = 2πiξ_i f̂`".
-/
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform ComplexInnerProductSpace ContDiff

noncomputable section

namespace HRS.Whole.Q09A
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

/-- Plancherel Fourier transform of a complex `L²` function, as a function. -/
def fcL {f : Euc d → ℂ} (hf : MemLp f 2 volume) : Euc d → ℂ :=
  ⇑(FT d (hf.toLp f))

theorem fcL_memLp {f : Euc d → ℂ} (hf : MemLp f 2 volume) : MemLp (fcL hf) 2 volume :=
  Lp.memLp _

theorem pairing {f : Euc d → ℂ} (hf : MemLp f 2 volume) (ψ : SchwartzMap (Euc d) ℂ) :
    Integrable (fun ξ => fcL hf ξ * (𝓕 ψ : SchwartzMap (Euc d) ℂ) (-ξ)) volume ∧
      ∫ x, f x * ψ x = ∫ ξ, fcL hf ξ * (𝓕 ψ : SchwartzMap (Euc d) ℂ) (-ξ) := by
  set F := hf.toLp f with hF
  set g : Lp (α := Euc d) ℂ 2 := (conjSchwartz ψ).toLp 2 with hg
  have h1 : FT d g = ((𝓕 (conjSchwartz ψ) : SchwartzMap (Euc d) ℂ)).toLp 2 :=
    SchwartzMap.toLp_fourier_eq _
  have hcoe1 : (FT d g : Euc d → ℂ) =ᵐ[volume] fun ξ => conj (𝓕 ψ (-ξ)) := by
    rw [h1]
    filter_upwards [SchwartzMap.coeFn_toLp (𝓕 (conjSchwartz ψ) : SchwartzMap (Euc d) ℂ) 2 volume]
      with ξ a
    rw [a, fourier_conjSchwartz]
  have hcoe2 : (g : Euc d → ℂ) =ᵐ[volume] fun x => conj (ψ x) := by
    filter_upwards [SchwartzMap.coeFn_toLp (conjSchwartz ψ) 2 volume] with x a
    rw [hg, a]; rfl
  have hFc : (F : Euc d → ℂ) =ᵐ[volume] f := hf.coeFn_toLp
  have hinner := inner_FT g F
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def] at hinner
  constructor
  · have := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (FT d g) (FT d F)
    refine this.congr ?_
    filter_upwards [hcoe1] with ξ a
    simp only [a, fcL, RCLike.inner_apply, Complex.conj_conj]
    ring
  · have e1 : ∫ x, f x * ψ x = ∫ a, ⟪(g : Euc d → ℂ) a, (F : Euc d → ℂ) a⟫ := by
      refine integral_congr_ae ?_
      filter_upwards [hcoe2, hFc] with x h2 h3
      simp [h2, h3, RCLike.inner_apply]
    have e2 : ∫ ξ, fcL hf ξ * (𝓕 ψ : SchwartzMap (Euc d) ℂ) (-ξ) =
        ∫ a, ⟪(FT d g : Euc d → ℂ) a, (FT d F : Euc d → ℂ) a⟫ := by
      refine integral_congr_ae ?_
      filter_upwards [hcoe1] with ξ a
      simp only [a, fcL, RCLike.inner_apply, Complex.conj_conj]
      ring
    rw [e1, e2, hinner]

open LineDeriv in
theorem fourier_lineDeriv_apply (ψ : SchwartzMap (Euc d) ℂ) (i : Fin d) (ξ : Euc d) :
    (𝓕 (∂_{(EuclideanSpace.single i (1 : ℝ) : Euc d)} ψ) : SchwartzMap (Euc d) ℂ) ξ =
      (2 * Real.pi * Complex.I * (ξ i : ℂ)) * (𝓕 ψ : SchwartzMap (Euc d) ℂ) ξ := by
  have := SchwartzMap.fourier_lineDerivOp_eq ψ (EuclideanSpace.single i (1 : ℝ) : Euc d)
  have hg : (fun ξ : Euc d => inner ℝ ξ (EuclideanSpace.single i (1 : ℝ) : Euc d)).HasTemperateGrowth :=
    ((innerSL ℝ).flip (EuclideanSpace.single i (1 : ℝ) : Euc d)).hasTemperateGrowth
  rw [this]
  rw [SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg]
  simp [EuclideanSpace.inner_single_right, smul_eq_mul, mul_assoc]

open LineDeriv

/-- `g` is the weak derivative `∂_i f` of `f` (both in `L²`), tested against Schwartz functions. -/
def WD (i : Fin d) (f g : Euc d → ℂ) : Prop :=
  MemLp f 2 volume ∧ MemLp g 2 volume ∧ ∀ ψ : SchwartzMap (Euc d) ℂ,
    ∫ x, g x * ψ x = -∫ x, f x * (∂_{(EuclideanSpace.single i (1 : ℝ) : Euc d)} ψ) x

theorem WD.fourier {i : Fin d} {f g : Euc d → ℂ} (h : WD i f g) :
    fcL h.2.1 =ᵐ[volume] fun ξ => (2 * Real.pi * Complex.I * (ξ i : ℂ)) * fcL h.1 ξ := by
  obtain ⟨hf, hg, hw⟩ := h
  set Δ : Euc d → ℂ := fun ξ => fcL hg ξ - (2 * Real.pi * Complex.I * (ξ i : ℂ)) * fcL hf ξ with hΔ
  have hloc : LocallyIntegrable Δ volume := by
    refine ((fcL_memLp hg).locallyIntegrable (by norm_num)).sub ?_
    have h1 : LocallyIntegrable (fcL hf) volume := (fcL_memLp hf).locallyIntegrable (by norm_num)
    have hc : Continuous fun ξ : Euc d => (2 * Real.pi * Complex.I * (ξ i : ℂ)) := by fun_prop
    exact h1.continuous_mul hc
  have key := ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume) hloc ?_
  · filter_upwards [key] with ξ hξ
    simpa [hΔ, sub_eq_zero] using hξ
  · intro Ψ hΨ hΨc
    set Φc : Euc d → ℂ := fun ξ => ((Ψ (-ξ) : ℝ) : ℂ) with hΦc_def
    have hΦs : ContDiff ℝ ∞ Φc := Complex.ofRealCLM.contDiff.comp (hΨ.comp contDiff_neg)
    have hΦc : HasCompactSupport Φc :=
      (hΨc.comp_homeomorph (Homeomorph.neg (Euc d))).comp_left (g := ((↑) : ℝ → ℂ)) (by simp)
    let Φ : SchwartzMap (Euc d) ℂ := hΦc.toSchwartzMap hΦs
    let ψ : SchwartzMap (Euc d) ℂ := 𝓕⁻ Φ
    have hψ : (𝓕 ψ : SchwartzMap (Euc d) ℂ) = Φ := FourierInvPair.fourier_fourierInv_eq Φ
    have hF1 : ∀ ξ : Euc d, (𝓕 ψ : SchwartzMap (Euc d) ℂ) (-ξ) = ((Ψ ξ : ℝ) : ℂ) := by
      intro ξ; rw [hψ]; simp [Φ, Φc]
    obtain ⟨i1, e1⟩ := pairing hg ψ
    obtain ⟨i2, e2⟩ := pairing hf (∂_{(EuclideanSpace.single i (1 : ℝ) : Euc d)} ψ)
    have hF2 : ∀ ξ : Euc d, (𝓕 (∂_{(EuclideanSpace.single i (1 : ℝ) : Euc d)} ψ) :
        SchwartzMap (Euc d) ℂ) (-ξ) = -(2 * Real.pi * Complex.I * (ξ i : ℂ)) * ((Ψ ξ : ℝ) : ℂ) := by
      intro ξ
      rw [fourier_lineDeriv_apply, hF1]
      simp [mul_assoc]
    simp_rw [hF1] at i1 e1
    simp_rw [hF2] at i2 e2
    have e3 := hw ψ
    rw [e1, e2] at e3
    have e4 : ∫ ξ, fcL hf ξ * (-(2 * Real.pi * Complex.I * (ξ i : ℂ)) * ((Ψ ξ : ℝ) : ℂ)) =
        -∫ ξ, ((Ψ ξ : ℝ) : ℂ) * ((2 * Real.pi * Complex.I * (ξ i : ℂ)) * fcL hf ξ) := by
      rw [← integral_neg]; congr 1; ext ξ; ring
    have i3 : Integrable (fun ξ => ((Ψ ξ : ℝ) : ℂ) * ((2 * Real.pi * Complex.I * (ξ i : ℂ)) *
        fcL hf ξ)) volume := by
      have := i2.neg
      refine this.congr (Eventually.of_forall fun ξ => ?_)
      simp only [Pi.neg_apply]; ring
    have i4 : Integrable (fun ξ => ((Ψ ξ : ℝ) : ℂ) * fcL hg ξ) volume := by
      refine i1.congr (Eventually.of_forall fun ξ => ?_); simp only; ring
    have e5 : ∫ ξ, fcL hg ξ * ((Ψ ξ : ℝ) : ℂ) = ∫ ξ, ((Ψ ξ : ℝ) : ℂ) * ((2 * Real.pi * Complex.I * (ξ i : ℂ)) * fcL hf ξ) := by
      rw [e4] at e3
      linear_combination e3
    simp only [hΔ, Complex.real_smul, mul_sub]
    rw [integral_sub i4 i3, ← e5]
    have : ∫ ξ, ((Ψ ξ : ℝ) : ℂ) * fcL hg ξ = ∫ ξ, fcL hg ξ * ((Ψ ξ : ℝ) : ℂ) := by
      congr 1; ext ξ; ring
    rw [this]; ring

theorem exists_WD {f : Euc d → ℂ} (hf : MemLp f 2 volume) (i : Fin d)
    (hΞ : MemLp (fun ξ : Euc d => (ξ i : ℂ) * fcL hf ξ) 2 volume) :
    ∃ (g : Euc d → ℂ) (hg : MemLp g 2 volume), WD i f g ∧
      fcL hg =ᵐ[volume] fun ξ => (2 * Real.pi * Complex.I * (ξ i : ℂ)) * fcL hf ξ := by
  set Ξ : Euc d → ℂ := fun ξ => (2 * Real.pi * Complex.I * (ξ i : ℂ)) * fcL hf ξ with hΞdef
  have hΞ2 : MemLp Ξ 2 volume := by
    have := hΞ.const_mul (2 * Real.pi * Complex.I)
    refine this.ae_eq (Eventually.of_forall fun ξ => ?_)
    simp only [hΞdef]; ring
  set gL : Lp (α := Euc d) ℂ 2 := (FT d).symm (hΞ2.toLp Ξ) with hgL
  have hg : MemLp (⇑gL : Euc d → ℂ) 2 volume := Lp.memLp gL
  have hgfc : fcL hg =ᵐ[volume] Ξ := by
    have : hg.toLp (⇑gL) = gL := Lp.toLp_coeFn gL hg
    unfold fcL
    rw [this, hgL, LinearIsometryEquiv.apply_symm_apply]
    exact hΞ2.coeFn_toLp
  refine ⟨⇑gL, hg, ⟨hf, hg, fun ψ => ?_⟩, hgfc⟩
  obtain ⟨-, e1⟩ := pairing hg ψ
  obtain ⟨-, e2⟩ := pairing hf (∂_{(EuclideanSpace.single i (1 : ℝ) : Euc d)} ψ)
  rw [e1, e2]
  simp_rw [fourier_lineDeriv_apply]
  rw [← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [hgfc] with ξ hξ
  rw [hξ]
  simp only [hΞdef, neg_mul, mul_neg, neg_neg, Pi.neg_apply]
  have : (-ξ) i = -ξ i := rfl
  simp only [this]
  push_cast
  ring

theorem integral_norm_sq_fcL {f : Euc d → ℂ} (hf : MemLp f 2 volume) :
    ∫ ξ, ‖fcL hf ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  set F := hf.toLp f with hF
  have h := inner_FT F F
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def] at h
  have hFc : (F : Euc d → ℂ) =ᵐ[volume] f := hf.coeFn_toLp
  have e1 : ∀ (u : Euc d → ℂ), ∫ a, ⟪u a, u a⟫ = ((∫ a, ‖u a‖ ^ 2 : ℝ) : ℂ) := by
    intro u
    rw [← integral_complex_ofReal (μ := volume) (f := fun a => ‖u a‖ ^ 2)]
    congr 1; ext a
    simp [RCLike.inner_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have e2 : ∫ a, ⟪(F : Euc d → ℂ) a, (F : Euc d → ℂ) a⟫ = ((∫ x, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    rw [e1]
    have : ∫ a, ‖(F : Euc d → ℂ) a‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
      refine integral_congr_ae ?_
      filter_upwards [hFc] with x hx
      rw [hx]
    rw [this]
  have e3 := e1 (FT d F : Euc d → ℂ)
  rw [e3, e2] at h
  exact_mod_cast h
end HRS.Whole.Q09A
