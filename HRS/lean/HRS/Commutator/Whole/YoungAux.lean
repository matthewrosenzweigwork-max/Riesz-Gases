import HRS.Commutator.Whole.Defs

/-!
# Helpers for the Bernstein inequality (packet X-BERN)

Mathlib (pin v4.34.1) has no Young inequality.  The Bernstein inequality `bernstein_Lq` is proved
without it: for `a ∈ L^p` with `supp â ⊂ B̄(0,R)` one has `a = K ⋆ a` a.e. for a Schwartz `K` with
`𝓚 K = 1` near `B̄(0,R)`, hence `‖a‖_∞ ≤ ‖K‖_{p'} ‖a‖_p` by Hölder, and `‖a‖_q ≤ ‖a‖_∞^{1-p/q}‖a‖_p^{p/q}`.

This file contains the kernel construction, the Hölder estimates, the Fubini identity and the
representation `a = K ⋆ a` a.e.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff Convolution

noncomputable section

namespace HRS.Commutator.Whole

variable {d : ℕ}

/-- A Schwartz kernel whose Fourier transform is `1` on `B(0,ρ)`. -/
lemma exists_kernel_fourier_one (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ K : SchwartzMap (Euc d) ℂ, ∀ ξ : Euc d, ‖ξ‖ < ρ → 𝓕 (⇑K) ξ = 1 := by
  let χ : ContDiffBump (0 : Euc d) := ⟨ρ, ρ + 1, hρ, by linarith⟩
  have hc : HasCompactSupport (fun ξ : Euc d => ((χ ξ : ℝ) : ℂ)) := by
    have := χ.hasCompactSupport
    exact this.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have hs : ContDiff ℝ ∞ (fun ξ : Euc d => ((χ ξ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp χ.contDiff
  let Xc : SchwartzMap (Euc d) ℂ := hc.toSchwartzMap hs
  let KS : SchwartzMap (Euc d) ℂ := 𝓕⁻ Xc
  refine ⟨KS, fun ξ hξ => ?_⟩
  have h1 : 𝓕 (⇑KS) = ⇑Xc := by
    rw [← SchwartzMap.fourier_coe]
    exact congrArg (⇑) (FourierInvPair.fourier_fourierInv_eq (E := SchwartzMap (Euc d) ℂ)
      (F := SchwartzMap (Euc d) ℂ) Xc)
  rw [h1]
  show ((χ ξ : ℝ) : ℂ) = 1
  rw [χ.one_of_mem_closedBall (mem_closedBall_zero_iff.2 hξ.le)]
  simp

/-- Fourier transform of the Schwartz convolution. -/
lemma fourier_conv_kernel (K φ : SchwartzMap (Euc d) ℂ) (ξ : Euc d) :
    𝓕 (⇑(SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) K φ)) ξ
      = 𝓕 (⇑K) ξ * 𝓕 (⇑φ) ξ := by
  rw [← SchwartzMap.fourier_coe, SchwartzMap.fourier_convolution_apply]
  exact Real.fourier_mul_convolution_eq K.integrable φ.integrable ξ

/-- Hölder estimate with a translation: `∫⁻ ‖u(x+t) v(x)‖ ≤ ‖u‖_p ‖v‖_{p'}`. -/
lemma lintegral_holder_shift {p p' : ℝ≥0∞} [p.HolderConjugate p'] {u v : Euc d → ℂ}
    (hu : MemLp u p) (hv : MemLp v p') (t : Euc d) :
    ∫⁻ x, ‖u (x + t) * v x‖ₑ ≤ eLpNorm u p volume * eLpNorm v p' volume := by
  have hmeas : AEStronglyMeasurable (fun x => u (x + t) * v x) volume :=
    (hu.aestronglyMeasurable.comp_measurePreserving (measurePreserving_add_right volume t)).mul
      hv.aestronglyMeasurable
  have h1 : eLpNorm (fun x => u (x + t)) p volume = eLpNorm u p volume :=
    eLpNorm_comp_measurePreserving hu.aestronglyMeasurable (measurePreserving_add_right volume t)
  have hm1 : AEStronglyMeasurable (fun x => u (x + t)) volume :=
    hu.aestronglyMeasurable.comp_measurePreserving (measurePreserving_add_right volume t)
  have h2 := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (μ := volume) (p := p) (q := p')
    (r := 1) (fun x y : ℂ => x * y) (1 : NNReal) (continuous_mul) hm1 hv.aestronglyMeasurable
    (Eventually.of_forall fun x => by simp [nnnorm_mul])
  rw [← eLpNorm_one_eq_lintegral_enorm hmeas]
  rw [h1] at h2
  simpa using h2

/-- Translation of the integral variable. -/
lemma lintegral_shift_eq (u v : Euc d → ℂ) (t : Euc d) :
    ∫⁻ x, ‖u x * v (x - t)‖ₑ = ∫⁻ x, ‖u (x + t) * v x‖ₑ := by
  rw [← lintegral_add_right_eq_self (fun x => ‖u x * v (x - t)‖ₑ) t]
  simp

/-- Integrability of `(x,t) ↦ a x * (K t * φ (x - t))`. -/
lemma integrable_pairing_left {p p' : ℝ≥0∞} [p.HolderConjugate p'] {a : Euc d → ℂ}
    (ha : MemLp a p volume) (K φ : SchwartzMap (Euc d) ℂ) :
    Integrable (Function.uncurry fun x t : Euc d => a x * (K t * φ (x - t)))
      (volume.prod volume) := by
  have hφ : MemLp φ p' volume := φ.memLp p'
  have hmeas : AEStronglyMeasurable (Function.uncurry fun x t : Euc d => a x * (K t * φ (x - t)))
      (volume.prod volume) := by
    apply AEStronglyMeasurable.mul
    · exact ha.aestronglyMeasurable.comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_fst
    · apply Continuous.aestronglyMeasurable
      exact (K.continuous.comp continuous_snd).mul
        (φ.continuous.comp (continuous_fst.sub continuous_snd))
  refine ⟨hmeas, ?_⟩
  unfold HasFiniteIntegral
  have hm2 : AEMeasurable (fun z : Euc d × Euc d =>
      ‖(Function.uncurry fun x t : Euc d => a x * (K t * φ (x - t))) z‖ₑ) (volume.prod volume) :=
    hmeas.enorm
  rw [lintegral_prod_symm _ hm2]
  have hfin : eLpNorm a p volume * eLpNorm φ p' volume < ⊤ :=
    ENNReal.mul_lt_top ha.eLpNorm_lt_top hφ.eLpNorm_lt_top
  calc ∫⁻ t, ∫⁻ x, ‖(Function.uncurry fun x t : Euc d => a x * (K t * φ (x - t))) (x, t)‖ₑ
      ≤ ∫⁻ t, ‖K t‖ₑ * (eLpNorm a p volume * eLpNorm φ p' volume) := by
        refine lintegral_mono fun t => ?_
        have h : ∀ x : Euc d, ‖(Function.uncurry fun x t : Euc d => a x * (K t * φ (x - t))) (x, t)‖ₑ
            = ‖K t‖ₑ * ‖a x * φ (x - t)‖ₑ := by
          intro x
          simp only [Function.uncurry_apply_pair]
          rw [show a x * (K t * φ (x - t)) = K t * (a x * φ (x - t)) by ring, enorm_mul]
        simp_rw [h]
        rw [lintegral_const_mul' _ _ (enorm_ne_top)]
        rw [lintegral_shift_eq]
        gcongr
        exact lintegral_holder_shift ha hφ t
    _ = (∫⁻ t, ‖K t‖ₑ) * (eLpNorm a p volume * eLpNorm φ p' volume) :=
        lintegral_mul_const' _ _ (by finiteness)
    _ < ⊤ := ENNReal.mul_lt_top K.integrable.2 hfin

/-- Fourier transform of the test function `φ - K ⋆ φ`. -/
lemma fourier_test_sub (K φ : SchwartzMap (Euc d) ℂ) (ξ : Euc d) :
    𝓕 (⇑(φ - SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) K φ)) ξ
      = (1 - 𝓕 (⇑K) ξ) * 𝓕 (⇑φ) ξ := by
  rw [← SchwartzMap.fourier_coe, sub_eq_add_neg, FourierAdd.fourier_add,
    FourierTransform.fourier_neg, add_apply, neg_apply,
    SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, fourier_conv_kernel]
  ring

/-- Integrability of `(t,y) ↦ K t * (a (y + t) * φ y)`. -/
lemma integrable_pairing_right {p p' : ℝ≥0∞} [p.HolderConjugate p'] {a : Euc d → ℂ}
    (ha : MemLp a p volume) (K φ : SchwartzMap (Euc d) ℂ) :
    Integrable (Function.uncurry fun t y : Euc d => K t * (a (y + t) * φ y))
      (volume.prod volume) := by
  have hφ : MemLp φ p' volume := φ.memLp p'
  have hsh : AEStronglyMeasurable (fun z : Euc d × Euc d => a (z.2 + z.1)) (volume.prod volume) :=
    ha.aestronglyMeasurable.comp_quasiMeasurePreserving (quasiMeasurePreserving_add_swap volume volume)
  have hmeas : AEStronglyMeasurable (Function.uncurry fun t y : Euc d => K t * (a (y + t) * φ y))
      (volume.prod volume) := by
    apply AEStronglyMeasurable.mul
    · exact (K.continuous.comp continuous_fst).aestronglyMeasurable
    · exact hsh.mul (Continuous.aestronglyMeasurable (φ.continuous.comp continuous_snd))
  refine ⟨hmeas, ?_⟩
  unfold HasFiniteIntegral
  rw [lintegral_prod _ hmeas.enorm]
  have hfin : eLpNorm a p volume * eLpNorm φ p' volume < ⊤ :=
    ENNReal.mul_lt_top ha.eLpNorm_lt_top hφ.eLpNorm_lt_top
  calc ∫⁻ t, ∫⁻ y, ‖(Function.uncurry fun t y : Euc d => K t * (a (y + t) * φ y)) (t, y)‖ₑ
      ≤ ∫⁻ t, ‖K t‖ₑ * (eLpNorm a p volume * eLpNorm φ p' volume) := by
        refine lintegral_mono fun t => ?_
        have h : ∀ y : Euc d, ‖(Function.uncurry fun t y : Euc d => K t * (a (y + t) * φ y)) (t, y)‖ₑ
            = ‖K t‖ₑ * ‖a (y + t) * φ y‖ₑ := fun y => by
          simp only [Function.uncurry_apply_pair]
          rw [enorm_mul]
        simp_rw [h]
        rw [lintegral_const_mul' _ _ enorm_ne_top]
        gcongr
        exact lintegral_holder_shift ha hφ t
    _ = (∫⁻ t, ‖K t‖ₑ) * (eLpNorm a p volume * eLpNorm φ p' volume) :=
        lintegral_mul_const' _ _ (by finiteness)
    _ < ⊤ := ENNReal.mul_lt_top K.integrable.2 hfin

/-- Fubini identity: `∫ a (K ⋆ φ) = ∫ φ · (a ⋆ K)`, where `(a ⋆ K)(y) = ∫ K t a(y+t) dt`. -/
lemma pairing_identity {p p' : ℝ≥0∞} [p.HolderConjugate p'] {a : Euc d → ℂ}
    (ha : MemLp a p volume) (K φ : SchwartzMap (Euc d) ℂ) :
    ∫ x, a x * (∫ t, K t * φ (x - t)) = ∫ y, φ y * ∫ t, K t * a (y + t) := by
  have hI1 := integrable_pairing_left (p' := p') ha K φ
  have hI2 := integrable_pairing_right (p' := p') ha K φ
  calc ∫ x, a x * (∫ t, K t * φ (x - t))
      = ∫ x, ∫ t, a x * (K t * φ (x - t)) := by
        congr 1; ext x; rw [integral_const_mul]
    _ = ∫ t, ∫ x, a x * (K t * φ (x - t)) := integral_integral_swap hI1
    _ = ∫ t, K t * ∫ y, a (y + t) * φ y := by
        congr 1; ext t
        have h : ∀ x, a x * (K t * φ (x - t)) = K t * (a x * φ (x - t)) := fun x => by ring
        simp_rw [h]
        rw [integral_const_mul]
        congr 1
        rw [← integral_add_right_eq_self (fun x => a x * φ (x - t)) t]
        simp
    _ = ∫ t, ∫ y, K t * (a (y + t) * φ y) := by
        congr 1; ext t; rw [integral_const_mul]
    _ = ∫ y, ∫ t, K t * (a (y + t) * φ y) := integral_integral_swap hI2
    _ = ∫ y, φ y * ∫ t, K t * a (y + t) := by
        congr 1; ext y
        rw [← integral_const_mul]
        congr 1; ext t; ring


/-- Convolution with the Schwartz kernel, evaluated: `(K ⋆ φ)(x) = ∫ K t φ(x - t)`. -/
lemma conv_kernel_apply (K φ : SchwartzMap (Euc d) ℂ) (x : Euc d) :
    SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) K φ x = ∫ t, K t * φ (x - t) := by
  rw [SchwartzMap.convolution_apply, convolution_def]
  rfl

/-- Test-function identity: if `𝓕 G` vanishes near `B̄(0,R)` for `G = φ - K ⋆ φ`, then
`∫ a φ = ∫ a (K ⋆ φ)` for `a` with `supp â ⊂ B̄(0,R)`. -/
lemma fourier_supp_test {p p' : ℝ≥0∞} [p.HolderConjugate p'] {R : ℝ}
    (K : SchwartzMap (Euc d) ℂ) (hK : ∀ ξ : Euc d, ‖ξ‖ < R + 1 → 𝓕 (⇑K) ξ = 1)
    {a : Euc d → ℂ} (ha : MemLp a p volume)
    (hsupp : ∀ G : SchwartzMap (Euc d) ℂ,
      Disjoint (tsupport (𝓕 (⇑G))) (closedBall (0 : Euc d) R) → ∫ x, a x * G x = 0)
    (φ : SchwartzMap (Euc d) ℂ) :
    ∫ x, a x * φ x = ∫ x, a x * (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) K φ x) := by
  have hdisj : Disjoint
      (tsupport (𝓕 (⇑(φ - SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) K φ))))
      (closedBall (0 : Euc d) R) := by
    rw [Set.disjoint_left]
    intro ξ hξ hball
    have hsub : tsupport (𝓕 (⇑(φ - SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) K φ)))
        ⊆ {η : Euc d | R + 1 ≤ ‖η‖} := by
      apply closure_minimal _ (isClosed_le continuous_const continuous_norm)
      intro η hη
      show R + 1 ≤ ‖η‖
      by_contra h
      push Not at h
      apply Function.mem_support.1 hη
      rw [fourier_test_sub, hK η h, sub_self, zero_mul]
    have h1 : R + 1 ≤ ‖ξ‖ := hsub hξ
    have h2 := mem_closedBall_zero_iff.1 hball
    linarith
  have h0 := hsupp _ hdisj
  have hi1 : Integrable (fun x => a x * φ x) := ha.integrable_mul (φ.memLp p')
  have hi2 : Integrable (fun x => a x * (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) K φ x)) :=
    ha.integrable_mul ((SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) K φ).memLp p')
  have hsplit : ∫ x, a x * (φ - SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) K φ) x
      = (∫ x, a x * φ x) - ∫ x, a x * (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) K φ x) := by
    rw [← integral_sub hi1 hi2]
    congr 1
    ext x
    rw [sub_apply]
    ring
  rw [h0] at hsplit
  exact sub_eq_zero.1 hsplit.symm

/-- Representation `a = K ⋆ a` almost everywhere (complex version). -/
lemma ae_repr_complex {p p' : ℝ≥0∞} [p.HolderConjugate p'] (hp : 1 ≤ p) {R : ℝ}
    (K : SchwartzMap (Euc d) ℂ) (hK : ∀ ξ : Euc d, ‖ξ‖ < R + 1 → 𝓕 (⇑K) ξ = 1)
    {a : Euc d → ℂ} (ha : MemLp a p volume)
    (hsupp : ∀ G : SchwartzMap (Euc d) ℂ,
      Disjoint (tsupport (𝓕 (⇑G))) (closedBall (0 : Euc d) R) → ∫ x, a x * G x = 0) :
    ∀ᵐ y ∂volume, a y = ∫ t, K t * a (y + t) := by
  have hMtop : eLpNorm a p volume * eLpNorm K p' volume ≠ ⊤ :=
    (ENNReal.mul_lt_top ha.eLpNorm_lt_top (K.memLp p').eLpNorm_lt_top).ne
  have hTb : ∀ y : Euc d, ‖∫ t, K t * a (y + t)‖ₑ ≤ eLpNorm a p volume * eLpNorm K p' volume := by
    intro y
    calc ‖∫ t, K t * a (y + t)‖ₑ ≤ ∫⁻ t, ‖K t * a (y + t)‖ₑ := enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ t, ‖a (t + y) * K t‖ₑ := by
          apply lintegral_congr
          intro t
          rw [add_comm y t, mul_comm (K t)]
      _ ≤ eLpNorm a p volume * eLpNorm K p' volume :=
          lintegral_holder_shift ha (K.memLp p') y
  have hTm : AEStronglyMeasurable (fun y : Euc d => ∫ t, K t * a (y + t)) volume := by
    have hF : AEStronglyMeasurable (fun q : Euc d × Euc d => K q.2 * a (q.1 + q.2))
        (volume.prod volume) :=
      (K.continuous.comp continuous_snd).aestronglyMeasurable.mul
        (ha.aestronglyMeasurable.comp_quasiMeasurePreserving
          (quasiMeasurePreserving_add volume volume))
    exact hF.integral_prod_right'
  have hTreal : ∀ y : Euc d, ‖∫ t, K t * a (y + t)‖ ≤
      (eLpNorm a p volume * eLpNorm K p' volume).toReal := by
    intro y
    have hy := hTb y
    rw [← ofReal_norm] at hy
    exact (ENNReal.ofReal_le_iff_le_toReal hMtop).1 hy
  have hTbd : MemLp (fun y : Euc d => ∫ t, K t * a (y + t)) ⊤ volume :=
    memLp_top_of_bound hTm _ (Eventually.of_forall hTreal)
  have hTloc : LocallyIntegrable (fun y : Euc d => ∫ t, K t * a (y + t)) volume :=
    hTbd.locallyIntegrable le_top
  have hacloc : LocallyIntegrable a volume := ha.locallyIntegrable hp
  have hf : LocallyIntegrable (fun y => a y - ∫ t, K t * a (y + t)) volume :=
    hacloc.sub hTloc
  have hzero : ∀ g : Euc d → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ x, g x • (a x - ∫ t, K t * a (x + t)) = 0 := by
    intro g hg hgc
    have hgc' : HasCompactSupport (fun x => ((g x : ℝ) : ℂ)) :=
      hgc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
    have hsm : ContDiff ℝ ∞ (fun x => ((g x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
    let ψ : SchwartzMap (Euc d) ℂ := hgc'.toSchwartzMap hsm
    have hψ : ∀ x, ψ x = ((g x : ℝ) : ℂ) := fun x => rfl
    have hpair : ∫ x, a x * (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) K ψ x)
        = ∫ x, ψ x * ∫ t, K t * a (x + t) := by
      simp only [conv_kernel_apply]
      exact pairing_identity (p' := p') ha K ψ
    have hsψ := fourier_supp_test (p' := p') K hK ha hsupp ψ
    have hI1 : Integrable (fun x => a x * ψ x) := ha.integrable_mul (ψ.memLp p')
    have hI2 : Integrable (fun x => (∫ t, K t * a (x + t)) * ψ x) :=
      Integrable.bdd_mul ψ.integrable hTm (Eventually.of_forall hTreal)
    have e1 : ∫ x, g x • (a x - ∫ t, K t * a (x + t))
        = (∫ x, a x * ψ x) - ∫ x, (∫ t, K t * a (x + t)) * ψ x := by
      rw [← integral_sub hI1 hI2]
      congr 1
      ext x
      rw [Complex.real_smul, hψ]
      ring
    have e2 : ∫ x, (∫ t, K t * a (x + t)) * ψ x = ∫ x, ψ x * ∫ t, K t * a (x + t) := by
      congr 1
      ext x
      ring
    rw [e1, e2, hsψ, hpair, sub_self]
  have hF := ae_eq_zero_of_integral_contDiff_smul_eq_zero hf hzero
  filter_upwards [hF] with y hy
  exact sub_eq_zero.1 hy

/-- Pointwise bound of the convolution `a ⋆ K` at each point. -/
lemma enorm_conv_le {p p' : ℝ≥0∞} [p.HolderConjugate p'] {a : Euc d → ℂ} (ha : MemLp a p volume)
    (K : SchwartzMap (Euc d) ℂ) (y : Euc d) :
    ‖∫ t, K t * a (y + t)‖ₑ ≤ eLpNorm a p volume * eLpNorm K p' volume := by
  calc ‖∫ t, K t * a (y + t)‖ₑ ≤ ∫⁻ t, ‖K t * a (y + t)‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ t, ‖a (t + y) * K t‖ₑ := by
        apply lintegral_congr
        intro t
        rw [add_comm y t, mul_comm (K t)]
    _ ≤ eLpNorm a p volume * eLpNorm K p' volume :=
        lintegral_holder_shift ha (K.memLp p') y

/-- Interpolation: `‖f‖_q ≤ M^{(q-p)/q} ‖f‖_p^{p/q}` when `‖f‖_∞ ≤ M < ∞`. -/
lemma eLpNorm_interp {f : Euc d → ℂ} {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q) (hq : q < ⊤)
    (hf : MemLp f p volume) {M : ℝ≥0∞} (hM : M ≠ ⊤) (hbd : ∀ᵐ x ∂volume, ‖f x‖ₑ ≤ M) :
    eLpNorm f q volume ≤
      M ^ ((q.toReal - p.toReal) / q.toReal) * (eLpNorm f p volume) ^ (p.toReal / q.toReal) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hpt : p ≠ ⊤ := ne_top_of_le_ne_top hq.ne hpq
  have hq0 : q ≠ 0 := (lt_of_lt_of_le (zero_lt_one.trans_le hp) hpq).ne'
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hs : 0 < q.toReal := ENNReal.toReal_pos hq0 hq.ne
  have hrs : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq.ne hpq
  have hmeas := hf.aestronglyMeasurable
  have hB : eLpNorm f p volume = (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂volume) ^ (1 / p.toReal) :=
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hmeas
  have hIB : (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂volume) = (eLpNorm f p volume) ^ p.toReal := by
    rw [hB, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hr.ne', ENNReal.rpow_one]
  have hpoint : ∀ᵐ x ∂volume, ‖f x‖ₑ ^ q.toReal ≤ M ^ (q.toReal - p.toReal) * ‖f x‖ₑ ^ p.toReal := by
    filter_upwards [hbd] with x hx
    have e : ‖f x‖ₑ ^ q.toReal = ‖f x‖ₑ ^ (q.toReal - p.toReal) * ‖f x‖ₑ ^ p.toReal := by
      rw [← ENNReal.rpow_add_of_nonneg (x := ‖f x‖ₑ) (q.toReal - p.toReal) p.toReal
        (sub_nonneg.2 hrs) hr.le, sub_add_cancel]
    rw [e]
    gcongr
  have hlint : ∫⁻ x, ‖f x‖ₑ ^ q.toReal ∂volume
      ≤ M ^ (q.toReal - p.toReal) * ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂volume := by
    calc ∫⁻ x, ‖f x‖ₑ ^ q.toReal ∂volume
        ≤ ∫⁻ x, M ^ (q.toReal - p.toReal) * ‖f x‖ₑ ^ p.toReal ∂volume := lintegral_mono_ae hpoint
      _ = M ^ (q.toReal - p.toReal) * ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂volume :=
          lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.2 hrs) hM)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq.ne hmeas]
  calc (∫⁻ x, ‖f x‖ₑ ^ q.toReal ∂volume) ^ (1 / q.toReal)
      ≤ (M ^ (q.toReal - p.toReal) * ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂volume) ^ (1 / q.toReal) :=
        ENNReal.rpow_le_rpow hlint (by positivity)
    _ = M ^ ((q.toReal - p.toReal) / q.toReal) * (eLpNorm f p volume) ^ (p.toReal / q.toReal) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), hIB, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul, div_eq_mul_one_div (q.toReal - p.toReal), div_eq_mul_one_div p.toReal]

/-- `A^θ ≤ 1 + A` for `θ ∈ [0,1]`. -/
lemma rpow_le_one_add {A : ℝ≥0∞} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : A ^ θ ≤ 1 + A := by
  rcases le_total A 1 with h | h
  · calc A ^ θ ≤ 1 ^ θ := ENNReal.rpow_le_rpow h hθ0
      _ = 1 := ENNReal.one_rpow θ
      _ ≤ 1 + A := le_self_add
  · calc A ^ θ ≤ A ^ (1 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le h hθ1
      _ = A := ENNReal.rpow_one A
      _ ≤ 1 + A := le_add_self

/-- Core of the Bernstein inequality: `a = K ⋆ a` a.e. gives `‖a‖_q ≤ (1 + ‖K‖_{p'}) ‖a‖_p`. -/
lemma bernstein_core {p p' : ℝ≥0∞} [p.HolderConjugate p'] (hp : 1 ≤ p) {q : ℝ≥0∞} (hpq : p ≤ q)
    {R : ℝ} (K : SchwartzMap (Euc d) ℂ) (hK : ∀ ξ : Euc d, ‖ξ‖ < R + 1 → 𝓕 (⇑K) ξ = 1)
    (a : Euc d → ℝ) (ha : MemLp a p volume) (hsupp : FourierSuppIn R a) :
    eLpNorm a q volume ≤ ENNReal.ofReal ((eLpNorm K p' volume).toReal + 1) * eLpNorm a p volume := by
  have hacm : MemLp (fun x => ((a x : ℝ) : ℂ)) p volume := ha.ofReal
  have hBc : eLpNorm (fun x => ((a x : ℝ) : ℂ)) p volume = eLpNorm a p volume :=
    eLpNorm_congr_norm_ae hacm.aestronglyMeasurable ha.aestronglyMeasurable
      (Eventually.of_forall fun x => by simp)
  have hA : eLpNorm K p' volume ≠ ⊤ := (K.memLp p').eLpNorm_lt_top.ne
  have hBtop : eLpNorm a p volume ≠ ⊤ := ha.eLpNorm_lt_top.ne
  have hCeq : ENNReal.ofReal ((eLpNorm K p' volume).toReal + 1) = eLpNorm K p' volume + 1 := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one, ENNReal.ofReal_one,
      ENNReal.ofReal_toReal hA]
  have hBq : ∀ r : ℝ≥0∞, eLpNorm (fun x => ((a x : ℝ) : ℂ)) r volume = eLpNorm a r volume :=
    fun r => eLpNorm_congr_norm_ae (p := r) hacm.aestronglyMeasurable ha.aestronglyMeasurable
      (Eventually.of_forall fun x => by simp)
  have hsupp' : ∀ G : SchwartzMap (Euc d) ℂ,
      Disjoint (tsupport (𝓕 (⇑G))) (closedBall (0 : Euc d) R) →
        ∫ x, ((a x : ℝ) : ℂ) * G x = 0 := fun G hG => hsupp G hG
  have hrep := ae_repr_complex (p' := p') hp K hK hacm hsupp'
  have hbd : ∀ᵐ x ∂volume, ‖((a x : ℝ) : ℂ)‖ₑ ≤ eLpNorm a p volume * eLpNorm K p' volume := by
    filter_upwards [hrep] with y hy
    rw [hy, ← hBq p]
    exact enorm_conv_le hacm K y
  have hM : eLpNorm a p volume * eLpNorm K p' volume ≠ ⊤ :=
    (ENNReal.mul_lt_top ha.eLpNorm_lt_top (K.memLp p').eLpNorm_lt_top).ne
  by_cases hqt : q = ⊤
  · subst hqt
    have hess : eLpNormEssSup (fun x => ((a x : ℝ) : ℂ)) volume
        ≤ eLpNorm a p volume * eLpNorm K p' volume :=
      eLpNormEssSup_le_of_ae_enorm_bound hbd
    have hfin : eLpNorm a ⊤ volume = eLpNormEssSup (fun x => ((a x : ℝ) : ℂ)) volume := by
      rw [← hBq ⊤, eLpNorm_exponent_top hacm.aestronglyMeasurable]
    rw [hfin]
    refine hess.trans ?_
    calc eLpNorm a p volume * eLpNorm K p' volume
        ≤ eLpNorm a p volume * (eLpNorm K p' volume + 1) := by gcongr; exact le_self_add
      _ = ENNReal.ofReal ((eLpNorm K p' volume).toReal + 1) * eLpNorm a p volume := by
          rw [← hCeq, mul_comm]
  · have hq' : q < ⊤ := lt_top_iff_ne_top.2 hqt
    have hq0 : 0 < q.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le (hp.trans hpq)).ne' hq'.ne
    have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' (ne_top_of_le_ne_top hq'.ne hpq)
    have hrs : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq'.ne hpq
    have h1 := eLpNorm_interp (f := fun x => ((a x : ℝ) : ℂ)) hp hpq hq' hacm hM hbd
    rw [hBq q, hBq p] at h1
    set θ : ℝ := (q.toReal - p.toReal) / q.toReal with hθdef
    set η : ℝ := p.toReal / q.toReal with hηdef
    have hθ0 : 0 ≤ θ := div_nonneg (sub_nonneg.2 hrs) hq0.le
    have hθ1 : θ ≤ 1 := div_le_one_of_le₀ (by linarith) hq0.le
    have hη0 : 0 ≤ η := div_nonneg hp0.le hq0.le
    have hsum : θ + η = 1 := by
      rw [hθdef, hηdef, ← add_div, sub_add_cancel, div_self hq0.ne']
    have key : (eLpNorm a p volume * eLpNorm K p' volume) ^ θ * (eLpNorm a p volume) ^ η
        = eLpNorm K p' volume ^ θ * eLpNorm a p volume := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hθ0]
      calc (eLpNorm a p volume) ^ θ * (eLpNorm K p' volume) ^ θ * (eLpNorm a p volume) ^ η
          = (eLpNorm K p' volume) ^ θ * ((eLpNorm a p volume) ^ θ * (eLpNorm a p volume) ^ η) := by
            ring
        _ = (eLpNorm K p' volume) ^ θ * eLpNorm a p volume := by
            rw [← ENNReal.rpow_add_of_nonneg _ _ hθ0 hη0, hsum, ENNReal.rpow_one]
    rw [key] at h1
    refine h1.trans ?_
    calc eLpNorm K p' volume ^ θ * eLpNorm a p volume
        ≤ (1 + eLpNorm K p' volume) * eLpNorm a p volume := by
          gcongr
          exact rpow_le_one_add hθ0 hθ1
      _ ≤ ENNReal.ofReal ((eLpNorm K p' volume).toReal + 1) * eLpNorm a p volume := by
          rw [hCeq, add_comm]

end HRS.Commutator.Whole
