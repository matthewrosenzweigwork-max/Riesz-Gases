import HRS.MH.ScreenedS3
import HRS.PDE.ToolboxRd.Fourier

/-!
# UniqT2: Fourier bridge for the Riesz kernel on Schwartz functions (spike T2)

For Schwartz `u v` and the constant `c` of `kg_fourier_h_proof`,
`symbolForm (c (2π ξ_l)² ‖ξ‖^{s-d}) u v = - ∫ u (g * D_l² v)`.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate SchwartzMap LineDeriv

namespace HRS.MS.UniqT2
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

/-- `D_l v` as a real Schwartz function. -/
def dl (l : Fin d) (v : SchwartzMap (Euc d) ℝ) : SchwartzMap (Euc d) ℝ :=
  SchwartzMap.evalCLM ℝ (Euc d) ℝ (EuclideanSpace.single l 1) (SchwartzMap.fderivCLM ℝ (Euc d) ℝ v)

lemma dl_apply (l : Fin d) (v : SchwartzMap (Euc d) ℝ) (x : Euc d) :
    dl l v x = fderiv ℝ v x (EuclideanSpace.single l 1) := rfl

lemma fourier_dl (l : Fin d) (v : SchwartzMap (Euc d) ℝ) (ξ : Euc d) :
    𝓕 (fun x : Euc d => ((dl l v x : ℝ) : ℂ)) ξ =
      (2 * Real.pi * Complex.I * (ξ l : ℂ)) * 𝓕 (fun x : Euc d => ((v x : ℝ) : ℂ)) ξ := by
  set V : SchwartzMap (Euc d) ℂ := v.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM with hV
  have h1 := SchwartzMap.fourier_lineDerivOp_eq V (EuclideanSpace.single l 1)
  have h2 : ⇑(∂_{(EuclideanSpace.single l 1 : Euc d)} V : SchwartzMap (Euc d) ℂ) =
      fun x : Euc d => ((dl l v x : ℝ) : ℂ) := by
    ext x
    show fderiv ℝ (⇑V) x _ = _
    have : ⇑V = fun x => ((v x : ℝ) : ℂ) := rfl
    rw [this, dl_apply]
    have hd : DifferentiableAt ℝ (⇑v) x := v.differentiableAt
    rw [show (fun x => ((v x : ℝ) : ℂ)) = Complex.ofRealCLM ∘ ⇑v from rfl,
      (Complex.ofRealCLM.hasFDerivAt.comp x hd.hasFDerivAt).fderiv]
    rfl
  have h3 : ⇑V = fun x => ((v x : ℝ) : ℂ) := rfl
  have hg : (fun x : Euc d => inner ℝ x (EuclideanSpace.single l 1 : Euc d)).HasTemperateGrowth :=
    ((innerSL ℝ).flip (EuclideanSpace.single l 1 : Euc d)).hasTemperateGrowth
  have e : 𝓕 (fun x : Euc d => ((dl l v x : ℝ) : ℂ)) ξ = (𝓕 (∂_{(EuclideanSpace.single l 1 : Euc d)} V : SchwartzMap (Euc d) ℂ)) ξ := by
    rw [SchwartzMap.fourier_coe, h2]
  rw [e, h1]
  simp only [smul_apply, smul_eq_mul]
  rw [SchwartzMap.smulLeftCLM_apply_apply hg, SchwartzMap.fourier_coe, h3]
  simp [EuclideanSpace.inner_single_right]
  ring

lemma conj_fourier_real (u : SchwartzMap (Euc d) ℝ) (ξ : Euc d) :
    conj (𝓕 (fun x : Euc d => ((u x : ℝ) : ℂ)) ξ) =
      ∫ y : Euc d, ((u y : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (inner ℝ y ξ : ℝ)) := by
  rw [Real.fourier_eq, ← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [Circle.smul_def, smul_eq_mul, map_mul, Complex.conj_ofReal, Real.fourierChar_apply]
  rw [← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [mul_comm]
  congr 2
  push_cast; ring

lemma fubini_step (u : SchwartzMap (Euc d) ℝ) {H : Euc d → ℂ} (hH : Integrable H) :
    ∫ y : Euc d, ((u y : ℝ) : ℂ) * ∫ ξ : Euc d, H ξ *
        Complex.exp (2 * Real.pi * Complex.I * (inner ℝ y ξ : ℝ)) =
      ∫ ξ : Euc d, H ξ * conj (𝓕 (fun x : Euc d => ((u x : ℝ) : ℂ)) ξ) := by
  have hu : Integrable (fun y : Euc d => ((u y : ℝ) : ℂ)) :=
    (u.integrable (μ := volume)).ofReal
  have hmeas : AEStronglyMeasurable (fun p : Euc d × Euc d =>
      ((u p.1 : ℝ) : ℂ) * (H p.2 * Complex.exp (2 * Real.pi * Complex.I * (inner ℝ p.1 p.2 : ℝ))))
      (volume.prod volume) := by
    refine (hu.aestronglyMeasurable.comp_quasiMeasurePreserving
      MeasureTheory.Measure.quasiMeasurePreserving_fst).mul ?_
    refine (hH.aestronglyMeasurable.comp_quasiMeasurePreserving
      MeasureTheory.Measure.quasiMeasurePreserving_snd).mul ?_
    exact (by fun_prop : Continuous fun p : Euc d × Euc d =>
      Complex.exp (2 * Real.pi * Complex.I * (inner ℝ p.1 p.2 : ℝ))).aestronglyMeasurable
  have hint : Integrable (fun p : Euc d × Euc d =>
      ((u p.1 : ℝ) : ℂ) * (H p.2 * Complex.exp (2 * Real.pi * Complex.I * (inner ℝ p.1 p.2 : ℝ))))
      (volume.prod volume) := by
    refine (hu.mul_prod hH).norm.mono' hmeas (Eventually.of_forall fun p => ?_)
    have : ‖Complex.exp (2 * Real.pi * Complex.I * (inner ℝ p.1 p.2 : ℝ))‖ = 1 := by
      rw [show (2 * Real.pi * Complex.I * ((inner ℝ p.1 p.2 : ℝ) : ℂ)) =
        (((2 * Real.pi * (inner ℝ p.1 p.2 : ℝ) : ℝ)) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    simp [this]
  have h1 : ∀ y : Euc d, ((u y : ℝ) : ℂ) * ∫ ξ : Euc d, H ξ *
        Complex.exp (2 * Real.pi * Complex.I * (inner ℝ y ξ : ℝ)) =
      ∫ ξ : Euc d, ((u y : ℝ) : ℂ) * (H ξ *
        Complex.exp (2 * Real.pi * Complex.I * (inner ℝ y ξ : ℝ))) := fun y =>
    (integral_const_mul _ _).symm
  simp_rw [h1]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  beta_reduce
  rw [conj_fourier_real u ξ, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  ring

/-- **T2 (Fourier bridge on Schwartz functions).**  There is `c > 0` (the constant of
`kg_fourier_h_proof`) such that for all directions `l` and real Schwartz `u v`,
`symbolForm (c (2π ξ_l)² ‖ξ‖^{s-d}) u v = - ∫ u (g * D_l² v)` with `g = rieszKernel d s`,
`(g * f)(x) = ∫ g (x - y) f y dy` and `D_l = fderiv · (e_l)`.  No sign or constant correction. -/
theorem t2_bridge (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (l : Fin d) (u v : SchwartzMap (Euc d) ℝ),
      symbolForm (fun ξ : Euc d => c * (2 * Real.pi * ξ l) ^ 2 * ‖ξ‖ ^ (s - d)) u v =
        - ∫ x, u x * HRS.Whole.convFun (rieszKernel d s)
            (fun y => fderiv ℝ (fun z => fderiv ℝ v z (EuclideanSpace.single l 1)) y
              (EuclideanSpace.single l 1)) x := by
  obtain ⟨c, hc, h⟩ := HRS.MH.Screened.kg_fourier_h_proof hd hs0 hsd
  refine ⟨c, hc, fun l u v => ?_⟩
  set φ : SchwartzMap (Euc d) ℝ := dl l v with hφ
  set Hf : Euc d → ℂ := fun ξ => ((c * (2 * Real.pi * ξ l) * ‖ξ‖ ^ (s - d) : ℝ) : ℂ) * Complex.I *
    𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ with hHf
  have hHint : Integrable Hf := (h l φ 0).1
  have hw : ∀ y, ((HRS.Whole.convFun (rieszKernel d s)
      (fun y => fderiv ℝ (fun z => fderiv ℝ v z (EuclideanSpace.single l 1)) y
        (EuclideanSpace.single l 1)) y : ℝ) : ℂ) =
      ∫ ξ : Euc d, Hf ξ * Complex.exp (2 * Real.pi * Complex.I * (inner ℝ y ξ : ℝ)) :=
    fun y => (h l φ y).2
  set I0 : ℝ := ∫ x, u x * HRS.Whole.convFun (rieszKernel d s)
            (fun y => fderiv ℝ (fun z => fderiv ℝ v z (EuclideanSpace.single l 1)) y
              (EuclideanSpace.single l 1)) x with hI0
  have e1 : (I0 : ℂ) = ∫ ξ, Hf ξ * conj (𝓕 (fun x : Euc d => ((u x : ℝ) : ℂ)) ξ) := by
    rw [hI0, ← integral_complex_ofReal, ← fubini_step u hHint]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [Complex.ofReal_mul, hw y]
  set m : Euc d → ℝ := fun ξ => c * (2 * Real.pi * ξ l) ^ 2 * ‖ξ‖ ^ (s - d) with hm
  set T : ℂ := ∫ ξ, ((m ξ : ℝ) : ℂ) * (𝓕 (fun x : Euc d => ((u x : ℝ) : ℂ)) ξ *
    conj (𝓕 (fun x : Euc d => ((v x : ℝ) : ℂ)) ξ)) with hT
  have e2 : (I0 : ℂ) = - conj T := by
    rw [e1, hT, ← integral_conj, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [hHf, hφ, fourier_dl, hm, map_mul, Complex.conj_ofReal]
    push_cast
    simp only [Complex.conj_conj]
    ring_nf
    simp [Complex.I_sq]
  have e3 : symbolForm m u v = T.re := by
    unfold symbolForm
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [fourierL2_schwartz u, fourierL2_schwartz v] with ξ hu hv
    rw [hu, hv]
  rw [e3]
  have := congrArg Complex.re e2
  simp at this
  linarith

end HRS.MS.UniqT2
