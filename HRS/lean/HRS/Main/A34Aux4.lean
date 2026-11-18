import HRS.Main.A34Aux3

/-!
# Packet A34, helper 4: one-dimensional Gaussian laws and the `W₁` coupling of convolutions
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A34

open HRS HRS.PDE HRS.PDE.ET HRS.A33

/-- the line embedding `ℝ → ℝ^1` -/
def a34_ι (x : ℝ) : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 fun _ => x

theorem a34_ι_meas : Measurable a34_ι :=
  (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun _ => measurable_id)

theorem a34_ι_norm (x : ℝ) : ‖a34_ι x‖ = |x| := by
  simp [a34_ι, EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]

theorem a34_ι_add (x y : ℝ) : a34_ι (x + y) = a34_ι x + a34_ι y := by
  ext i; simp [a34_ι]

/-- `ℝ^1 ≃ᵐ ℝ` -/
def a34_e : EuclideanSpace ℝ (Fin 1) ≃ᵐ ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans (MeasurableEquiv.funUnique (Fin 1) ℝ)

theorem a34_e_apply (x : EuclideanSpace ℝ (Fin 1)) : a34_e x = x.ofLp 0 := rfl

theorem a34_gauss1 (v : ℝ) (hv : 0 ≤ v) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) (Matrix.of fun _ _ => v) =
      (gaussianReal 0 1).map (fun z => a34_ι (Real.sqrt v * z)) := by
  have hS : (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => v).PosSemidef := by
    have : (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => v) = Matrix.diagonal (fun _ => v) := by
      ext i j; fin_cases i; fin_cases j; simp
    rw [this]
    exact Matrix.posSemidef_diagonal_iff.2 fun _ => hv
  apply MeasurableEquiv.map_measurableEquiv_injective a34_e
  have h1 := (measurePreserving_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin 1)))
    (S := Matrix.of fun (_ : Fin 1) (_ : Fin 1) => v) hS (i := 0)).map_eq
  have h2 : ((gaussianReal 0 1).map (fun z => a34_ι (Real.sqrt v * z))).map a34_e =
      gaussianReal 0 v.toNNReal := by
    rw [Measure.map_map a34_e.measurable]
    · have : (a34_e ∘ fun z => a34_ι (Real.sqrt v * z)) = fun z => Real.sqrt v * z := by
        funext z; simp [a34_e_apply, a34_ι]
      rw [this, gaussianReal_map_const_mul]
      congr 1
      · simp
      · ext; simp [Real.sq_sqrt hv, hv]
    · exact a34_ι_meas.comp (measurable_const.mul measurable_id)
  rw [h2]
  have h3 : (a34_e : EuclideanSpace ℝ (Fin 1) → ℝ) = fun x => x.ofLp 0 := rfl
  rw [h3]
  simpa using h1

theorem a34_int_abs_gauss : ∫ z : ℝ, |z| ∂(gaussianReal 0 1) ≤ 1 := by
  have hm : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 1) := by
    have := memLp_id_gaussianReal (μ := 0) (v := 1) 2
    simpa using this
  have h1 := a33_integral_abs_le (P := gaussianReal 0 1) (id : ℝ → ℝ) hm
  have h2 : ∫ z : ℝ, z ^ 2 ∂(gaussianReal 0 1) = 1 := by
    have hv := variance_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_eq_sub hm] at hv
    simp only [Pi.pow_apply] at hv
    simpa using hv
  simp only [id] at h1
  rw [h2, Real.sqrt_one] at h1
  exact h1

theorem a34_W1_conv {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : Integrable (fun ω => X ω - Y ω) P) (v₁ v₂ : ℝ) (h₁ : 0 ≤ v₁) (h₂ : 0 ≤ v₂) :
    wassersteinE 1
      (law P (fun ω => a34_ι (X ω)) ∗
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) (Matrix.of fun _ _ => v₁))
      (law P (fun ω => a34_ι (Y ω)) ∗
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) (Matrix.of fun _ _ => v₂)) ≤
    ENNReal.ofReal (∫ ω, |X ω - Y ω| ∂P + |Real.sqrt v₁ - Real.sqrt v₂|) := by
  set γ : Measure ℝ := gaussianReal 0 1 with hγ
  set σ₁ := Real.sqrt v₁
  set σ₂ := Real.sqrt v₂
  have hconv : ∀ μ ν : Measure (EuclideanSpace ℝ (Fin 1)), μ ∗ ν =
      (μ.prod ν).map (fun x => x.1 + x.2) := fun _ _ => rfl
  have hg : ∀ σ : ℝ, Measurable fun z : ℝ => a34_ι (σ * z) := fun σ =>
    a34_ι_meas.comp (measurable_const.mul measurable_id)
  have hmarg : ∀ (Z : Ω → ℝ) (hZ : Measurable Z) (v : ℝ) (hv : 0 ≤ v),
      law P (fun ω => a34_ι (Z ω)) ∗
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) (Matrix.of fun _ _ => v) =
      (P.prod γ).map (fun w => a34_ι (Z w.1) + a34_ι (Real.sqrt v * w.2)) := by
    intro Z hZ v hv
    rw [a34_gauss1 v hv, hconv]
    unfold law
    have hpm := Measure.map_prod_map P γ (f := fun ω => a34_ι (Z ω)) (g := fun z : ℝ => a34_ι (Real.sqrt v * z))
      (a34_ι_meas.comp hZ) (hg (Real.sqrt v))
    have hmap := Measure.map_map (μ := P.prod γ) (g := fun x : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) => x.1 + x.2)
      (f := Prod.map (fun ω => a34_ι (Z ω)) fun z => a34_ι (Real.sqrt v * z))
      (measurable_fst.add measurable_snd) (Measurable.prodMap (a34_ι_meas.comp hZ) (hg _))
    rw [hpm, hmap]
    rfl
  set FA : Ω × ℝ → EuclideanSpace ℝ (Fin 1) := fun w => a34_ι (X w.1) + a34_ι (σ₁ * w.2) with hFA
  set FB : Ω × ℝ → EuclideanSpace ℝ (Fin 1) := fun w => a34_ι (Y w.1) + a34_ι (σ₂ * w.2) with hFB
  have hFAm : Measurable FA :=
    (a34_ι_meas.comp (hX.comp measurable_fst)).add (hg σ₁ |>.comp measurable_snd)
  have hFBm : Measurable FB :=
    (a34_ι_meas.comp (hY.comp measurable_fst)).add (hg σ₂ |>.comp measurable_snd)
  have hπ : IsCoupling ((P.prod γ).map fun w => (FA w, FB w))
      (law P (fun ω => a34_ι (X ω)) ∗
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) (Matrix.of fun _ _ => v₁))
      (law P (fun ω => a34_ι (Y ω)) ∗
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) (Matrix.of fun _ _ => v₂)) := by
    constructor
    · rw [Measure.map_map measurable_fst (hFAm.prodMk hFBm), hmarg X hX v₁ h₁]
      rfl
    · rw [Measure.map_map measurable_snd (hFAm.prodMk hFBm), hmarg Y hY v₂ h₂]
      rfl
  refine (wassersteinE_le_cost hπ).trans ?_
  rw [lintegral_map (by fun_prop) (hFAm.prodMk hFBm)]
  simp only [div_one, ENNReal.rpow_one, Real.rpow_one]
  set G : Ω × ℝ → ℝ := fun w => |X w.1 - Y w.1| + |σ₁ - σ₂| * |w.2| with hG
  have hle : ∀ w, ‖FA w - FB w‖ ≤ G w := by
    intro w
    have : FA w - FB w = a34_ι ((X w.1 - Y w.1) + (σ₁ - σ₂) * w.2) := by
      ext i; simp [hFA, hFB, a34_ι]; ring
    rw [this, a34_ι_norm]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
  have hI1 : Integrable (fun w : Ω × ℝ => |X w.1 - Y w.1|) (P.prod γ) :=
    (hXY.abs).comp_fst (ν := γ)
  have hgi : Integrable (fun z : ℝ => |z|) γ := by
    have := (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by simp)
    exact this.abs
  have hI2 : Integrable (fun w : Ω × ℝ => |σ₁ - σ₂| * |w.2|) (P.prod γ) :=
    (hgi.comp_snd (μ := P)).const_mul _
  have hGint : Integrable G (P.prod γ) := hI1.add hI2
  refine le_trans (lintegral_mono fun w => ENNReal.ofReal_le_ofReal (hle w)) ?_
  refine le_trans (ofReal_integral_eq_lintegral_ofReal hGint
          (Eventually.of_forall fun w => by positivity)).symm.le ?_
  calc ENNReal.ofReal (∫ w, G w ∂(P.prod γ)) ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have e1 : ∫ w, G w ∂(P.prod γ) =
            ∫ ω, |X ω - Y ω| ∂P + |σ₁ - σ₂| * ∫ z, |z| ∂γ := by
          rw [integral_add hI1 hI2, integral_const_mul]
          congr 1
          · rw [integral_prod _ hI1]; simp
          · congr 1
            have hI3 : Integrable (fun w : Ω × ℝ => |w.2|) (P.prod γ) := hgi.comp_snd (μ := P)
            rw [integral_prod _ hI3]; simp
        rw [e1]
        have := mul_le_mul_of_nonneg_left a34_int_abs_gauss (abs_nonneg (σ₁ - σ₂))
        linarith

end HRS.A34
