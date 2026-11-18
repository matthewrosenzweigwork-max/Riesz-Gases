import HRS.Commutator.Torus.TEXTAux1

/-!
# T-EXT-A helpers, part 2: uniqueness of Fourier coefficients on `L¹(𝕋^d)`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

/-- `∫ φ g = 0` for every continuous `φ` if all Fourier coefficients of `g` vanish. -/
lemma text_integral_cont_eq_zero {g : Torus d → ℝ} (hg : Integrable g)
    (h : ∀ k, Torus.fcoef g k = 0) (φ : C(Torus d, ℂ)) :
    ∫ x, φ x * (g x : ℂ) = 0 := by
  have hint : ∀ φ : C(Torus d, ℂ), Integrable (fun x => φ x * (g x : ℂ)) := fun φ =>
    hg.ofReal.bdd_mul φ.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => φ.norm_coe_le_norm x)
  let Λ : C(Torus d, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => ∫ x, φ x * (g x : ℂ)
      map_add' := fun φ ψ => by
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add (hint φ) (hint ψ)
      map_smul' := fun c φ => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
        exact integral_const_mul c _ }
  have hΛ : Continuous Λ := by
    refine (Λ.mkContinuous (∫ x, ‖g x‖) (fun φ => ?_)).continuous
    show ‖∫ x, φ x * (g x : ℂ)‖ ≤ (∫ x, ‖g x‖) * ‖φ‖
    calc ‖∫ x, φ x * (g x : ℂ)‖ ≤ ∫ x, ‖φ‖ * ‖g x‖ := by
          refine norm_integral_le_of_norm_le (hg.norm.const_mul ‖φ‖)
            (Filter.Eventually.of_forall fun x => ?_)
          rw [norm_mul, Complex.norm_real]
          exact mul_le_mul_of_nonneg_right (φ.norm_coe_le_norm x) (norm_nonneg _)
      _ = (∫ x, ‖g x‖) * ‖φ‖ := by rw [integral_const_mul, mul_comm]
  have hclosed : IsClosed ((LinearMap.ker Λ : Submodule ℂ C(Torus d, ℂ)) : Set C(Torus d, ℂ)) :=
    (isClosed_singleton (x := (0 : ℂ))).preimage hΛ
  have hspan : Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := Fin d))) ≤
      LinearMap.ker Λ := by
    rw [Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    show Λ _ = 0
    have := h (-n)
    simp only [Torus.fcoef, neg_neg] at this
    exact this
  have htop : (LinearMap.ker Λ) = ⊤ := by
    have h1 := Submodule.topologicalClosure_minimal _ hspan hclosed
    rw [UnitAddTorus.span_mFourier_closure_eq_top] at h1
    exact top_le_iff.1 h1
  have : φ ∈ LinearMap.ker Λ := by rw [htop]; trivial
  exact this

lemma text_ae_eq_zero_of_fcoef_aux {g : Torus d → ℝ} (hgm : Measurable g) (hg : Integrable g)
    (h : ∀ k, Torus.fcoef g k = 0) : g =ᵐ[volume] 0 := by
  have hψ : ∀ ψ : BoundedContinuousFunction (Torus d) ℝ, ∫ x, ψ x * g x = 0 := by
    intro ψ
    have := text_integral_cont_eq_zero hg h
      ⟨fun x => (ψ x : ℂ), Complex.continuous_ofReal.comp ψ.continuous⟩
    simp only [ContinuousMap.coe_mk] at this
    have h2 : ∫ x, ((ψ x * g x : ℝ) : ℂ) = 0 := by simpa using this
    rw [integral_complex_ofReal] at h2
    exact_mod_cast h2
  set μp : Measure (Torus d) := volume.withDensity (fun x => ENNReal.ofReal (g x)) with hμp
  set μn : Measure (Torus d) := volume.withDensity (fun x => ENNReal.ofReal (-g x)) with hμn
  have hpfin : ∫⁻ x, ENNReal.ofReal (g x) < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hg.hasFiniteIntegral
    calc ENNReal.ofReal (g x) ≤ ENNReal.ofReal |g x| := ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ = ‖g x‖ₑ := (Real.enorm_eq_ofReal_abs _).symm
  have hnfin : ∫⁻ x, ENNReal.ofReal (-g x) < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hg.hasFiniteIntegral
    calc ENNReal.ofReal (-g x) ≤ ENNReal.ofReal |g x| := ENNReal.ofReal_le_ofReal (neg_le_abs _)
      _ = ‖g x‖ₑ := (Real.enorm_eq_ofReal_abs _).symm
  haveI : IsFiniteMeasure μp := by
    refine ⟨?_⟩
    rw [hμp, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hpfin
  haveI : IsFiniteMeasure μn := by
    refine ⟨?_⟩
    rw [hμn, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hnfin
  have hint_p : ∀ ψ : BoundedContinuousFunction (Torus d) ℝ,
      ∫ x, ψ x ∂μp = ∫ x, (max (g x) 0) * ψ x := by
    intro ψ
    rw [hμp, integral_withDensity_eq_integral_toReal_smul (hgm.ennreal_ofReal) 
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [ENNReal.toReal_ofReal', max_comm]
  have hint_n : ∀ ψ : BoundedContinuousFunction (Torus d) ℝ,
      ∫ x, ψ x ∂μn = ∫ x, (max (-g x) 0) * ψ x := by
    intro ψ
    have hmn : Measurable (fun x => ENNReal.ofReal (-g x)) := hgm.neg.ennreal_ofReal
    rw [hμn, integral_withDensity_eq_integral_toReal_smul hmn
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [ENNReal.toReal_ofReal', max_comm]
  have hmeq : μp = μn := by
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun ψ => ?_
    rw [hint_p, hint_n]
    have h0 := hψ ψ
    have hi1 : Integrable (fun x => (max (g x) 0) * ψ x) :=
      (hg.pos_part).bdd_mul ψ.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by simpa using ψ.norm_coe_le_norm x) |>.congr
        (Filter.Eventually.of_forall fun x => by simp [mul_comm])
    have hi2 : Integrable (fun x => (max (-g x) 0) * ψ x) :=
      (hg.neg_part).bdd_mul ψ.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by simpa using ψ.norm_coe_le_norm x) |>.congr
        (Filter.Eventually.of_forall fun x => by simp [mul_comm])
    have e : ∫ x, ψ x * g x = ∫ x, ((max (g x) 0) * ψ x - (max (-g x) 0) * ψ x) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      rcases le_total 0 (g x) with hx | hx
      · simp [max_eq_left hx, max_eq_right (neg_nonpos.2 hx)]; ring
      · simp [max_eq_right hx, max_eq_left (neg_nonneg.2 hx)]; ring
    rw [e, integral_sub hi1 hi2] at h0
    linarith
  refine ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite (fun s _ _ => hg.integrableOn) ?_
  intro s hs _
  have h1 := congrArg (fun μ => μ s) hmeq
  simp only [hμp, hμn, withDensity_apply _ hs] at h1
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg.integrableOn, h1, sub_self]

/-- Uniqueness: an integrable function on the torus with all Fourier coefficients zero vanishes a.e. -/
lemma text_ae_eq_zero_of_fcoef {g : Torus d → ℝ} (hg : Integrable g)
    (h : ∀ k, Torus.fcoef g k = 0) : g =ᵐ[volume] 0 := by
  set g' := hg.1.mk g with hg'
  have hae : g =ᵐ[volume] g' := hg.1.ae_eq_mk
  have hm : Measurable g' := hg.1.stronglyMeasurable_mk.measurable
  have hint : Integrable g' := hg.congr hae
  have hc : ∀ k, Torus.fcoef g' k = 0 := fun k => by
    rw [← h k]
    unfold Torus.fcoef
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  have := text_ae_eq_zero_of_fcoef_aux hm hint hc
  exact hae.trans this

end HRS.Commutator.TorusNote
