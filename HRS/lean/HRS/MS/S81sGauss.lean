import HRS.Main.GFB4Aux4
import HRS.Prob.HilbertMartingale
import HRS.MS.S81pGauss

/-!
# S8.1 (worker S81S): multi-time Gaussian laws of Hilbert martingales with deterministic covariation, independent of `ℱ 0`

Namespace `HRS.Whole.S81S`, prefix `s81s_`.

* `s81s_hm_cond`: a Hilbert martingale with covariation density stays one under `P(· | A)` for `A ∈ ℱ 0`.
* `s81s_vec_gauss_indep`: if `G` is a continuous Hilbert martingale started at zero with deterministic covariation density `C`,
  the vector `(⟨G(t_a), y_a⟩)_a` of finitely many pairings is centered Gaussian with covariance
  `S_{ab} = ∫_0^{t_a ∧ t_b} C_σ(y_a, y_b) dσ`, this matrix is positive semidefinite, and the vector is independent of every
  sub-σ-algebra `𝒢 ≤ ℱ 0` (Pro R26-T2.K07, with the independence).
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole

namespace HRS.Whole.S81S

section Cond

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

theorem s81s_hm_cond {ℱ : Filtration ℝ mΩ} {T : ℝ} {M : ℝ → Ω → H}
    {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)} (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg)
    {A : Set Ω} (hA : MeasurableSet[ℱ 0] A) (hP0 : P A ≠ 0) :
    IsHilbertMartingaleWithCovariation (ProbabilityTheory.cond P A) ℱ T M Sg := by
  have hQP : ProbabilityTheory.cond P A ≪ P := ProbabilityTheory.cond_absolutelyContinuous
  have hAm : MeasurableSet A := ℱ.le 0 _ hA
  refine
    { martingale := fun x => ?_
      zero := hQP.ae_le hM.zero
      cont := hQP.ae_le hM.cont
      sq_int := fun τ hτ => ((hM.sq_int τ hτ).restrict A).smul_measure (ENNReal.inv_ne_top.2 hP0)
      sigma_meas := hM.sigma_meas
      sigma_adapted := hM.sigma_adapted
      sigma_traceClass := hQP.ae_le hM.sigma_traceClass
      sigma_int := (hM.sigma_int.restrict (s := A)).smul_measure (ENNReal.inv_ne_top.2 hP0)
      sigma_pathint := hQP.ae_le hM.sigma_pathint
      sigma_entry_int := hQP.ae_le hM.sigma_entry_int
      covariation := fun x y => ?_ }
  · refine martingale_cond P (hM.martingale x) ?_ hA hP0
    filter_upwards [hM.zero] with ω hω
    simp [hω]
  · refine martingale_cond P (hM.covariation x y) ?_ hA hP0
    filter_upwards [hM.zero] with ω hω
    simp [hω]

end Cond

section Vec

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- The covariance matrix `S_{ab} = ∫_0^{t_a ∧ t_b} C_σ(y_a, y_b) dσ`. -/
def s81s_covMat (C : ℝ → H →L[ℝ] H →L[ℝ] ℝ) {p : ℕ} (ts : Fin p → ℝ) (ys : Fin p → H) :
    Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun a b => ∫ σ in Set.Icc 0 (min (ts a) (ts b)), C σ (ys a) (ys b)

/-- The vector of pairings `(⟨G(t_a), y_a⟩)_a`. -/
def s81s_pairVec (G : ℝ → Ω → H) {p : ℕ} (ts : Fin p → ℝ) (ys : Fin p → H) (ω : Ω) :
    EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 fun a => inner ℝ (G (ts a) ω) (ys a)

theorem s81s_pairVec_meas {G : ℝ → Ω → H} (hGm : ∀ t, Measurable (G t)) {p : ℕ} (ts : Fin p → ℝ)
    (ys : Fin p → H) : Measurable (s81s_pairVec G ts ys) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp
    (measurable_pi_iff.2 fun a => (hGm _).inner measurable_const)

theorem s81s_vec_law {ℱ : Filtration ℝ mΩ} {G : ℝ → Ω → H} {C : ℝ → H →L[ℝ] H →L[ℝ] ℝ} {T : ℝ}
    (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => C r))
    (hGc : ∀ ω, Continuous fun s => G s ω) (hGz : ∀ ω, G 0 ω = 0) (hGm : ∀ t, Measurable (G t))
    (hT : 0 < T) {p : ℕ} (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T) (ys : Fin p → H) :
    P.map (s81s_pairVec G ts ys) = multivariateGaussian 0 (s81s_covMat C ts ys) := by
  set B : ℝ := ∑ a, ‖ys a‖ with hB
  have h := HRS.GF.gfb4_vec_gaussian hG hGc hGz hT ts hts (fun a _ => ys a) (B := B)
    (fun a σ _ => Finset.single_le_sum (f := fun a => ‖ys a‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ a))
    (fun a x => (continuousOn_const : ContinuousOn (fun _ : ℝ => inner ℝ (ys a) x) (Set.Icc 0 (ts a))))
    _ (s81s_pairVec_meas hGm ts ys)
    (fun a => by
      have : ∀ N' ζ, ‖(s81s_pairVec G ts ys ζ) a - HRS.Uniform.Q54c.isum (fun σ => G σ ζ) (fun _ => ys a) T (ts a) N'‖ₑ ^ 2
          = 0 := by
        intro N' ζ
        have e := HRS.MS.GenPath.s56_isum_const (fun σ => G σ ζ) (ys a) (hts a) N'
        rw [e, hGz]
        simp [s81s_pairVec]
      simp_rw [this]
      simp)
  exact h

theorem s81s_covMat_psd {C : ℝ → H →L[ℝ] H →L[ℝ] ℝ} {T : ℝ} {p : ℕ} (ts : Fin p → ℝ)
    (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T) (ys : Fin p → H)
    (hCtc : ∀ σ ∈ Set.Icc (0 : ℝ) T, IsTraceClassCov (C σ))
    (hCint : ∀ u v : H, IntegrableOn (fun σ => C σ u v) (Set.Icc (0 : ℝ) T)) :
    (s81s_covMat C ts ys).PosSemidef := by
  classical
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext a b
    simp only [Matrix.conjTranspose_apply, s81s_covMat, Matrix.of_apply, star_trivial]
    rw [min_comm]
    refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
    exact (hCtc σ ⟨hσ.1, hσ.2.trans ((min_le_left _ _).trans (hts a).2)⟩).symm _ _
  · -- the quadratic form is an integral of nonnegative integrands
    set f : Fin p → Fin p → ℝ → ℝ := fun a b σ =>
      if σ ≤ min (ts a) (ts b) then C σ (ys a) (ys b) else 0 with hf
    have hfint : ∀ a b, IntegrableOn (f a b) (Set.Icc (0 : ℝ) T) := fun a b =>
      (hCint (ys a) (ys b)).indicator (measurableSet_Iic (a := min (ts a) (ts b)))
    have hset : ∀ a b, ∫ σ in Set.Icc (0 : ℝ) (min (ts a) (ts b)), C σ (ys a) (ys b) =
        ∫ σ in Set.Icc (0 : ℝ) T, f a b σ := by
      intro a b
      have hle : min (ts a) (ts b) ≤ T := (min_le_left _ _).trans (hts a).2
      have e : Set.Icc (0 : ℝ) (min (ts a) (ts b)) =
          Set.Icc (0 : ℝ) T ∩ Set.Iic (min (ts a) (ts b)) := by
        ext σ
        simp only [Set.mem_Icc, Set.mem_inter_iff, Set.mem_Iic]
        constructor
        · rintro ⟨h0, h1⟩; exact ⟨⟨h0, h1.trans hle⟩, h1⟩
        · rintro ⟨⟨h0, _⟩, h1⟩; exact ⟨h0, h1⟩
      rw [e, ← setIntegral_indicator (measurableSet_Iic (a := min (ts a) (ts b)))]
      refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
      simp only [hf, Set.indicator, Set.mem_Iic]
    set w : ℝ → H := fun σ => ∑ a, (if σ ≤ ts a then x a else 0) • ys a with hw
    have hpt : ∀ σ, C σ (w σ) (w σ) = ∑ a, ∑ b, x a * x b * f a b σ := by
      intro σ
      simp only [hw, map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul, Finset.mul_sum, hf]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      by_cases h1 : σ ≤ ts a <;> by_cases h2 : σ ≤ ts b <;> simp [h1, h2] <;> ring
    have hquad : dotProduct (star x) (Matrix.mulVec (s81s_covMat C ts ys) x) =
        ∫ σ in Set.Icc (0 : ℝ) T, C σ (w σ) (w σ) := by
      simp_rw [hpt]
      rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => (hfint a b).const_mul _)]
      simp only [dotProduct, Matrix.mulVec, s81s_covMat, Matrix.of_apply, star_trivial, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_finsetSum _ (fun b _ => (hfint a b).const_mul _)]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [integral_const_mul, hset a b]
      ring
    rw [hquad]
    exact setIntegral_nonneg measurableSet_Icc fun σ hσ => (hCtc σ hσ).nonneg _

end Vec

section VecIndep

theorem s81s_vec_gauss_indep {Ω : Type*} (𝒢 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H] {ℱ : Filtration ℝ mΩ} {G : ℝ → Ω → H}
    {C : ℝ → H →L[ℝ] H →L[ℝ] ℝ} {T : ℝ}
    (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => C r))
    (hGc : ∀ ω, Continuous fun s => G s ω) (hGz : ∀ ω, G 0 ω = 0) (hGm : ∀ t, Measurable (G t))
    (hT : 0 < T) (h𝒢 : 𝒢 ≤ ℱ 0) {p : ℕ} (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T)
    (ys : Fin p → H) :
    Indep 𝒢 (MeasurableSpace.comap (s81s_pairVec G ts ys) inferInstance) P ∧
      P.map (s81s_pairVec G ts ys) = multivariateGaussian 0 (s81s_covMat C ts ys) ∧
      (s81s_covMat C ts ys).PosSemidef := by
  have hlaw := s81s_vec_law hG hGc hGz hGm hT ts hts ys
  refine ⟨?_, hlaw, ?_⟩
  · have hZm := s81s_pairVec_meas hGm ts ys
    rw [Indep_iff]
    rintro A S hA ⟨Bset, hBm, rfl⟩
    have hA0 : MeasurableSet[ℱ 0] A := h𝒢 _ hA
    have hAm : MeasurableSet A := ℱ.le 0 _ hA0
    by_cases hP0 : P A = 0
    · rw [hP0, zero_mul]; exact measure_mono_null Set.inter_subset_left hP0
    · haveI := ProbabilityTheory.cond_isProbabilityMeasure hP0
      have hGA := s81s_hm_cond hG hA0 hP0
      have hlawA := s81s_vec_law hGA hGc hGz hGm hT ts hts ys
      have h1 : (ProbabilityTheory.cond P A) (s81s_pairVec G ts ys ⁻¹' Bset) =
          P (s81s_pairVec G ts ys ⁻¹' Bset) := by
        have := congrArg (fun μ => μ Bset) (hlawA.trans hlaw.symm)
        simpa [Measure.map_apply hZm hBm] using this
      rw [ProbabilityTheory.cond_apply hAm] at h1
      calc P (A ∩ s81s_pairVec G ts ys ⁻¹' Bset)
          = P A * ((P A)⁻¹ * P (A ∩ s81s_pairVec G ts ys ⁻¹' Bset)) := by
            rw [← mul_assoc, ENNReal.mul_inv_cancel hP0 (measure_ne_top _ _), one_mul]
        _ = P A * P (s81s_pairVec G ts ys ⁻¹' Bset) := by rw [h1]
  · obtain ⟨ω₀, h1, h2⟩ := (hG.sigma_traceClass.and hG.sigma_entry_int).exists
    exact s81s_covMat_psd ts hts ys h1 h2

end VecIndep

end HRS.Whole.S81S
