import HRS.MS.MainRdFieldAux9

/-!
# S.A.6, packet P5d: the Gaussian `ν_G` has the covariance `∫ sb`

From `IsLinearFieldNoiseRd` (covariance only on the smooth tests, `noiseCovW`) to
`IsGaussianWithIntegratedCov t sb νG` (covariance form on all of `H^{-Γ}`): the Riesz representatives of the smooth tests
span a dense subspace (`sa6_dense_J`), both covariance forms are continuous bilinear forms (`sa6_Sint` for the integrated
form), and they agree on the representatives (`noiseCovW`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdField

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.RdMart HRS.MP.RdProp
  HRS.MP.HNegInfra HRS.MP.RdRem

variable {d : ℕ}

lemma sa6_dense_J (Γ : ℝ) :
    Dense (Submodule.span ℝ (Set.range (fun φ : rpk_Tst d Γ => rpk_J Γ φ)) : Set (HNeg d Γ)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro F hF
  refine hneg_eq_zero_of_pairing_zero F (fun φ hφ => ?_)
  have h1 : rpk_J Γ ⟨φ, hφ⟩ ∈ Submodule.span ℝ (Set.range (fun φ : rpk_Tst d Γ => rpk_J Γ φ)) :=
    Submodule.subset_span ⟨⟨φ, hφ⟩, rfl⟩
  have h2 := Submodule.inner_right_of_mem_orthogonal h1 hF
  rwa [rpk_J_inner] at h2

/-- Two continuous bilinear forms on `H^{-Γ}` that agree on the Riesz representatives of the smooth tests agree. -/
lemma sa6_forms_ext (Γ : ℝ) (A B : HNeg d Γ →L[ℝ] HNeg d Γ →L[ℝ] ℝ)
    (h : ∀ φ ψ : rpk_Tst d Γ, A (rpk_J Γ φ) (rpk_J Γ ψ) = B (rpk_J Γ φ) (rpk_J Γ ψ)) : A = B := by
  have hd := sa6_dense_J (d := d) Γ
  have h1 : ∀ ψ : rpk_Tst d Γ, ∀ x, A x (rpk_J Γ ψ) = B x (rpk_J Γ ψ) := by
    intro ψ
    have : A.flip (rpk_J Γ ψ) = B.flip (rpk_J Γ ψ) :=
      ContinuousLinearMap.ext_on hd (fun x hx => by
        obtain ⟨φ, rfl⟩ := hx
        exact h φ ψ)
    intro x
    exact congrArg (fun f => f x) this
  ext x y
  have : A x = B x := ContinuousLinearMap.ext_on hd (fun y hy => by
    obtain ⟨ψ, rfl⟩ := hy
    exact h1 ψ x)
  exact congrArg (fun f => f y) this

lemma sa6_cov_apply {Γ : ℝ} (ν : Measure (HNeg d Γ)) (hν : IsCenteredGaussian ν)
    (x y : HNeg d Γ) :
    covarianceBilin ν x y = ∫ z, inner ℝ x z * inner ℝ y z ∂ν := by
  haveI : IsGaussian ν := hν.1
  have hmem : MemLp id 2 ν := IsGaussian.memLp_two_id
  have hmean : ∫ z, id z ∂ν = 0 := by
    have hi : Integrable (id : HNeg d Γ → HNeg d Γ) ν := hmem.integrable one_le_two
    refine ext_inner_left ℝ (fun v => ?_)
    rw [inner_zero_right]
    have := integral_inner (𝕜 := ℝ) (μ := ν) (f := id) hi v
    rw [← this]
    simpa using hν.2 (innerSL ℝ v)
  rw [covarianceBilin_apply hmem]
  have hmean' : ∫ z, z ∂ν = 0 := hmean
  simp only [hmean', sub_zero, id]

section Gamma

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- The integrated covariance form `∫_{[0,t]} sb_σ dσ` as a continuous bilinear form. -/
def sa6_Sint (sb : ℝ → H →L[ℝ] H →L[ℝ] ℝ) (t B : ℝ) (ht : 0 ≤ t)
    (hm : ∀ x y, Measurable fun σ => sb σ x y) (hb : ∀ σ x y, |sb σ x y| ≤ B * ‖x‖ * ‖y‖) :
    H →L[ℝ] H →L[ℝ] ℝ :=
  have hi : ∀ x y, IntegrableOn (fun σ => sb σ x y) (Set.Icc 0 t) := fun x y =>
    Measure.integrableOn_of_bounded (M := B * ‖x‖ * ‖y‖) (by simp [Real.volume_Icc])
      (hm x y).aestronglyMeasurable
      (ae_of_all _ fun σ => by simpa [Real.norm_eq_abs] using hb σ x y)
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun x y => ∫ σ in Set.Icc 0 t, sb σ x y)
      (fun x x' y => by
        simp only [map_add, ContinuousLinearMap.add_apply]
        exact integral_add (hi x y) (hi x' y))
      (fun c x y => by
        simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
        exact integral_const_mul c _)
      (fun x y y' => by
        simp only [map_add]
        exact integral_add (hi x y) (hi x y'))
      (fun c x y => by
        simp only [map_smul, smul_eq_mul]
        exact integral_const_mul c _))
    (|t| * |B|) (fun x y => by
      show ‖∫ σ in Set.Icc 0 t, sb σ x y‖ ≤ _
      have := norm_integral_le_of_norm_le_const (μ := volume.restrict (Set.Icc (0 : ℝ) t))
        (f := fun σ => sb σ x y) (C := |B| * ‖x‖ * ‖y‖)
        (ae_of_all _ fun σ => by
          simpa [Real.norm_eq_abs] using (hb σ x y).trans
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self B) (norm_nonneg _))
              (norm_nonneg _)))
      have hvol : (volume.restrict (Set.Icc (0 : ℝ) t)).real Set.univ = t := by
        simp [Measure.real, Real.volume_Icc, ht]
      refine this.trans (le_of_eq ?_)
      rw [hvol, abs_of_nonneg ht]; ring)

lemma sa6_Sint_apply (sb : ℝ → H →L[ℝ] H →L[ℝ] ℝ) (t B : ℝ) (ht : 0 ≤ t)
    (hm : ∀ x y, Measurable fun σ => sb σ x y) (hb : ∀ σ x y, |sb σ x y| ≤ B * ‖x‖ * ‖y‖)
    (x y : H) : sa6_Sint sb t B ht hm hb x y = ∫ σ in Set.Icc 0 t, sb σ x y := rfl

end Gamma

section GammaConcrete

variable {S : WholeMainData d} {N : ℕ} {Γ : ℕ} {Kk : ℝ}
  {Kern : Fin d → ℝ → ℝ → Euc d → HNeg d (Γ : ℝ)}

lemma sa6_sb_bound {t q : ℝ} (hq : 0 ≤ q) {hkb : ∀ σ : ℝ, Sa6KBdd (fun j z => Kern j σ t z) Kk}
    {ρ : ℝ → Euc d → ℝ} {hprob : ∀ σ, HRS.Whole.IsProbDensity (ρ σ)} (σ : ℝ) (x y : HNeg d (Γ : ℝ)) :
    |sa6_sb Kern t Kk q hkb ρ hprob σ x y| ≤ (2 * q * (d * Kk ^ 2)) * ‖x‖ * ‖y‖ := by
  haveI := Q09A.measure_isProb (hprob σ)
  rw [sa6_sb_apply, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * q)]
  have := norm_integral_le_of_norm_le_const (μ := HRS.Whole.withDensityReal (ρ σ))
    (f := sa6Fn (fun j z => Kern j σ t z) x y) (C := d * Kk ^ 2 * (‖x‖ * ‖y‖))
    (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using sa6Fn_abs_le (hkb σ) x y z)
  have h1 : (HRS.Whole.withDensityReal (ρ σ)).real Set.univ = 1 := by simp
  simp only [Real.norm_eq_abs] at this
  rw [h1, mul_one] at this
  calc 2 * q * |∫ z, sa6Fn (fun j z => Kern j σ t z) x y z ∂HRS.Whole.withDensityReal (ρ σ)|
      ≤ 2 * q * (d * Kk ^ 2 * (‖x‖ * ‖y‖)) := mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

theorem sa6_gamma (hK : Sa6Kern (S.coeff N) S.T Γ Kk Kern) {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ S.T)
    (hq : 0 ≤ S.qN N)
    (hkb : ∀ σ : ℝ, Sa6KBdd (fun j z => Kern j σ t z) Kk)
    (hprob : ∀ σ : ℝ, HRS.Whole.IsProbDensity (S.ρ N (mrrClamp S.T σ)))
    (hρm : Measurable (fun p : ℝ × Euc d => S.ρ N (mrrClamp S.T p.1) p.2))
    {νG : Measure (HNeg d (Γ : ℝ))} (hν : IsLinearFieldNoiseRd (S.coeff N) (S.qN N) t Γ νG) :
    IsGaussianWithIntegratedCov t
      (sa6_sb Kern t Kk (S.qN N) hkb (fun σ => S.ρ N (mrrClamp S.T σ)) hprob) νG := by
  have hT : 0 ≤ S.T := S.hT.le
  have hKm : ∀ j, Measurable (fun p : ℝ × Euc d => Kern j p.1 t p.2) :=
    fun j => sa6_kern_meas_joint hK htT j
  set sb := sa6_sb Kern t Kk (S.qN N) hkb (fun σ => S.ρ N (mrrClamp S.T σ)) hprob with hsbdef
  obtain ⟨hp, hc, hcov⟩ := hν
  refine ⟨hp, hc, fun x y => ?_⟩
  set Sint := sa6_Sint sb t (2 * S.qN N * (d * Kk ^ 2)) ht (fun x y => sa6_sb_meas hρm hKm x y)
    (fun σ x y => sa6_sb_bound hq σ x y) with hSint
  have hform : covarianceBilin νG = Sint := by
    refine sa6_forms_ext (Γ : ℝ) _ _ (fun φ ψ => ?_)
    rw [hSint, sa6_Sint_apply, sa6_cov_apply νG hc]
    have h1 : ∫ z, inner ℝ (rpk_J (Γ : ℝ) φ) z * inner ℝ (rpk_J (Γ : ℝ) ψ) z ∂νG =
        noiseCovW (S.coeff N) (S.qN N) t t φ.1 ψ.1 := by
      simp_rw [rpk_J_inner]
      exact hcov φ.1 ψ.1 φ.2 ψ.2
    rw [h1]
    unfold noiseCovW
    rw [min_self, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
    have hσS : σ ∈ Set.Icc (0 : ℝ) S.T := ⟨hσ.1, hσ.2.trans htT⟩
    have hcl : mrrClamp S.T σ = σ := mrrClamp_of_mem hσS
    have hpσ : HRS.Whole.IsProbDensity (S.ρ N σ) := hcl ▸ hprob σ
    have hin : ∀ (F : HNeg d (Γ : ℝ)) (θ : rpk_Tst d (Γ : ℝ)),
        inner ℝ F (rpk_J (Γ : ℝ) θ) = HNeg.pairing θ.1 F := fun F θ => by
      rw [real_inner_comm, rpk_J_inner]
    rw [hsbdef, sa6_sb_apply, hcl, mrr_integral_withDensityReal (S.ρ N σ) hpσ.measurable hpσ.nonneg]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    have hsum : sa6Fn (fun j z => Kern j σ t z) (rpk_J (Γ : ℝ) φ) (rpk_J (Γ : ℝ) ψ) z =
        inner ℝ (gradient (propagatorW (S.coeff N) σ t φ.1) z)
          (gradient (propagatorW (S.coeff N) σ t ψ.1) z) := by
      unfold sa6Fn
      rw [HRS.Whole.Q09B.q09b_inner_euc]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hin, hK.pair j σ t hσ.1 hσ.2 htT z φ.1 φ.2, hK.pair j σ t hσ.1 hσ.2 htT z ψ.1 ψ.2]
    beta_reduce
    rw [hsum]
    exact mul_comm _ _
  exact (congrArg (fun A => A x y) hform).trans (sa6_Sint_apply _ _ _ ht _ _ x y)

end GammaConcrete

end HRS.MS.MainRdField
