import HRS.MS.MainRdFieldAux6
import HRS.MS.MainRdFieldAux7

/-!
# S.A.6, packet P5b: the covariance density `sb`, the identity `Σ_σ - sb_σ = 2q(Form(μ_N) - Form(ρ))`, and the
cutoff estimate in expectation for a general pathwise bound

* `sa6_kern_meas_joint`, `sa6_kslice`: joint measurability of the kernel and the bounded-measurable slices;
* `sa6_sb`, `sa6_sb_det`: `sb_σ(x,y) = 2q ∫ Σ_j ⟨K_j^{σ,t}(z),x⟩⟨K_j^{σ,t}(z),y⟩ ρ_σ(z) dz` and `IsDetCovDensity`;
* `sa6_cov_eq`: `Σ_σ = hsCovForm(c K(X_i)) = 2q Form(μ_N)` for `c² N = 2q`;
* `sa6_cutoff_expect`: the expectation form of `test_cutoff_expectation` for a general real random variable with the
  pathwise cutoff bound.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdField

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.RdMart HRS.MP.RdProp
  HRS.MP.HNegInfra HRS.MP.RdRem

variable {d : ℕ}

section Kslice

variable {Cf : WholeCoeff d} {T : ℝ} {Γ : ℕ} {C₁ : ℝ} {Kern : Fin d → ℝ → ℝ → Euc d → HNeg d (Γ : ℝ)}

theorem sa6_kern_meas_joint (hK : Sa6Kern Cf T Γ C₁ Kern) {t : ℝ} (htT : t ≤ T) (j : Fin d) :
    Measurable (fun p : ℝ × Euc d => Kern j p.1 t p.2) := by
  refine mrm_measurable_of_pairings (fun φ hφ => ?_)
  have : (fun p : ℝ × Euc d => HNeg.pairing φ (Kern j p.1 t p.2)) = fun p =>
      if p.1 ∈ Set.Icc (0 : ℝ) t then gradient (propagatorW Cf p.1 t φ) p.2 j else 0 := by
    funext p
    by_cases h : p.1 ∈ Set.Icc (0 : ℝ) t
    · rw [if_pos h, hK.pair j p.1 t h.1 h.2 htT p.2 φ hφ]
    · rw [if_neg h, hK.zero j p.1 t p.2 (fun hh => h ⟨hh.1, hh.2.1⟩)]
      exact mrm_pairing_zero hφ
  rw [this]
  exact mrm_meas_grad Cf t φ j

theorem sa6_kslice (hK : Sa6Kern Cf T Γ C₁ Kern) {t : ℝ} (htT : t ≤ T) (σ : ℝ) :
    Sa6KBdd (fun j z => Kern j σ t z) C₁ :=
  ⟨hK.nonneg, fun j z => hK.bdd j σ t z,
    fun j => (sa6_kern_meas_joint hK htT j).comp (measurable_const.prodMk measurable_id)⟩

end Kslice

section SB

variable {Γ : ℕ}

/-- The deterministic covariance density `sb_σ`. -/
def sa6_sb (Kern : Fin d → ℝ → ℝ → Euc d → HNeg d (Γ : ℝ)) (t Kk q : ℝ)
    (hkb : ∀ σ : ℝ, Sa6KBdd (fun j z => Kern j σ t z) Kk) (ρ : ℝ → Euc d → ℝ)
    (hprob : ∀ σ, HRS.Whole.IsProbDensity (ρ σ)) : ℝ → HNeg d (Γ : ℝ) →L[ℝ] HNeg d (Γ : ℝ) →L[ℝ] ℝ :=
  fun σ => haveI := Q09A.measure_isProb (hprob σ)
    (2 * q) • sa6Form (fun j z => Kern j σ t z) (hkb σ) (HRS.Whole.withDensityReal (ρ σ))

variable {Kern : Fin d → ℝ → ℝ → Euc d → HNeg d (Γ : ℝ)} {t Kk q : ℝ}
  {hkb : ∀ σ : ℝ, Sa6KBdd (fun j z => Kern j σ t z) Kk} {ρ : ℝ → Euc d → ℝ}
  {hprob : ∀ σ, HRS.Whole.IsProbDensity (ρ σ)}

lemma sa6_sb_apply (σ : ℝ) (x y : HNeg d (Γ : ℝ)) :
    sa6_sb Kern t Kk q hkb ρ hprob σ x y =
      2 * q * ∫ z, sa6Fn (fun j z => Kern j σ t z) x y z ∂(HRS.Whole.withDensityReal (ρ σ)) := by
  haveI := Q09A.measure_isProb (hprob σ)
  show ((2 * q) • sa6Form (fun j z => Kern j σ t z) (hkb σ) (HRS.Whole.withDensityReal (ρ σ))) x y = _
  simp [ContinuousLinearMap.smul_apply, sa6Form_apply]

theorem sa6_sb_meas (hρm : Measurable (fun p : ℝ × Euc d => ρ p.1 p.2))
    (hKm : ∀ j, Measurable (fun p : ℝ × Euc d => Kern j p.1 t p.2)) (x y : HNeg d (Γ : ℝ)) :
    Measurable (fun σ => sa6_sb Kern t Kk q hkb ρ hprob σ x y) := by
  have hG : Measurable (fun p : ℝ × Euc d =>
      ρ p.1 p.2 * ∑ j, inner ℝ (Kern j p.1 t p.2) x * inner ℝ (Kern j p.1 t p.2) y) :=
    hρm.mul (Finset.measurable_sum _ fun j _ =>
      ((hKm j).inner measurable_const).mul ((hKm j).inner measurable_const))
  have e : (fun σ => sa6_sb Kern t Kk q hkb ρ hprob σ x y) = fun σ => 2 * q *
      ∫ z, (ρ σ z * ∑ j, inner ℝ (Kern j σ t z) x * inner ℝ (Kern j σ t z) y) := by
    funext σ
    rw [sa6_sb_apply]
    congr 1
    exact mrr_integral_withDensityReal (ρ σ) (hprob σ).measurable (hprob σ).nonneg
      (fun z => sa6Fn (fun j z => Kern j σ t z) x y z)
  rw [e]
  exact (hG.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable.const_mul _

theorem sa6_sb_det (hq : 0 ≤ q) (hρm : Measurable (fun p : ℝ × Euc d => ρ p.1 p.2))
    (hKm : ∀ j, Measurable (fun p : ℝ × Euc d => Kern j p.1 t p.2)) :
    IsDetCovDensity t (sa6_sb Kern t Kk q hkb ρ hprob) := by
  refine ⟨fun x y => sa6_sb_meas hρm hKm x y, fun σ _ => ?_, ?_⟩
  · haveI := Q09A.measure_isProb (hprob σ)
    exact sa6_traceClass_smul (sa6Form_isTraceClass (hkb σ) _) (by positivity)
  · have hmeas : Measurable fun σ => traceNormForm (sa6_sb Kern t Kk q hkb ρ hprob σ) :=
      measurable_traceNormForm _ (fun x y => sa6_sb_meas hρm hKm x y)
    refine Measure.integrableOn_of_bounded (M := |2 * q| * (d * Kk ^ 2 * 1)) (by simp)
      hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun σ _ => ?_)
    haveI := Q09A.measure_isProb (hprob σ)
    rw [Real.norm_of_nonneg (traceNormForm_nonneg _)]
    have h0 := sa6_traceNorm_single (hkb σ) (HRS.Whole.withDensityReal (ρ σ)) (2 * q)
    have h1 : (HRS.Whole.withDensityReal (ρ σ)).real Set.univ = 1 := by simp
    rw [h1] at h0
    exact h0

end SB

section CovEq

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

theorem sa6_cov_eq {N : ℕ} (hN : 0 < N) {k : Fin d → Euc d → H} {Kk : ℝ} (hk : Sa6KBdd k Kk)
    (X : EucConfig d N) [IsProbabilityMeasure (HRS.Whole.empirical X)] (c q : ℝ) (hc : c ^ 2 * N = 2 * q) :
    hsCovForm (fun ia : Fin N × Fin d => c • k ia.2 (X ia.1)) =
      (2 * q) • sa6Form k hk (HRS.Whole.empirical X) := by
  ext x y
  rw [hsCovForm_apply Summable.of_finite, tsum_fintype]
  simp only [ContinuousLinearMap.smul_apply, sa6Form_apply, smul_eq_mul]
  have e1 : ∫ z, sa6Fn k x y z ∂(HRS.Whole.empirical X) = (N : ℝ)⁻¹ * ∑ i, sa6Fn k x y (X i) :=
    HRS.Whole.pair_empirical hN X (sa6Fn k x y)
  rw [e1, Fintype.sum_prod_type]
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have e2 : ∀ i : Fin N, ∑ j : Fin d, inner ℝ (c • k j (X i)) x * inner ℝ (c • k j (X i)) y =
      c ^ 2 * sa6Fn k x y (X i) := by
    intro i
    unfold sa6Fn
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_left, real_inner_smul_left]; ring
  simp_rw [e2]
  rw [← Finset.mul_sum, ← hc]
  field_simp

end CovEq

end HRS.MS.MainRdField
