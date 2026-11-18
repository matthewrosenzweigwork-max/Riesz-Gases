import HRS.MS.R2SeAux49
import HRS.MS.R2ObsAux1

/-!
# S9.10 family row, packet 2: transport helpers for a Hilbert space `H` with an orthonormal basis

Worker S910, namespace `HRS.MS.R2Obs`.  `Ψ = e.repr : H ≃ₗᵢ ℓ²(ℕ)` replaces the isometry `s45_Psi` of S9.9.  For the features
`ψ_j` (an `IsSummableFeatureFamily (J1 d)`):

* `s910_env`: the S9.9 environment (thermal data, the static bundle for every `N ≥ 2`, the correctors);
* `s910_ell_eq`, `s910_ell_norm`, `s910_ell_cont`: `r2EllH e ψ … x = Ψ⁻¹ (ellv x)`, bounded and continuous in `x`;
* `s910_field_eq`: `r2FieldH e ψ P X = Ψ⁻¹ (featureVec ψ (HRS.Whole.firstMarginal P) X)` for exchangeable `P`;
* `s910_gauss_symm`, `s910_cov_map`: the Gaussian on `ℓ²` pulled back to `H`;
* `s910_tensor`: the Bochner projective tensor of a bounded continuous map `Euc d → B`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace HRS.MS.R2Obs

open S99 S45 HRS HRS.Whole
open HRS (Euc cbNorm MemCb)

universe u

variable {d : ℕ} {s : ℝ} {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- The S9.9 environment of a summable feature family. -/
structure Env (d : ℕ) (s a β γ : ℝ) (ψ : ℕ → Euc d → ℝ) where
  C : ℝ
  c : ℝ
  BU : ℝ
  Cs : ℝ
  hT : S45.ThermalData d s a β C c BU
  hS : ∀ N : ℕ, 2 ≤ N → S46.S46Static d s a β γ Cs N
  hφ : IsSummableFeatureFamily (J1 d) ψ
  F : FamData d s a β γ ψ

theorem s910_env (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (hγ : 0 < γ) {ψ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily (J1 d) ψ) :
    Nonempty (Env d s a β γ ψ) := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  obtain ⟨C, c, BU, Cs, hT, -, hS⟩ := s99_env hd hs0 hs ha hβ hγ
  obtain ⟨F⟩ := s99_famData hd hs0 hsd ha hβ hγ hφ.1
  exact ⟨⟨C, c, BU, Cs, hT, hS, hφ, F⟩⟩

/-- The isometry `H ≃ ℓ²(ℕ)` of an orthonormal basis. -/
def s910_Psi (e : HilbertBasis ℕ ℝ H) : H ≃ₗᵢ[ℝ] SeqL2 := e.repr

theorem s910_Psi_coord (e : HilbertBasis ℕ ℝ H) (z : H) (j : ℕ) :
    SeqL2.coord (s910_Psi e z) j = inner ℝ (e j) z :=
  e.repr_apply_apply z j

theorem s910_Psi_symm_hasSum (e : HilbertBasis ℕ ℝ H) (z : SeqL2) :
    HasSum (fun j => SeqL2.coord z j • e j) ((s910_Psi e).symm z) :=
  e.hasSum_repr_symm z

section Ell

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a) (hβ : 0 < β) (hγ : 0 < γ)
  {ψ : ℕ → Euc d → ℝ} (E : Env d s a β γ ψ)

include hd hs0 hs ha hβ hγ E

theorem s910_ell_eq (e : HilbertBasis ℕ ℝ H) (x : Euc d) :
    r2EllH e ψ (rieszKernel d s) (thermalMeasure d s a β) γ x =
      (s910_Psi e).symm (ellv d s a β γ ψ x) := by
  have h := s910_Psi_symm_hasSum e (ellv d s a β γ ψ x)
  unfold r2EllH
  have : (fun j => responseRepW (rieszKernel d s) (thermalMeasure d s a β) γ (ψ j) x • e j) =
      fun j => SeqL2.coord (ellv d s a β γ ψ x) j • e j := funext fun j => by
    rw [s99_ellv_coord hd hs0 hs ha hβ hγ E.hT E.hφ E.F x j]; rfl
  rw [this]
  exact h.tsum_eq

theorem s910_ell_norm (e : HilbertBasis ℕ ℝ H) (x : Euc d) :
    ‖r2EllH e ψ (rieszKernel d s) (thermalMeasure d s a β) γ x‖ ≤ E.F.K * ∑' j, cbNorm (J1 d) (ψ j) := by
  rw [s910_ell_eq hd hs0 hs ha hβ hγ E e x, LinearIsometryEquiv.norm_map]
  exact s99_ellv_norm hd hs0 hs ha hβ hγ E.hT E.hφ E.F x

theorem s910_ell_cont (e : HilbertBasis ℕ ℝ H) :
    Continuous (r2EllH e ψ (rieszKernel d s) (thermalMeasure d s a β) γ) := by
  have : r2EllH e ψ (rieszKernel d s) (thermalMeasure d s a β) γ =
      fun x => (s910_Psi e).symm (ellv d s a β γ ψ x) := funext (s910_ell_eq hd hs0 hs ha hβ hγ E e)
  rw [this]
  exact (s910_Psi e).symm.continuous.comp (s99_ellv_cont hd hs0 hs ha hβ hγ E.hT E.hφ E.F)

end Ell

theorem s910_field_eq {N : ℕ} (hN : 1 ≤ N) (e : HilbertBasis ℕ ℝ H) {ψ : ℕ → Euc d → ℝ}
    (hφ : IsSummableFeatureFamily (J1 d) ψ) (P : Measure (EucConfig d N)) [IsProbabilityMeasure P]
    (hex : HRS.Whole.IsExchangeable P) (X : EucConfig d N) :
    r2FieldH e ψ P X = (s910_Psi e).symm (featureVec ψ (HRS.Whole.firstMarginal P) X) := by
  haveI : IsProbabilityMeasure (HRS.Whole.firstMarginal P) := s99_nu_prob hN
  have hme : HRS.Whole.meanEmpirical P = HRS.Whole.firstMarginal P := HRS.Whole.meanEmpirical_eq_firstMarginal P hex hN
  have h := s910_Psi_symm_hasSum e (featureVec ψ (HRS.Whole.firstMarginal P) X)
  have hm := s45_feature_memℓp hN hφ (ν := HRS.Whole.firstMarginal P) X
  unfold r2FieldH
  rw [hme]
  have : (fun j => (Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) (ψ j) - HRS.Whole.pair (HRS.Whole.firstMarginal P) (ψ j))) • e j) =
      fun j => SeqL2.coord (featureVec ψ (HRS.Whole.firstMarginal P) X) j • e j := funext fun j => by
    unfold featureVec
    rw [s45_coord_ofSeq hm j]
  rw [this]
  exact h.tsum_eq

theorem s910_gauss_symm (e : HilbertBasis ℕ ℝ H) {G' : Measure SeqL2} (hG : IsCenteredGaussian G') :
    IsCenteredGaussian (G'.map (s910_Psi e).symm) := by
  have hΨm : Measurable (s910_Psi e).symm := (s910_Psi e).symm.continuous.measurable
  have : IsGaussian G' := hG.1
  refine ⟨isGaussian_map_equiv (μ := G') (s910_Psi e).symm.toContinuousLinearEquiv, fun L => ?_⟩
  rw [integral_map hΨm.aemeasurable L.continuous.aestronglyMeasurable]
  have := hG.2 (L.comp (s910_Psi e).symm.toContinuousLinearEquiv.toContinuousLinearMap)
  simpa using this

theorem s910_cov_map (e : HilbertBasis ℕ ℝ H) {G' : Measure SeqL2} {c : ℕ → ℕ → ℝ}
    (hG : IsCenteredGaussianSeq G' c) (j k : ℕ) :
    Integrable (fun z : H => inner ℝ (e j) z * inner ℝ (e k) z) (G'.map (s910_Psi e).symm) ∧
      ∫ z, inner ℝ (e j) z * inner ℝ (e k) z ∂(G'.map (s910_Psi e).symm) = c j k := by
  have hΨm : Measurable (s910_Psi e).symm := (s910_Psi e).symm.continuous.measurable
  have hcm : Continuous fun z : H => inner ℝ (e j) z * inner ℝ (e k) z :=
    (continuous_const.inner continuous_id).mul (continuous_const.inner continuous_id)
  have hform : ∀ z : SeqL2, inner ℝ (e j) ((s910_Psi e).symm z) * inner ℝ (e k) ((s910_Psi e).symm z) =
      SeqL2.coord z j * SeqL2.coord z k := fun z => by
    rw [← s910_Psi_coord, ← s910_Psi_coord]; simp
  obtain ⟨hint, hval⟩ := hG.2 j k
  refine ⟨(integrable_map_measure hcm.aestronglyMeasurable hΨm.aemeasurable).2 ?_, ?_⟩
  · have : ((fun z : H => inner ℝ (e j) z * inner ℝ (e k) z) ∘ (s910_Psi e).symm) =
        fun z : SeqL2 => SeqL2.coord z j * SeqL2.coord z k := funext hform
    rw [this]
    exact hint
  · rw [integral_map hΨm.aemeasurable hcm.aestronglyMeasurable]
    simp_rw [hform]
    exact hval

theorem s910_tensor {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] (ℓ : Euc d → B) (hℓ : Continuous ℓ) {Cb : ℝ} (hC : ∀ x, ‖ℓ x‖ ≤ Cb) :
    ∃ K : projTensor B 3, ∀ T : B [×3]→L[ℝ] ℝ, (K : TensorDual B 3) T = ∫ x, T ![ℓ x, ℓ x, ℓ x] ∂μ := by
  have hasm : AEStronglyMeasurable ℓ μ := hℓ.aestronglyMeasurable
  have hint : Integrable (fun x => ‖ℓ x‖ * ‖ℓ x‖ * ‖ℓ x‖) μ := by
    refine Integrable.of_bound (C := Cb * Cb * Cb) ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact ((hℓ.norm.mul hℓ.norm).mul hℓ.norm).aestronglyMeasurable
    · have h0 : 0 ≤ ‖ℓ x‖ := norm_nonneg _
      have h1 := hC x
      have hC0 : 0 ≤ Cb := h0.trans h1
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      gcongr
  refine ⟨⟨HRS.MC.E213T.bochTensor3 μ ℓ ℓ ℓ, HRS.MC.E213T.bochTensor3_mem hasm hasm hasm hint⟩, fun T => ?_⟩
  exact HRS.MC.E213T.bochTensor3_apply hasm hasm hasm hint T

end HRS.MS.R2Obs

end
