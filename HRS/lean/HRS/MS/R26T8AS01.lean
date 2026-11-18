import HRS.MS.R26T8AS00

/-!
# S8.2 observed-time layer, packet T8A.S01: the Itô integral as a bounded linear map on the closed span

For a fixed horizon `b ≥ 0`, the progressive integrands form a real vector space `r26t8a_s01_mod`.  The embedding
`H ↦ embL2 H b` is linear, and `H ↦ (itoIntegral H b)` is linear as an `L²(P)` valued map.  The Gram identity
`IsItoIntegral.inner_eq` shows that both maps have the same norms, so the Itô map factors through the kernel of the
embedding, is an isometry on the span, and extends by continuity to the closed span `r26t8a_progSpan`.
No new stochastic integral is constructed.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS

/-- the progressive `L²` integrands as a real vector space -/
def r26t8a_s01_mod {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I] (P : Measure Omega)
    (F : Filtration ℝ mOmega) : Submodule ℝ (ℝ → Omega → I → ℝ) where
  carrier := {H | IsProgressiveL2 P F H}
  zero_mem' := ⟨isProgressive_const F (0 : I → ℝ), fun T => by simp [sqIntegralOn]⟩
  add_mem' := fun hH hH' => hH.add hH'
  smul_mem' := fun c _ hH => hH.smul c

theorem r26t8a_s01_prog {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I] (P : Measure Omega)
    (F : Filtration ℝ mOmega) (H : r26t8a_s01_mod (I := I) P F) :
    IsProgressiveL2 P F (H : ℝ → Omega → I → ℝ) := H.2

/-- the embedding of the progressive integrands into `L²([0,b] × Ω; ℝ^I)` -/
def r26t8a_s01_E {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I] (P : Measure Omega)
    [IsProbabilityMeasure P] (F : Filtration ℝ mOmega) (b : ℝ) :
    r26t8a_s01_mod (I := I) P F →ₗ[ℝ] Lp (EuclideanSpace ℝ I) 2 (HRS.tsMeasure P b) where
  toFun H := HRS.embL2 (r26t8a_s01_prog P F H) b
  map_add' H H' := HRS.embL2_add (r26t8a_s01_prog P F H) (r26t8a_s01_prog P F H') b
  map_smul' c H := HRS.embL2_smul (r26t8a_s01_prog P F H) c b

/-- the Itô integral at time `b`, as a linear map into `L²(P)` -/
def r26t8a_s01_L {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I] (P : Measure Omega)
    [IsProbabilityMeasure P] (F : Filtration ℝ mOmega) (W : ℝ≥0 → Omega → I → ℝ)
    (hW : IsBrownianFiltration P F W) (b : ℝ) :
    r26t8a_s01_mod (I := I) P F →ₗ[ℝ] Lp ℝ 2 P where
  toFun H := (HRS.memLp_two_itoIntegral hW (r26t8a_s01_prog P F H) b).toLp
    (HRS.itoIntegral P F W H.1 b)
  map_add' H H' := by
    rw [← MemLp.toLp_add (HRS.memLp_two_itoIntegral hW (r26t8a_s01_prog P F H) b)
      (HRS.memLp_two_itoIntegral hW (r26t8a_s01_prog P F H') b)]
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [HRS.itoIntegral_add hW (r26t8a_s01_prog P F H) (r26t8a_s01_prog P F H')] with s hs
    exact hs b
  map_smul' c H := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul c
      (HRS.memLp_two_itoIntegral hW (r26t8a_s01_prog P F H) b)]
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [HRS.itoIntegral_smul hW (r26t8a_s01_prog P F H) c] with s hs
    show HRS.itoIntegral P F W (fun u w => c • H.1 u w) b s = c * HRS.itoIntegral P F W H.1 b s
    exact hs b

/-- the Gram identity: the Itô map and the embedding have the same norm -/
theorem r26t8a_s01_norm {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I] (P : Measure Omega)
    [IsProbabilityMeasure P] (F : Filtration ℝ mOmega) (W : ℝ≥0 → Omega → I → ℝ)
    (hW : IsBrownianFiltration P F W) (b : ℝ) (hb : 0 ≤ b) (H : r26t8a_s01_mod (I := I) P F) :
    ‖r26t8a_s01_L P F W hW b H‖ = ‖r26t8a_s01_E P F b H‖ := by
  have hH := r26t8a_s01_prog P F H
  have h := HRS.IsItoIntegral.inner_eq hW hH hH (HRS.isItoIntegral_itoIntegral hW hH)
    (HRS.isItoIntegral_itoIntegral hW hH) hb
  have h2 : ‖r26t8a_s01_L P F W hW b H‖ ^ 2 = ‖r26t8a_s01_E P F b H‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    exact h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

theorem r26t8a_s01_ker_le {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I] (P : Measure Omega)
    [IsProbabilityMeasure P] (F : Filtration ℝ mOmega) (W : ℝ≥0 → Omega → I → ℝ)
    (hW : IsBrownianFiltration P F W) (b : ℝ) (hb : 0 ≤ b) :
    LinearMap.ker (r26t8a_s01_E (I := I) P F b) ≤ LinearMap.ker (r26t8a_s01_L P F W hW b) := by
  intro H hH
  rw [LinearMap.mem_ker] at hH ⊢
  have h := r26t8a_s01_norm P F W hW b hb H
  rw [hH, norm_zero] at h
  exact norm_eq_zero.1 h

/-- the Itô map on the range of the embedding -/
def r26t8a_s01_J0 {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I] (P : Measure Omega)
    [IsProbabilityMeasure P] (F : Filtration ℝ mOmega) (W : ℝ≥0 → Omega → I → ℝ)
    (hW : IsBrownianFiltration P F W) (b : ℝ) (hb : 0 ≤ b) :
    LinearMap.range (r26t8a_s01_E (I := I) P F b) →ₗ[ℝ] Lp ℝ 2 P :=
  ((LinearMap.ker (r26t8a_s01_E (I := I) P F b)).liftQ (r26t8a_s01_L P F W hW b)
    (r26t8a_s01_ker_le P F W hW b hb)) ∘ₗ
    (LinearMap.quotKerEquivRange (r26t8a_s01_E (I := I) P F b)).symm.toLinearMap

theorem r26t8a_s01_J0_apply {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I] (P : Measure Omega)
    [IsProbabilityMeasure P] (F : Filtration ℝ mOmega) (W : ℝ≥0 → Omega → I → ℝ)
    (hW : IsBrownianFiltration P F W) (b : ℝ) (hb : 0 ≤ b) (H : r26t8a_s01_mod (I := I) P F) :
    r26t8a_s01_J0 P F W hW b hb ⟨r26t8a_s01_E P F b H, ⟨H, rfl⟩⟩ = r26t8a_s01_L P F W hW b H := by
  unfold r26t8a_s01_J0
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [LinearMap.quotKerEquivRange_symm_apply_image (r26t8a_s01_E (I := I) P F b) H ⟨H, rfl⟩]
  rfl

theorem r26t8a_s01_J0_norm {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I] (P : Measure Omega)
    [IsProbabilityMeasure P] (F : Filtration ℝ mOmega) (W : ℝ≥0 → Omega → I → ℝ)
    (hW : IsBrownianFiltration P F W) (b : ℝ) (hb : 0 ≤ b)
    (x : LinearMap.range (r26t8a_s01_E (I := I) P F b)) :
    ‖r26t8a_s01_J0 P F W hW b hb x‖ ≤ 1 * ‖x‖ := by
  rcases x with ⟨_, H, rfl⟩
  rw [r26t8a_s01_J0_apply, one_mul, r26t8a_s01_norm P F W hW b hb H]
  exact le_rfl

/-- the Itô map on the range, as a continuous linear map -/
def r26t8a_s01_J1 {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I] (P : Measure Omega)
    [IsProbabilityMeasure P] (F : Filtration ℝ mOmega) (W : ℝ≥0 → Omega → I → ℝ)
    (hW : IsBrownianFiltration P F W) (b : ℝ) (hb : 0 ≤ b) :
    LinearMap.range (r26t8a_s01_E (I := I) P F b) →L[ℝ] Lp ℝ 2 P :=
  LinearMap.mkContinuous (r26t8a_s01_J0 P F W hW b hb) 1
    (fun x => r26t8a_s01_J0_norm P F W hW b hb x)

/-- the range of the embedding lies in the closed span -/
theorem r26t8a_s01_mem {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I] (P : Measure Omega)
    [IsProbabilityMeasure P] (F : Filtration ℝ mOmega) (b : ℝ)
    (x : LinearMap.range (r26t8a_s01_E (I := I) P F b)) :
    (x : Lp (EuclideanSpace ℝ I) 2 (HRS.tsMeasure P b)) ∈ r26t8a_progSpan (I := I) P F b := by
  rcases x with ⟨_, H, rfl⟩
  exact Submodule.le_topologicalClosure _
    (Submodule.subset_span ⟨(H : ℝ → Omega → I → ℝ), r26t8a_s01_prog P F H, rfl⟩)

/-- the inclusion of the range into the closed span, as a continuous linear map -/
def r26t8a_s01_e {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I] (P : Measure Omega)
    [IsProbabilityMeasure P] (F : Filtration ℝ mOmega) (b : ℝ) :
    LinearMap.range (r26t8a_s01_E (I := I) P F b) →L[ℝ] r26t8a_progSpan (I := I) P F b :=
  LinearMap.mkContinuous
    (LinearMap.codRestrict (r26t8a_progSpan (I := I) P F b)
      (LinearMap.range (r26t8a_s01_E (I := I) P F b)).subtype
      (fun x => r26t8a_s01_mem P F b x)) 1
    (fun x => by rw [one_mul]; exact le_rfl)

theorem r26t8a_s01_e_norm {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I] (P : Measure Omega)
    [IsProbabilityMeasure P] (F : Filtration ℝ mOmega) (b : ℝ)
    (x : LinearMap.range (r26t8a_s01_E (I := I) P F b)) :
    ‖r26t8a_s01_e (I := I) P F b x‖ = ‖x‖ := rfl

/-- the range of the inclusion is dense in the closed span -/
theorem r26t8a_s01_dense {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I] (P : Measure Omega)
    [IsProbabilityMeasure P] (F : Filtration ℝ mOmega) (b : ℝ) :
    DenseRange (r26t8a_s01_e (I := I) P F b) := by
  have hsub : r26t8a_progSpan (I := I) P F b ≤
      (LinearMap.range (r26t8a_s01_E (I := I) P F b)).topologicalClosure := by
    unfold r26t8a_progSpan
    refine Submodule.topologicalClosure_mono (Submodule.span_le.2 ?_)
    rintro v ⟨H, hH, rfl⟩
    exact ⟨⟨H, hH⟩, rfl⟩
  rw [DenseRange, Topology.IsInducing.subtypeVal.dense_iff]
  intro y
  have hy := hsub y.2
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hy
  refine closure_mono ?_ hy
  intro z hz
  exact ⟨r26t8a_s01_e (I := I) P F b ⟨z, hz⟩, ⟨⟨z, hz⟩, rfl⟩, rfl⟩

/-- the Itô integral is a bounded linear map on the closed span of the progressive embeddings -/
theorem r26t8a_ito_continuousLinear {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I]
    (P : Measure Omega) [IsProbabilityMeasure P] (F : Filtration ℝ mOmega)
    (W : ℝ≥0 → Omega → I → ℝ) (hW : IsBrownianFiltration P F W) (b : ℝ) (hb : 0 ≤ b) :
    ∃ J : r26t8a_progSpan (I := I) P F b →L[ℝ] Lp ℝ 2 P, ‖J‖ ≤ 1 ∧
      ∀ (H : ℝ → Omega → I → ℝ) (hH : IsProgressiveL2 P F H),
        J (r26t8a_progEmbed P F b H hH) =
          (HRS.memLp_two_itoIntegral hW hH b).toLp (itoIntegral P F W H b) := by
  have hdense := r26t8a_s01_dense (I := I) P F b
  have hunif : IsUniformInducing (r26t8a_s01_e (I := I) P F b) :=
    (AddMonoidHomClass.isometry_of_norm (r26t8a_s01_e (I := I) P F b)
      (fun x => r26t8a_s01_e_norm P F b x)).isUniformInducing
  refine ⟨ContinuousLinearMap.extend (r26t8a_s01_J1 P F W hW b hb) (r26t8a_s01_e (I := I) P F b), ?_, ?_⟩
  · have hJ1 : ‖r26t8a_s01_J1 P F W hW b hb‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x =>
        r26t8a_s01_J0_norm P F W hW b hb x)
    have h1 := ContinuousLinearMap.opNorm_extend_le (r26t8a_s01_J1 P F W hW b hb) hdense
      (N := 1) (fun x => by simp only [NNReal.coe_one, one_mul, r26t8a_s01_e_norm, le_refl])
    exact h1.trans (by simp only [NNReal.coe_one, one_mul]; exact hJ1)
  · intro H hH
    have hx : r26t8a_progEmbed (I := I) P F b H hH = r26t8a_s01_e (I := I) P F b
        ⟨r26t8a_s01_E P F b ⟨H, hH⟩, ⟨⟨H, hH⟩, rfl⟩⟩ := Subtype.ext rfl
    rw [hx, ContinuousLinearMap.extend_eq (h_dense := hdense) (h_e := hunif)]
    exact r26t8a_s01_J0_apply P F W hW b hb ⟨H, hH⟩

end HRS.MS.R26T8A

end
