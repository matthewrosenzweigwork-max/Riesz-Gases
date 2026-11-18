import HRS.MS.R2InterpAux43
import HRS.MS.R2InterpAux65
import HRS.MC.S7PIS2RS

/-!
# S10.2 (worker S102), part 44 (packet G6, core): removal of the projection from the cylindrical conclusions

Whole-space port of `S7PIG6_core`.  Inputs (all about the particle system, to be discharged by the moment packets M1-M3): the a.s. drift structure
`S102Drift` of `B_N` with an integrable total bound, a.s. continuity of `Y`, a uniform Lipschitz cumulative covariance path for `η_N`, and the
measurability of the path and of the initial propagation.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MC.Sec7.S7PIG6 HRS.MS.CovMeas HRS.Sec7

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}

set_option maxSynthPendingDepth 3 in
theorem s102_G6_core (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c) (hlin : S102Lin C m T) (hT : 0 < T)
    (s : ℝ) (μ : Measure (Euc d)) (γ : ℝ → Measure (OscPath d m T)) (hγp : ∀ u, IsProbabilityMeasure (γ u))
    {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → EucConfig d N)
    (Pj : ℕ → (OscPath d m T →L[ℝ] OscPath d m T)) (hP1 : ∀ L, ‖Pj L‖ ≤ 1)
    (hconv : ∀ w, Tendsto (fun L => Pj L w) atTop (𝓝 w))
    (hTconv : ∀ (j : ℕ) (v : TensorDual (OscPath d m T) j), v ∈ projTensor (OscPath d m T) j →
      Tendsto (fun L => tensorPow j (Pj L) v) atTop (𝓝 v))
    (hLP : S102LipProj γ Pj) {Φ : OscPath d m T → ℝ} (hΦ : MemCb 5 Φ)
    (Mb : Ω → ℝ → ℝ)
    (hdr : ∀ᵐ ζ ∂P, S102Drift C m T r Pw (fun u => r2QuadField s μ P X u ζ) (Mb ζ))
    (hMint : Integrable (fun ζ => ∫ u in Ioc 0 T, Mb ζ u) P)
    (hY : ∀ᵐ ζ ∂P, ContinuousOn (s102_Y C m T P X ζ) (Icc 0 T))
    (Vf : Ω → ℝ) (hVf : Integrable Vf P)
    (hJc : ∀ᵐ ζ ∂P, ∃ (Jc : ℝ → TensorDual (OscPath d m T) 2), Jc 0 = 0 ∧
      (∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T → IsR2JValue C m T (s102_etaf μ X ζ) (Ioc a b) (Jc b - Jc a)) ∧
      BoundedVariationOn Jc (Icc 0 T) ∧ (eVariationOn Jc (Icc 0 T)).toReal ≤ Vf ζ)
    (hzW : AEMeasurable (fun ζ => zetaPathW m T 0 P X ζ) P)
    (hy : AEMeasurable (fun ζ => s102_y0 C m T P X ζ) P)
    (hF : ∀ L, S102Concl C m T s μ γ P X Φ (Pj L)) :
    S102Concl C m T s μ γ P X Φ (ContinuousLinearMap.id ℝ (OscPath d m T)) := by
  classical
  unfold S102Concl at hF
  choose A J hA hJ hAR hJR hid using hF
  have hC0 : 0 ≤ cbNorm 5 Φ := HRS.MC.Sec7.S7PIL.S7PIL_cbNorm_nonneg hΦ 0
  have hKV0 : 0 ≤ s102_KV d r Pw c := s102_KV_nonneg d r Pw c
  -- the drift part
  have hAae : ∀ᵐ ζ ∂P, ∃ I, IsR2RS T (fun τ a b => fderiv ℝ (r2HeatFn γ Φ τ) (s102_Y C m T P X ζ τ)
      (r2DriftInc C m T (fun u => r2QuadField s μ P X u ζ) a b)) I ∧
      Tendsto (fun L => A L ζ) atTop (𝓝 I) ∧ ∀ L, |A L ζ| ≤ s102_KV d r Pw c * cbNorm 5 Φ *
        ∫ u in Ioc 0 T, Mb ζ u := by
    filter_upwards [hdr, hY, ae_all_iff.2 hAR] with ζ hb hYc hR
    obtain ⟨I, hI, -, IL, hIL, hILb, hlim⟩ := s102_RS_drift hP hD hlin hb hT γ hγp Pj hP1 hconv hLP hΦ _ hYc
    have hAeq : ∀ L, A L ζ = IL L := fun L =>
      HRS.MC.Sec7.S7PIS2.S7PIS2_RS_unique T hT _ _ _ ((s102_isR2RS_iff _ _ _).1 (hR L))
        ((s102_isR2RS_iff _ _ _).1 (hIL L))
    refine ⟨I, hI, ?_, fun L => ?_⟩
    · simpa only [hAeq] using hlim
    · rw [hAeq]; exact hILb L
  obtain ⟨hAint, hAlim, hAtend⟩ := S7PIG6_lim (P := P) A (fun L => (hA L).aestronglyMeasurable) _
    (hMint.const_mul (s102_KV d r Pw c * cbNorm 5 Φ))
    (hAae.mono fun ζ h => by obtain ⟨I, -, h1, h2⟩ := h; exact ⟨⟨I, h1⟩, h2⟩)
  -- the covariance part
  have hJae : ∀ᵐ ζ ∂P, ∃ I, IsR2RS T (fun τ a b => r2JPair C m T (s102_etaf μ X ζ) (Ioc a b)
      (iteratedFDeriv ℝ 2 (r2HeatFn γ Φ τ) (s102_Y C m T P X ζ τ))) I ∧
      Tendsto (fun L => J L ζ) atTop (𝓝 I) ∧ ∀ L, |J L ζ| ≤ cbNorm 5 Φ * Vf ζ := by
    filter_upwards [hJc, hY, ae_all_iff.2 hJR] with ζ hz hYc hR
    obtain ⟨Jc, hJc0, hJv, hBV, hVle⟩ := hz
    obtain ⟨I, hI, -, IL, hIL, hILb, hlim⟩ := s102_RS_J_bv C hT γ hγp Pj hP1 hconv hTconv hLP hΦ _ hYc
      (s102_etaf μ X ζ) Jc hJc0 hJv hBV
    have hAeq : ∀ L, J L ζ = IL L := fun L =>
      HRS.MC.Sec7.S7PIS2.S7PIS2_RS_unique T hT _ _ _ ((s102_isR2RS_iff _ _ _).1 (hR L))
        ((s102_isR2RS_iff _ _ _).1 (hIL L))
    refine ⟨I, hI, ?_, fun L => ?_⟩
    · simpa only [hAeq] using hlim
    · rw [hAeq]
      exact (hILb L).trans (mul_le_mul_of_nonneg_left hVle hC0)
  obtain ⟨hJint, hJlim, hJtend⟩ := S7PIG6_lim (P := P) J (fun L => (hJ L).aestronglyMeasurable) _
    (hVf.const_mul (cbNorm 5 Φ))
    (hJae.mono fun ζ h => by obtain ⟨I, -, h1, h2⟩ := h; exact ⟨⟨I, h1⟩, h2⟩)
  -- the identity: boundedness of `Φ`
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ x, |Φ x| ≤ K := by
    obtain ⟨K, hK⟩ := hΦ.2 0 (Nat.zero_le _)
    refine ⟨K, fun x => ?_⟩
    have := hK ⟨x, rfl⟩
    simpa [norm_iteratedFDeriv_zero] using this
  have hΦc : Continuous Φ := hΦ.1.continuous
  have hL1 : Tendsto (fun L => ∫ ζ, Φ (Pj L (zetaPathW m T 0 P X ζ)) ∂P) atTop
      (𝓝 (∫ ζ, Φ (zetaPathW m T 0 P X ζ) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => K) (fun L => ?_) (integrable_const K)
      (fun L => Eventually.of_forall fun ζ => ?_) (Eventually.of_forall fun ζ => ?_)
    · exact ((hΦc.comp (Pj L).continuous).measurable.comp_aemeasurable hzW).aestronglyMeasurable
    · simpa using hK _
    · exact (hΦc.tendsto _).comp (hconv _)
  have hF1 : Tendsto (fun L => ∫ ζ, r2HeatFn γ (fun w => Φ (Pj L w)) 0 (s102_y0 C m T P X ζ) ∂P) atTop
      (𝓝 (∫ ζ, r2HeatFn γ Φ 0 (s102_y0 C m T P X ζ) ∂P)) := by
    have := hγp 0
    have hcL : ∀ L, Continuous (r2HeatFn γ (fun w => Φ (Pj L w)) 0) := fun L =>
      S7PIG6_heat_cont (γ 0) (hΦc.comp (Pj L).continuous) K (fun x => hK _)
    refine tendsto_integral_of_dominated_convergence (fun _ => K) (fun L => ?_) (integrable_const K)
      (fun L => Eventually.of_forall fun ζ => ?_) (Eventually.of_forall fun ζ => ?_)
    · exact ((hcL L).measurable.comp_aemeasurable hy).aestronglyMeasurable
    · have := norm_integral_le_of_norm_le_const (μ := γ 0)
        (f := fun z => Φ (Pj L (s102_y0 C m T P X ζ + z))) (C := K)
        (Eventually.of_forall fun z => by simpa using hK _)
      simpa [r2HeatFn] using this
    · unfold r2HeatFn
      refine tendsto_integral_of_dominated_convergence (fun _ => K) (fun L => ?_) (integrable_const K)
        (fun L => Eventually.of_forall fun z => ?_) (Eventually.of_forall fun z => ?_)
      · exact (hΦc.comp ((Pj L).continuous.comp (continuous_const.add continuous_id))).aestronglyMeasurable
      · simpa using hK _
      · exact (hΦc.tendsto _).comp (hconv _)
  refine ⟨fun ζ => limUnder atTop (fun L => A L ζ), fun ζ => limUnder atTop (fun L => J L ζ),
    hAint, hJint, ?_, ?_, ?_⟩
  · filter_upwards [hAae, hAlim] with ζ h ht'
    obtain ⟨I, hI, ht, -⟩ := h
    rw [tendsto_nhds_unique ht' ht]
    exact hI
  · filter_upwards [hJae, hJlim] with ζ h ht'
    obtain ⟨I, hI, ht, -⟩ := h
    rw [tendsto_nhds_unique ht' ht]
    exact hI
  · have hfin : Tendsto (fun L => ∫ ζ, Φ (Pj L (zetaPathW m T 0 P X ζ)) ∂P) atTop
        (𝓝 (∫ ζ, r2HeatFn γ Φ 0 (s102_y0 C m T P X ζ) ∂P -
          (Real.sqrt N)⁻¹ * ∫ ζ, limUnder atTop (fun L => A L ζ) ∂P +
          (1 / (2 * Real.sqrt N)) * ∫ ζ, limUnder atTop (fun L => J L ζ) ∂P)) := by
      have heq : (fun L => ∫ ζ, Φ (Pj L (zetaPathW m T 0 P X ζ)) ∂P) = fun L =>
          ∫ ζ, r2HeatFn γ (fun w => Φ (Pj L w)) 0 (s102_y0 C m T P X ζ) ∂P -
            (Real.sqrt N)⁻¹ * ∫ ζ, A L ζ ∂P + (1 / (2 * Real.sqrt N)) * ∫ ζ, J L ζ ∂P := funext hid
      rw [heq]
      exact (hF1.sub (hAtend.const_mul _)).add (hJtend.const_mul _)
    simpa using tendsto_nhds_unique hL1 hfin

end HRS.MS.R2Interp

end
