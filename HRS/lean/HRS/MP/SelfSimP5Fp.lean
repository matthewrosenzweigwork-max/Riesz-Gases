import HRS.MP.SelfSimP5FpB

/-!
# MPP5FP: `ss5_sde_weakFP` on `Fin N` from the P4 flow lemma

Namespace `HRS.MP.SelfSimP5Fp`, helpers `p5f_`.  Theorem `ss5_sde_weakFP_proof`, tied to
`HRS.MP.SelfSimP5.ss5_sde_weakFP` for `ι = Fin N`.  Route: transport along `e : ℝ^N ≃ (ℝ¹)^N`
(`(e z) k = single 0 (z k)`) and apply `HRS.MP.SelfSimP4Impl.p4_flow_hyp_proof` with `d = 1`; the Brownian
filtration is frozen at `ℱ 0` for negative times so that progressive measurability holds.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSim HRS.MP.SelfSimP4 HRS.MP.SelfSimP5
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.SelfSimP5Fp

variable {N : ℕ}

theorem p5f_flow {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {B : ℝ≥0 → Ω → Fin N → ℝ} (hB : IsBrownianFiltration P ℱ B)
    {U : EuclideanSpace ℝ (Fin N) → ℝ} {K : ℝ≥0} (hK : LipschitzWith K (gradient U))
    {θ : ℝ} (hθ : 0 < θ) {z₀ : Ω → EuclideanSpace ℝ (Fin N)}
    (hm0 : ∫⁻ ζ, ENNReal.ofReal (‖z₀ ζ‖ ^ 2) ∂P < ⊤)
    {Z : ℝ → Ω → EuclideanSpace ℝ (Fin N)} (hZ : ss5_IsSol P ℱ B θ (fun z => -(gradient U z)) z₀ Z)
    {S : ℝ} (hS : 0 < S) :
    P4FlowHyp θ (p5f_b U) S (fun r => law P (p5f_Y Z (Real.toNNReal r))) := by
  have hecm : Measurable (p5f_e N) := (p5f_e N).continuous.measurable
  have hZm : ∀ r : ℝ, 0 ≤ r → Measurable (Z r) := fun r hr => (hZ.2.1 r hr).mono (ℱ.le r) le_rfl
  have hLip : LipschitzWith ((‖(p5f_e N : EuclideanSpace ℝ (Fin N) →L[ℝ] EucConfig 1 N)‖₊) *
      (K * ‖((p5f_e N).symm : EucConfig 1 N →L[ℝ] EuclideanSpace ℝ (Fin N))‖₊)) (p5f_b U 0) := by
    have h1 := (p5f_e N : EuclideanSpace ℝ (Fin N) →L[ℝ] EucConfig 1 N).lipschitz
    have h2 := ((p5f_e N).symm : EucConfig 1 N →L[ℝ] EuclideanSpace ℝ (Fin N)).lipschitz
    exact h1.comp ((ss5_lip_neg hK).comp h2)
  have hbc : Continuous (Function.uncurry (p5f_b U)) := by
    have : Continuous fun x : EucConfig 1 N => p5f_b U 0 x := hLip.continuous
    exact this.comp continuous_snd
  have hbl : ∃ K' : ℝ≥0, ∀ τ ∈ Icc (0 : ℝ) S, LipschitzWith K' (p5f_b U τ) :=
    ⟨_, fun τ _ => hLip⟩
  have hZ0 : ∀ᵐ ζ ∂P, Z 0 ζ = z₀ ζ := by
    filter_upwards [hZ.2.2] with ζ hζ
    have h0 := hζ 0 le_rfl
    simpa [hB.zero ζ] using h0
  have hmeas : Measurable (p5f_Y Z 0) := hecm.comp (hZm _ (NNReal.coe_nonneg _))
  have hmY : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(law P (p5f_Y Z 0)) < ⊤ := by
    rw [lintegral_map (by fun_prop) hmeas]
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) hm0
    filter_upwards [hZ0] with ζ hζ
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : ‖p5f_Y Z 0 ζ‖ ≤ ‖Z 0 ζ‖ := by simpa [p5f_Y] using p5f_norm_e_le (Z 0 ζ)
    rw [hζ] at h1
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  exact HRS.MP.SelfSimP4Impl.p4_flow_hyp_proof P hθ.le hS hbc hbl (p5f_addSol hB hK.continuous hZ S) hmY

theorem p5f_law_eq {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
    {B : ℝ≥0 → Ω → Fin N → ℝ} {θ : ℝ}
    {b : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)} {z₀ : Ω → EuclideanSpace ℝ (Fin N)}
    {Z : ℝ → Ω → EuclideanSpace ℝ (Fin N)} (hZ : ss5_IsSol P ℱ B θ b z₀ Z) {r : ℝ} (hr : 0 ≤ r) :
    law P (p5f_Y Z (Real.toNNReal r)) = (P.map (Z r)).map (p5f_e N) := by
  have hZm : Measurable (Z r) := (hZ.2.1 r hr).mono (ℱ.le r) le_rfl
  have h : p5f_Y Z (Real.toNNReal r) = (p5f_e N) ∘ Z r := by
    funext ζ; simp [p5f_Y, Real.coe_toNNReal r hr]
  rw [Measure.map_map (p5f_e N).continuous.measurable hZm, h]

theorem p5f_integral_law {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
    {B : ℝ≥0 → Ω → Fin N → ℝ} {θ : ℝ}
    {b : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)} {z₀ : Ω → EuclideanSpace ℝ (Fin N)}
    {Z : ℝ → Ω → EuclideanSpace ℝ (Fin N)} (hZ : ss5_IsSol P ℱ B θ b z₀ Z) {r : ℝ} (hr : 0 ≤ r)
    (F : EucConfig 1 N → ℝ) :
    ∫ x, F x ∂(law P (p5f_Y Z (Real.toNNReal r))) = ∫ z, F (p5f_e N z) ∂(P.map (Z r)) := by
  rw [p5f_law_eq hZ hr]
  exact (p5f_e N).toHomeomorph.measurableEmbedding.integral_map F

theorem p5f_lintegral_law {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
    {B : ℝ≥0 → Ω → Fin N → ℝ} {θ : ℝ}
    {b : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)} {z₀ : Ω → EuclideanSpace ℝ (Fin N)}
    {Z : ℝ → Ω → EuclideanSpace ℝ (Fin N)} (hZ : ss5_IsSol P ℱ B θ b z₀ Z) {r : ℝ} (hr : 0 ≤ r)
    (F : EucConfig 1 N → ℝ≥0∞) :
    ∫⁻ x, F x ∂(law P (p5f_Y Z (Real.toNNReal r))) = ∫⁻ z, F (p5f_e N z) ∂(P.map (Z r)) := by
  rw [p5f_law_eq hZ hr]
  exact (p5f_e N).toHomeomorph.measurableEmbedding.lintegral_map F

theorem ss5_sde_weakFP_proof {N : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {B : ℝ≥0 → Ω → Fin N → ℝ}
    (hB : IsBrownianFiltration P ℱ B)
    {U : EuclideanSpace ℝ (Fin N) → ℝ} (hU : ContDiff ℝ 2 U) {K : ℝ≥0} (hK : LipschitzWith K (gradient U))
    {θ : ℝ} (hθ : 0 < θ) {z₀ : Ω → EuclideanSpace ℝ (Fin N)} (hz₀ : Measurable[ℱ 0] z₀)
    (hm0 : ∫⁻ ζ, ENNReal.ofReal (‖z₀ ζ‖ ^ 2) ∂P < ⊤)
    {Z : ℝ → Ω → EuclideanSpace ℝ (Fin N)} (hZ : ss5_IsSol P ℱ B θ (fun z => -(gradient U z)) z₀ Z) :
    ss5_WeakFP θ U (fun t => P.map (Z t)) ∧
      (∀ T : ℝ, ∃ M : ℝ≥0∞, M < ⊤ ∧
        ∀ t ∈ Icc (0 : ℝ) T, ∫⁻ z, ENNReal.ofReal (‖z‖ ^ 2) ∂(P.map (Z t)) ≤ M) ∧
      ∀ g : EuclideanSpace ℝ (Fin N) → ℝ, Continuous g → (∃ C : ℝ, ∀ z, |g z| ≤ C) → ∀ T : ℝ,
        ContinuousOn (fun t => ∫ z, g z ∂(P.map (Z t))) (Icc (0 : ℝ) T) := by
  have hflow : ∀ S : ℝ, 0 < S → P4FlowHyp θ (p5f_b U) S (fun r => law P (p5f_Y Z (Real.toNNReal r))) :=
    fun S hS => p5f_flow hB hK hθ hm0 hZ hS
  refine ⟨fun g hg t ht => ?_, fun T => ?_, fun g hgc ⟨C, hC⟩ T => ?_⟩
  · have hfp := (hflow (t + 1) (by linarith)).fp (p5f_tr g) (p5f_test_tr hg) t ⟨ht, by linarith⟩
    simp only [Real.toNNReal_zero] at hfp
    have e1 : ∀ r : ℝ, 0 ≤ r → ∫ x, p5f_tr g x ∂(law P (p5f_Y Z (Real.toNNReal r))) =
        ∫ z, g z ∂(P.map (Z r)) := fun r hr => by
      rw [p5f_integral_law hZ hr]
      simp [p5f_tr]
    have e0 : ∫ x, p5f_tr g x ∂(law P (p5f_Y Z 0)) = ∫ z, g z ∂(P.map (Z 0)) := by
      simpa using e1 0 le_rfl
    have e2 : ∀ r ∈ Icc (0 : ℝ) t, ∫ x, p4Gen θ (p5f_b U) r (p5f_tr g) x ∂(law P (p5f_Y Z (Real.toNNReal r))) =
        ∫ z, ss5_gen θ U g z ∂(P.map (Z r)) := fun r hr => by
      rw [p5f_integral_law hZ hr.1]
      exact integral_congr_ae (Eventually.of_forall fun z => p5f_gen_eq hg.smooth θ U r z)
    rw [e1 t ht, e0] at hfp
    rw [hfp]
    congr 1
    exact setIntegral_congr_fun measurableSet_Icc e2
  · obtain ⟨C, hCtop, hC⟩ := (hflow (max T 1) (lt_of_lt_of_le one_pos (le_max_right _ _))).mom
    refine ⟨(N : ℝ≥0∞) * C, ENNReal.mul_lt_top (ENNReal.natCast_lt_top N) hCtop, fun t ht => ?_⟩
    have ht' : t ∈ Icc (0 : ℝ) (max T 1) := ⟨ht.1, ht.2.trans (le_max_left _ _)⟩
    have h1 := hC t ht'
    rw [p5f_lintegral_law hZ ht.1 (fun x => ENNReal.ofReal (‖x‖ ^ 2))] at h1
    calc ∫⁻ z, ENNReal.ofReal (‖z‖ ^ 2) ∂(P.map (Z t))
        ≤ ∫⁻ z, (N : ℝ≥0∞) * ENNReal.ofReal (‖p5f_e N z‖ ^ 2) ∂(P.map (Z t)) := by
          refine lintegral_mono fun z => ?_
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg N)]
          exact ENNReal.ofReal_le_ofReal (p5f_norm_sq_le z)
      _ = (N : ℝ≥0∞) * ∫⁻ z, ENNReal.ofReal (‖p5f_e N z‖ ^ 2) ∂(P.map (Z t)) :=
          lintegral_const_mul' _ _ (ENNReal.natCast_ne_top N)
      _ ≤ (N : ℝ≥0∞) * C := by gcongr
  · have hS : 0 < max T 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hn := (hflow (max T 1) hS).narrow (p5f_tr g)
      (hgc.comp (p5f_e N).symm.continuous) ⟨C, fun x => hC _⟩
    refine (hn.mono fun t ht => ⟨ht.1, ht.2.trans (le_max_left _ _)⟩).congr fun t ht => ?_
    beta_reduce
    rw [p5f_integral_law hZ ht.1]
    simp [p5f_tr]

example {N : ℕ} := (@ss5_sde_weakFP_proof N :
  type_of% (@HRS.MP.SelfSimP5.ss5_sde_weakFP (Fin N) _ _))

end HRS.MP.SelfSimP5Fp
