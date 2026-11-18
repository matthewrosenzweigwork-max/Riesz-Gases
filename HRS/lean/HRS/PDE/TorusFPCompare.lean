import HRS.PDE.TorusFPSpec
import HRS.Stochastic.EmpiricalIto
import HRS.PDE.TorusFPCompareAux2
import HRS.PDE.TorusFPCompareAux3

/-!
# D1: regularity bridge on the covering space (proof of `d1_isC12On_of_isC12Test`)

Relocated proof of the frozen specification `HRS.d1_isC12On_of_isC12Test` (`HRS/PDE/TorusFPSpec.lean`;
the statement there is unchanged and is left as it was).

Route: the covering-space lift `d1_cl φ = Torus.lift φ ∘ d1_eucEquiv` of a `C²` function is `C²`
(`d1_isCk_iff`), its first and second derivatives are the transported derivatives of `Torus.lift φ`
(`d1_fderiv_cl`, `d1_fderiv2_cl`), and joint continuity comes from `IsC12Test.contOn_iter`, as in
`isC12On_empiricalLift` (`HRS/Stochastic/EmpiricalIto.lean`).  The time derivative at the endpoints
`0`, `τ` is the one-sided derivative `IsC12Test.hasDerivWithinAt_Icc`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {d N : ℕ}
variable {n : ℕ}

/-- Precomposition with the covering equivalence `d1_eucEquiv`, on dual spaces. -/
def d1c_pre : (Euc (N * d) →L[ℝ] ℝ) →L[ℝ] ((Fin N → Euc d) →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ (Fin N → Euc d) (Euc (N * d)) ℝ).flip
    (d1_eucEquiv d N).toContinuousLinearMap

theorem d1c_pre_apply (B : Euc (N * d) →L[ℝ] ℝ) (v : Fin N → Euc d) :
    d1c_pre B v = B (d1_eucEquiv d N v) := rfl

theorem d1c_fderiv_cl (φ : Torus (N * d) → ℝ) (Y : Fin N → Euc d) :
    fderiv ℝ (d1_cl φ) Y = d1c_pre (fderiv ℝ (Torus.lift φ) (d1_eucEquiv d N Y)) := by
  ext v
  rw [d1c_pre_apply, d1_fderiv_cl]

theorem d1c_fderiv2_cl (φ : Torus (N * d) → ℝ) (Y : Fin N → Euc d) :
    fderiv ℝ (fderiv ℝ (d1_cl φ)) Y =
      d1c_pre.comp ((fderiv ℝ (fderiv ℝ (Torus.lift φ)) (d1_eucEquiv d N Y)).comp
        (d1_eucEquiv d N).toContinuousLinearMap) := by
  ext v w
  rw [d1_fderiv2_cl]
  simp [d1c_pre_apply]

/-- Restriction of a function continuous on `[0,T] × Euc (N d)` to `(r, Y) ↦ (r, d1_eucEquiv Y)`. -/
theorem d1c_contOn_comp_E {T : ℝ} {Z : Type*} [TopologicalSpace Z] {G : ℝ × Euc (N * d) → Z}
    (h : ContinuousOn G (Set.Icc 0 T ×ˢ Set.univ)) :
    ContinuousOn (fun p : ℝ × (Fin N → Euc d) => G (p.1, d1_eucEquiv d N p.2))
      (Set.Icc 0 T ×ˢ Set.univ) :=
  h.comp (continuous_fst.prodMk ((d1_eucEquiv d N).continuous.comp continuous_snd)).continuousOn
    (fun p hp => ⟨hp.1, Set.mem_univ _⟩)

set_option maxHeartbeats 1000000 in
theorem d1_isC12On_of_isC12Test_proof {τ : ℝ} (hτ : 0 < τ) {f ft : ℝ → Torus (N * d) → ℝ}
    (hf : IsC12Test τ f ft) :
    IsC12On τ Set.univ (fun r => d1_cl (f r)) ∧
      ∀ r ∈ Set.Icc 0 τ, ∀ Y : Fin N → Euc d,
        derivWithin (fun r' => d1_cl (f r') Y) (Set.Icc 0 τ) r =
          ft r (d1_configEquiv d N fun i => Torus.mk (Y i)) := by
  have hcd : ∀ r ∈ Set.Icc 0 τ, ContDiff ℝ 2 (d1_cl (f r)) := fun r hr =>
    (d1_isCk_iff 2 (f r)).1 (hf.c2 r hr)
  have key : ∀ r ∈ Set.Icc 0 τ, ∀ Y : Fin N → Euc d,
      derivWithin (fun r' => d1_cl (f r') Y) (Set.Icc 0 τ) r =
        ft r (d1_configEquiv d N fun i => Torus.mk (Y i)) := fun r hr Y =>
    (hf.hasDerivWithinAt_Icc hτ (d1_configEquiv d N fun i => Torus.mk (Y i)) hr).derivWithin
      (uniqueDiffOn_Icc hτ r hr)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, key⟩
  · have h : ContinuousOn (fun p : ℝ × (Fin N → Euc d) => Torus.lift (f p.1) (d1_eucEquiv d N p.2))
        (Set.Icc 0 τ ×ˢ Set.univ) := d1c_contOn_comp_E hf.contOn_lift
    exact h.congr fun p _ => congrFun (d1_cl_eq (f p.1)) p.2
  · intro r hr Y _
    exact ((hcd r hr).differentiable (by norm_num) Y).hasFDerivAt
  · intro r hr Y _
    exact ((((hcd r hr).fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num)) Y).hasFDerivAt
  · have hA : ContinuousOn (fun p : ℝ × (Fin N → Euc d) =>
        fderiv ℝ (Torus.lift (f p.1)) (d1_eucEquiv d N p.2)) (Set.Icc 0 τ ×ˢ Set.univ) := by
      have h1 : ContinuousOn (fun p : ℝ × (Fin N → Euc d) =>
          iteratedFDeriv ℝ 1 (Torus.lift (f p.1)) (d1_eucEquiv d N p.2))
          (Set.Icc 0 τ ×ˢ Set.univ) :=
        d1c_contOn_comp_E (hf.contOn_iter (j := 1) (by norm_num))
      exact ((continuousMultilinearCurryFin1 ℝ (Euc (N * d)) ℝ).continuous.comp_continuousOn h1).congr
        fun p _ => fderiv_eq_curry _ _
    have h2 : ContinuousOn (fun p : ℝ × (Fin N → Euc d) =>
        d1c_pre (fderiv ℝ (Torus.lift (f p.1)) (d1_eucEquiv d N p.2)))
        (Set.Icc 0 τ ×ˢ Set.univ) :=
      d1c_pre.continuous.comp_continuousOn hA
    exact h2.congr fun p _ => d1c_fderiv_cl (f p.1) p.2
  · have hB : ContinuousOn (fun p : ℝ × (Fin N → Euc d) =>
        fderiv ℝ (fderiv ℝ (Torus.lift (f p.1))) (d1_eucEquiv d N p.2))
        (Set.Icc 0 τ ×ˢ Set.univ) := by
      have h1 : ContinuousOn (fun p : ℝ × (Fin N → Euc d) =>
          iteratedFDeriv ℝ 2 (Torus.lift (f p.1)) (d1_eucEquiv d N p.2))
          (Set.Icc 0 τ ×ˢ Set.univ) :=
        d1c_contOn_comp_E (hf.contOn_iter (j := 2) (by norm_num))
      exact ((continuous_curry2 (N * d)).comp_continuousOn h1).congr
        fun p _ => fderiv_fderiv_eq_curry2 _ _
    have h2 : ContinuousOn (fun p : ℝ × (Fin N → Euc d) =>
        d1c_pre.comp ((fderiv ℝ (fderiv ℝ (Torus.lift (f p.1))) (d1_eucEquiv d N p.2)).comp
          (d1_eucEquiv d N).toContinuousLinearMap)) (Set.Icc 0 τ ×ˢ Set.univ) :=
      (continuous_const.clm_comp (continuous_id.clm_comp continuous_const)).comp_continuousOn hB
    exact h2.congr fun p _ => d1c_fderiv2_cl (f p.1) p.2
  · intro Y _ r hr
    rw [key r hr Y]
    exact hf.hasDerivWithinAt_Icc hτ (d1_configEquiv d N fun i => Torus.mk (Y i)) hr
  · have h1 : ContinuousOn (fun p : ℝ × (Fin N → Euc d) =>
        ft p.1 (Torus.mk (d1_eucEquiv d N p.2))) (Set.Icc 0 τ ×ˢ Set.univ) :=
      hf.contOn_timeDeriv.comp
        (continuous_fst.prodMk ((d1_eucEquiv d N).continuous.comp continuous_snd)).continuousOn
        (fun p hp => ⟨hp.1, Set.mem_univ _⟩)
    refine h1.congr fun p hp => ?_
    dsimp only
    rw [key p.1 hp.1 p.2, d1_configEquiv_mk]

example := (@d1_isC12On_of_isC12Test_proof : type_of% @d1_isC12On_of_isC12Test)

/-! ### Target 2: comparison `c G ≤ μ 0 ≤ C G ⇒ c G ≤ μ t ≤ C G` (by duality)

Route: for smooth `ψ ≥ 0` and `t > 0`, duality with the classical backward solution `f` of terminal datum
`ψ` gives `∫ψ dμ_t = ∫ f_0 dμ_0`; `f_0 ≥ 0` (`d1_backward_nonneg`), `μ_0 ≤ C G` gives
`∫ f_0 dμ_0 ≤ C ∫ f_0 G dx`, and `∫ f_0 G dx = ∫ ψ G dx` (`d1c_stationary`).  Measure comparison from
smooth test functions (`d1c_le_of_smooth`).  The lower bound is symmetric. -/

theorem d1c_gibbs_continuous {κ : ℝ} {U : Torus n → ℝ} (hU : Torus.IsSmooth U) :
    Continuous (fun x => d1_gibbsWeight κ U x) := by
  have hU1 : Torus.IsCk 1 U := by
    have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift U) := hU
    exact h.of_le (by norm_num)
  exact Torus.continuous_of_continuous_lift
    (show ContDiff ℝ 1 (Torus.lift (fun x => d1_gibbsWeight κ U x)) from
      d1c_gibbs_isCk1 (κ := κ) hU1).continuous

theorem d1c_gibbs_nonneg (κ : ℝ) (U : Torus n → ℝ) (x : Torus n) :
    0 ≤ d1_gibbsWeight κ U x :=
  (Real.exp_pos _).le

theorem d1c_isFinite_gibbsRaw {κ : ℝ} {U : Torus n → ℝ} (hU : Torus.IsSmooth U) :
    IsFiniteMeasure (d1_gibbsRaw κ U) := by
  have hint : Integrable (fun x => d1_gibbsWeight κ U x) (volume : Measure (Torus n)) :=
    (d1c_gibbs_continuous hU).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold d1_gibbsRaw
  exact isFiniteMeasure_withDensity_ofReal hint.hasFiniteIntegral

theorem d1c_integral_gibbsRaw {κ : ℝ} {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    (g : Torus n → ℝ) :
    ∫ x, g x ∂(d1_gibbsRaw κ U) = ∫ x, g x * d1_gibbsWeight κ U x := by
  have hm : Measurable (fun x => ENNReal.ofReal (d1_gibbsWeight κ U x)) :=
    (d1c_gibbs_continuous hU).measurable.ennreal_ofReal
  unfold d1_gibbsRaw
  rw [integral_withDensity_eq_integral_toReal_smul hm (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [ENNReal.toReal_ofReal (d1c_gibbs_nonneg κ U x), smul_eq_mul, mul_comm]

/-- Duality: for smooth `ψ` and `t ∈ (0,T]`, `∫ψ dμ_t = ∫ f_0 dμ_0` for a backward solution `f`. -/
theorem d1c_backward_identity {κ : ℝ} (hn : 1 ≤ n) (hκ : 0 < κ) {U : Torus n → ℝ}
    (hU : Torus.IsSmooth U) {T : ℝ} {μ : ℝ → Measure (Torus n)}
    (hμ : D1WeakSolution κ (d1_gradDrift U) T μ) {t : ℝ} (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t)
    {ψ : Torus n → ℝ} (hψ : Torus.IsSmooth ψ) :
    ∃ f : ℝ → Torus n → ℝ, D1BackwardSolution κ (d1_gradDrift U) t ψ f ∧
      ∫ x, ψ x ∂(μ t) = ∫ x, f 0 x ∂(μ 0) := by
  obtain ⟨f, hf⟩ := d1_backward_classical hn hκ hU htpos hψ
  refine ⟨f, hf, ?_⟩
  have hC := hf.isC12Test
  have e1 := hμ.eqT t ht f _ hC
  have hz : ∀ (ρ : ℝ → Measure (Torus n)), ∀ s : ℝ,
      ∫ x, (-(d1_gen κ (d1_gradDrift U) (f s) x) + d1_gen κ (d1_gradDrift U) (f s) x) ∂(ρ s) = 0 := by
    intro ρ s; simp
  simp only [hz, integral_zero, add_zero] at e1
  rw [hf.terminal] at e1
  exact e1

theorem d1_fp_comparison_proof (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ}
    (hU : Torus.IsSmooth U) {T : ℝ} (hT : 0 < T) {μ : ℝ → Measure (Torus n)}
    (hμ : D1WeakSolution κ (d1_gradDrift U) T μ) {c C : ℝ≥0}
    (hc : (c : ℝ≥0∞) • d1_gibbsRaw κ U ≤ μ 0) (hC : μ 0 ≤ (C : ℝ≥0∞) • d1_gibbsRaw κ U) :
    ∀ t ∈ Set.Icc 0 T, (c : ℝ≥0∞) • d1_gibbsRaw κ U ≤ μ t ∧ μ t ≤ (C : ℝ≥0∞) • d1_gibbsRaw κ U := by
  intro t ht
  rcases ht.1.eq_or_lt with rfl | htpos
  · exact ⟨hc, hC⟩
  haveI := d1c_isFinite_gibbsRaw (κ := κ) hU
  haveI hCfin : IsFiniteMeasure ((C : ℝ≥0∞) • d1_gibbsRaw κ U) :=
    ⟨by rw [Measure.smul_apply, smul_eq_mul]
        exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top _ _)⟩
  haveI hcfin : IsFiniteMeasure ((c : ℝ≥0∞) • d1_gibbsRaw κ U) :=
    ⟨by rw [Measure.smul_apply, smul_eq_mul]
        exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top _ _)⟩
  haveI := hμ.finite 0 ⟨le_rfl, hT.le⟩
  haveI := hμ.finite t ht
  have hup : ∀ ψ : Torus n → ℝ, Torus.IsSmooth ψ → (∀ x, 0 ≤ ψ x) →
      ∫ x, ψ x ∂(μ t) ≤ ∫ x, ψ x ∂((C : ℝ≥0∞) • d1_gibbsRaw κ U) := by
    intro ψ hψ hψ0
    obtain ⟨f, hf, hid⟩ := d1c_backward_identity hn hκ hU hμ ht htpos hψ
    have hpos0 : ∀ x, 0 ≤ f 0 x :=
      d1_backward_nonneg hκ htpos hf hψ0 0 ⟨le_rfl, htpos.le⟩
    have hstat := d1c_stationary hκ hU htpos hf
    have hf0c : Continuous (f 0) := d1_continuous_of_isCk2 (hf.c2 0 ⟨le_rfl, htpos.le⟩)
    rw [hid]
    calc ∫ x, f 0 x ∂(μ 0)
        ≤ ∫ x, f 0 x ∂((C : ℝ≥0∞) • d1_gibbsRaw κ U) :=
          integral_mono_measure hC (ae_of_all _ hpos0) (d1c_integrable_of_cont _ hf0c)
      _ = (C : ℝ≥0∞).toReal • ∫ x, f 0 x ∂(d1_gibbsRaw κ U) := integral_smul_measure _ _
      _ = (C : ℝ≥0∞).toReal • ∫ x, ψ x ∂(d1_gibbsRaw κ U) := by
          rw [d1c_integral_gibbsRaw hU, d1c_integral_gibbsRaw hU, hstat]
      _ = ∫ x, ψ x ∂((C : ℝ≥0∞) • d1_gibbsRaw κ U) := (integral_smul_measure _ _).symm
  have hlow : ∀ ψ : Torus n → ℝ, Torus.IsSmooth ψ → (∀ x, 0 ≤ ψ x) →
      ∫ x, ψ x ∂((c : ℝ≥0∞) • d1_gibbsRaw κ U) ≤ ∫ x, ψ x ∂(μ t) := by
    intro ψ hψ hψ0
    obtain ⟨f, hf, hid⟩ := d1c_backward_identity hn hκ hU hμ ht htpos hψ
    have hpos0 : ∀ x, 0 ≤ f 0 x :=
      d1_backward_nonneg hκ htpos hf hψ0 0 ⟨le_rfl, htpos.le⟩
    have hstat := d1c_stationary hκ hU htpos hf
    have hf0c : Continuous (f 0) := d1_continuous_of_isCk2 (hf.c2 0 ⟨le_rfl, htpos.le⟩)
    rw [hid]
    calc ∫ x, ψ x ∂((c : ℝ≥0∞) • d1_gibbsRaw κ U)
        = (c : ℝ≥0∞).toReal • ∫ x, ψ x ∂(d1_gibbsRaw κ U) := integral_smul_measure _ _
      _ = (c : ℝ≥0∞).toReal • ∫ x, f 0 x ∂(d1_gibbsRaw κ U) := by
          rw [d1c_integral_gibbsRaw hU, d1c_integral_gibbsRaw hU, hstat]
      _ = ∫ x, f 0 x ∂((c : ℝ≥0∞) • d1_gibbsRaw κ U) := (integral_smul_measure _ _).symm
      _ ≤ ∫ x, f 0 x ∂(μ 0) :=
          integral_mono_measure hc (ae_of_all _ hpos0) (d1c_integrable_of_cont _ hf0c)
  exact ⟨d1c_le_of_smooth hlow, d1c_le_of_smooth hup⟩

example := (@d1_fp_comparison_proof : type_of% @d1_fp_comparison)

end HRS
