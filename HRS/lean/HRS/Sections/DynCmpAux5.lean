import HRS.Sections.DynCmpAux2
import HRS.Sections.DynCmpAux4
import HRS.Sections.Q40bAux9

/-!
# DYNCMP: Theorem 5.4 `dynamic_comparison`, step (4b): the duality identity for `linCoord` and the remainder bound

* `dyncmp_ae_identity`: a.s. `⟨φ, η_N^t⟩ = ⟨f^0, η_N^∘⟩ + √N M_N(t) + √N ∫_0^t flucInteraction dr`
  (`N:eq:duality`, scaled by `√N`), from `duality_identity_final` and the strong-solution data;
* `dyncmp_R_bound`: from the pair-entropy moment bound `E[N |F_N^{h_{∇F^r}}|] ≤ C_m` the remainder
  `R = √N ∫_0^t flucInteraction dr` is integrable with `E|R| ≤ t C_m/√N` (joint measurability and Fubini of
  `Q40bAux5`).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

section Identity

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

theorem dyncmp_linCoord_eq (hN : 0 < N) (μ : Measure (Torus d)) (ψ : Torus d → ℝ) (X : Config d N) :
    linCoord μ ψ X = Real.sqrt N * ((1 / (N : ℝ)) * ∑ i, ψ (X i) - pair μ ψ) := rfl

theorem dyncmp_flucPair_eq (hN : 0 < N) (X : Config d N) (ρ ψ : Torus d → ℝ) :
    flucPair X ρ ψ = (1 / (N : ℝ)) * ∑ i, ψ (X i) - pair (withDensityReal ρ) ψ := by
  unfold flucPair; rw [pair_empirical hN, one_div]

/-- The a.s. duality identity for the statistic `linCoord` (`N:eq:duality`, scaled by `√N`). -/
theorem dyncmp_ae_identity (hd : 1 ≤ d) {D : DynData d} (hM : D.M = -1) (hV : Torus.IsCk 2 D.V)
    {T Λ : ℝ} {ρ : ℝ → Torus d → ℝ} (hρ : IsMeanFieldSolution D T ρ) (hreg : IsRegularMF 3 Λ T ρ)
    (hN : 2 ≤ N) [NeZero N] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hsol : IsStrongSolution P D T X₀ W X) (hfilt : IsFilteredSolution P ℱ W' W X)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) {φ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ) {F : ℝ → Torus d → ℝ}
    (hF : IsClassicalAdjointSolution D ρ t φ F)
    (hFp : ∀ r ∈ Set.Icc 0 t, propagator D ρ r t φ = F r) :
    ∀ᵐ ω ∂P, linCoord (withDensityReal (ρ t)) φ (X t.toNNReal ω) =
      linCoord (withDensityReal (ρ 0)) (F 0) (X 0 ω) +
        Real.sqrt N * itoIntegral P ℱ W' (empiricalNoiseIntegrand D t F X) t ω +
        Real.sqrt N * ∫ r in (0 : ℝ)..t, flucInteraction D (F r) (X r.toNNReal ω) (ρ r) := by
  have hN0 : 0 < N := by omega
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    refine Eventually.of_forall fun ω => ?_
    have : F 0 = φ := hF.terminal
    rw [this, itoIntegral_of_nonpos P ℱ W' _ (le_refl (0 : ℝ))]
    simp
  · have hocc : D.M = 0 ∨ NullContactOccupation P T X := Or.inr (by
      unfold NullContactOccupation
      filter_upwards [hsol.no_collision] with ω hω
      have : {s : ℝ | s ∈ Set.Icc 0 T ∧ X s.toNNReal ω ∈ collisionSet d N} = ∅ := by
        ext s
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro hs hc
        refine hω s.toNNReal ?_ hc
        rw [Real.coe_toNNReal _ hs.1]; exact hs.2
      rw [this]; simp)
    have hdual := duality_identity_final hd hN hV hρ hreg hsol.toContact hfilt hocc ⟨hpos, ht.2⟩ hφ ⟨F, hF⟩
    have hΨeq : empiricalNoiseIntegrand D t (fun r => propagator D ρ r t φ) X =
        empiricalNoiseIntegrand D t F X := by
      funext s' ω k
      unfold empiricalNoiseIntegrand
      by_cases hs : s' ∈ Set.Icc 0 t
      · simp only [hs, if_true]; rw [hFp s' hs]
      · simp [hs]
    have hMeq : empiricalMartingale P ℱ W' D t (fun r => propagator D ρ r t φ) X =
        empiricalMartingale P ℱ W' D t F X := by
      unfold empiricalMartingale; rw [hΨeq]
    have hψ0 : propagator D ρ 0 t φ = F 0 := hFp 0 ⟨le_rfl, hpos.le⟩
    have hIeq : ∀ ω, ∫ r in (0 : ℝ)..t, flucInteraction D (propagator D ρ r t φ) (X r.toNNReal ω) (ρ r) =
        ∫ r in (0 : ℝ)..t, flucInteraction D (F r) (X r.toNNReal ω) (ρ r) := by
      intro ω
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [Set.uIcc_of_le hpos.le] at hr
      simp only [hFp r hr]
    filter_upwards [hdual] with ω h
    rw [hMeq, hψ0, hIeq ω, Real.coe_toNNReal _ hpos.le] at h
    have e1 : linCoord (withDensityReal (ρ t)) φ (X t.toNNReal ω) =
        Real.sqrt N * flucPair (X t.toNNReal ω) (ρ t) φ := by
      rw [dyncmp_linCoord_eq hN0, dyncmp_flucPair_eq hN0]
    have e0 : linCoord (withDensityReal (ρ 0)) (F 0) (X 0 ω) =
        Real.sqrt N * flucPair (X 0 ω) (ρ 0) (F 0) := by
      rw [dyncmp_linCoord_eq hN0, dyncmp_flucPair_eq hN0]
    rw [e1, e0, h]
    unfold empiricalMartingale
    ring


open HRS.Q40b in
/-- The remainder `R_a = √N ∫_0^t flucInteraction dr`: integrable with `E|R_a| ≤ t C_m/√N`, from the pair-entropy
moment bound `E[N |F_N^{h_{∇F^r}}|] ≤ C_m` for `r ∈ (0,t]`. -/
theorem dyncmp_R_bound (hd : 1 ≤ d) {D : DynData d} (hM : D.M = -1) {ρ : ℝ → Torus d → ℝ} {t : ℝ} (ht0 : 0 ≤ t)
    {F ft : ℝ → Torus d → ℝ} (hF : IsC12Test t F ft) (hN : 2 ≤ N)
    {ℱ : Filtration ℝ mΩ} {X : ℝ≥0 → Ω → Config d N} (hXprog : IsProgressive ℱ (ofNNRealTime X))
    (hρJ : ContinuousOn (fun p : ℝ × Torus d => ρ p.1 p.2) (Set.Icc 0 t ×ˢ Set.univ))
    (hρP : ∀ r ∈ Set.Icc 0 t, IsProbDensity (ρ r)) {Bρ : ℝ} (hB : ∀ r ∈ Set.Icc 0 t, ∀ x, ρ r x ≤ Bρ)
    {Cm : ℝ} (hCm0 : 0 ≤ Cm)
    (hmom : ∀ r ∈ Set.Ioc 0 t, ∫⁻ ω, ENNReal.ofReal ((N : ℝ) * |Fm d D.s F ρ X r ω|) ∂P ≤ ENNReal.ofReal Cm) :
    Integrable (fun ω => Real.sqrt N * ∫ r in (0 : ℝ)..t, flucInteraction D (F r) (X r.toNNReal ω) (ρ r)) P ∧
    ∫ ω, |Real.sqrt N * ∫ r in (0 : ℝ)..t, flucInteraction D (F r) (X r.toNNReal ω) (ρ r)| ∂P ≤
      t * Cm / Real.sqrt N := by
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 hNr
  obtain ⟨H, hH⟩ : ∃ H : ℝ → Ω → ℝ, H = fun r ω => (N : ℝ) * Fm d D.s F ρ X r ω := ⟨_, rfl⟩
  have hHm : Measurable (fun p : ℝ × Ω => H (clampTI t p.1) p.2) :=
    by rw [hH]; exact measurable_const.mul (q40b_Fm_meas (N := N) (s := D.s) (ℱ := ℱ) ht0 D.hsd hF hρJ hρP hXprog)
  have hbd : ∀ r ∈ Set.Ioc 0 t, ∫⁻ ω, ‖H r ω‖ₑ ∂P ≤ ENNReal.ofReal Cm := by
    intro r hr
    refine le_trans (le_of_eq ?_) (hmom r hr)
    refine lintegral_congr fun ω => ?_
    rw [Real.enorm_eq_ofReal_abs, hH]
    simp only [abs_mul, abs_of_pos hNr]
  have hint := q40b_integrable_prod ht0 hHm ENNReal.ofReal_ne_top hbd
  -- pointwise: the remainder is `-(1/√N) ∫_{(0,t]} H`
  have hRe : ∀ ω, Real.sqrt N * ∫ r in (0 : ℝ)..t, flucInteraction D (F r) (X r.toNNReal ω) (ρ r) =
      -((1 / Real.sqrt N) * ∫ r in Set.Ioc 0 t, H r ω) := by
    intro ω
    have h1 : ∫ r in (0 : ℝ)..t, flucInteraction D (F r) (X r.toNNReal ω) (ρ r) =
        -∫ r in (0 : ℝ)..t, Fm d D.s F ρ X r ω := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [Set.uIcc_of_le ht0] at hr
      exact dyncmp_fluc_eq hd hM (hF.c2 r hr) (hB r hr) hN0 _
    rw [h1, intervalIntegral.integral_of_le ht0]
    have h2 : ∫ r in Set.Ioc 0 t, H r ω = (N : ℝ) * ∫ r in Set.Ioc 0 t, Fm d D.s F ρ X r ω := by
      rw [hH]; simp only []; rw [integral_const_mul]
    rw [h2]
    have h3 : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNr.le
    have h4 : (1 / Real.sqrt N) * ((N : ℝ) * ∫ r in Set.Ioc 0 t, Fm d D.s F ρ X r ω) =
        Real.sqrt N * ∫ r in Set.Ioc 0 t, Fm d D.s F ρ X r ω := by
      calc (1 / Real.sqrt N) * ((N : ℝ) * ∫ r in Set.Ioc 0 t, Fm d D.s F ρ X r ω)
          = (1 / Real.sqrt N) * ((Real.sqrt N * Real.sqrt N) * ∫ r in Set.Ioc 0 t, Fm d D.s F ρ X r ω) := by
            rw [h3]
        _ = _ := by field_simp
    rw [h4]; ring
  simp_rw [hRe]
  refine ⟨(hint.integral_prod_right.const_mul (1 / Real.sqrt N)).neg, ?_⟩
  have hint' : Integrable (fun p : ℝ × Ω => |H p.1 p.2|) ((volume.restrict (Set.Ioc 0 t)).prod P) := by
    simpa only [Real.norm_eq_abs] using hint.norm
  have hGint : Integrable (fun ω => ∫ r in Set.Ioc 0 t, |H r ω|) P := hint'.integral_prod_right
  have hGint' : Integrable (fun r => ∫ ω, |H r ω| ∂P) (volume.restrict (Set.Ioc 0 t)) :=
    hint'.integral_prod_left
  have hswap : ∫ ω, (∫ r in Set.Ioc 0 t, |H r ω|) ∂P = ∫ r in Set.Ioc 0 t, (∫ ω, |H r ω| ∂P) :=
    (integral_integral_swap (f := fun r ω => |H r ω|) hint').symm
  have hslice : ∀ r ∈ Set.Ioc 0 t, ∫ ω, |H r ω| ∂P ≤ Cm := by
    intro r hr
    have hmeasr : Measurable (fun ω => H r ω) := by
      have h1 : Measurable (fun ω => H (clampTI t r) ω) :=
        hHm.comp (measurable_prodMk_left (m := (inferInstance : MeasurableSpace ℝ)) (x := r))
      rwa [clampTI_of_mem ⟨hr.1.le, hr.2⟩] at h1
    have hnn : 0 ≤ᵐ[P] fun ω => |H r ω| := Eventually.of_forall fun ω => abs_nonneg _
    rw [integral_eq_lintegral_of_nonneg_ae hnn hmeasr.abs.aestronglyMeasurable]
    have hle := hbd r hr
    have : ∫⁻ ω, ENNReal.ofReal |H r ω| ∂P = ∫⁻ ω, ‖H r ω‖ₑ ∂P :=
      lintegral_congr fun ω => (Real.enorm_eq_ofReal_abs _).symm
    rw [this]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle).trans (by rw [ENNReal.toReal_ofReal hCm0])
  have hpt : ∀ ω, |-((1 / Real.sqrt N) * ∫ r in Set.Ioc 0 t, H r ω)| ≤
      (1 / Real.sqrt N) * ∫ r in Set.Ioc 0 t, |H r ω| := by
    intro ω
    rw [abs_neg, abs_mul, abs_of_pos (one_div_pos.2 hsq)]
    exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (one_div_pos.2 hsq).le
  calc ∫ ω, |-((1 / Real.sqrt N) * ∫ r in Set.Ioc 0 t, H r ω)| ∂P
      ≤ ∫ ω, ((1 / Real.sqrt N) * ∫ r in Set.Ioc 0 t, |H r ω|) ∂P :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω => abs_nonneg _) (hGint.const_mul _)
          (Eventually.of_forall hpt)
    _ = (1 / Real.sqrt N) * ∫ r in Set.Ioc 0 t, (∫ ω, |H r ω| ∂P) := by
        rw [integral_const_mul, hswap]
    _ ≤ (1 / Real.sqrt N) * ∫ r in Set.Ioc 0 t, Cm := by
        refine mul_le_mul_of_nonneg_left ?_ (one_div_pos.2 hsq).le
        exact setIntegral_mono_on hGint' (integrable_const _) measurableSet_Ioc hslice
    _ = t * Cm / Real.sqrt N := by
        simp [Real.volume_real_Ioc_of_le ht0]
        ring

end Identity
end HRS
end
