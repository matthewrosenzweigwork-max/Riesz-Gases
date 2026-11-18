import HRS.Sections.Sec5
import HRS.Stochastic.DualityProof
import HRS.Sections.Q40bAux3
import HRS.Sections.Q40bAux5

/-!
# Packet Q40b, part 6: the centered duality identity

`q40b_centered_identity` is TeX `C:eq:centered-identity`:
`⟨φ, ζ_N^t⟩ = ⟨U^{0,t}φ, ζ_N^∘⟩ + √N M_N(t,φ) - 𝓡_N(t,φ)`, a.s., obtained from the duality identity
(Proposition 3.7) by centering, `flucInteraction = -F_N^{h_{∇f}}` (part 3) and Fubini (part 5).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section
namespace HRS.Q40b

variable {d N : ℕ} {s : ℝ}

theorem q40b_bdd {ψ : Torus d → ℝ} (hψ : Continuous ψ) : ∃ B : ℝ, ∀ x, |ψ x| ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hψ.continuousOn
  exact ⟨B, fun x => by simpa using hB x (Set.mem_univ x)⟩

section Zeta

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

theorem q40b_integrable_comp {X : Ω → Config d N} (hX : Measurable X) {ψ : Torus d → ℝ}
    (hψ : Continuous ψ) (i : Fin N) : Integrable (fun ω => ψ (X ω i)) P := by
  obtain ⟨B, hB⟩ := q40b_bdd hψ
  exact Integrable.of_bound (hψ.measurable.comp ((measurable_pi_apply i).comp hX)).aestronglyMeasurable B
    (Filter.Eventually.of_forall fun ω => by simpa using hB (X ω i))

theorem q40b_integrable_stat {X : Ω → Config d N} (hX : Measurable X) {ψ : Torus d → ℝ}
    (hψ : Continuous ψ) : Integrable (fun ω => (1 / (N : ℝ)) * ∑ i, ψ (X ω i)) P :=
  Integrable.const_mul (integrable_finset_sum _ fun i _ => q40b_integrable_comp hX hψ i) _

theorem q40b_pair_meanEmp (hN : 0 < N) {X : Ω → Config d N} (hX : Measurable X) {ψ : Torus d → ℝ}
    (hψ : Continuous ψ) :
    pair (meanEmpirical (P.map X)) ψ = ∫ ω, (1 / (N : ℝ)) * ∑ i, ψ (X ω i) ∂P := by
  unfold pair
  rw [integral_meanEmpirical (P.map X) hψ]
  have h1 : ∀ i : Fin N, ∫ y, ψ (y i) ∂(P.map X) = ∫ ω, ψ (X ω i) ∂P := fun i =>
    integral_map hX.aemeasurable (hψ.measurable.comp (measurable_pi_apply i)).aestronglyMeasurable
  simp_rw [h1]
  rw [integral_const_mul, integral_finset_sum _ (fun i _ => q40b_integrable_comp hX hψ i)]
  ring

theorem q40b_zeta_eq (hN : 0 < N) {X : ℝ≥0 → Ω → Config d N} (t : ℝ) (hXt : Measurable (X t.toNNReal))
    {ψ : Torus d → ℝ} (hψ : Continuous ψ) (ρ : Torus d → ℝ) (ω : Ω) :
    zetaStat P X t ψ ω = Real.sqrt N * (flucPair (X t.toNNReal ω) ρ ψ -
      ∫ ω', flucPair (X t.toNNReal ω') ρ ψ ∂P) := by
  have hf : ∀ ω', flucPair (X t.toNNReal ω') ρ ψ =
      (1 / (N : ℝ)) * ∑ i, ψ (X t.toNNReal ω' i) - pair (withDensityReal ρ) ψ := by
    intro ω'
    unfold flucPair
    rw [pair_empirical hN, one_div]
  simp_rw [hf]
  rw [integral_sub (q40b_integrable_stat hXt hψ) (integrable_const _), integral_const]
  unfold zetaStat
  rw [q40b_pair_meanEmp hN hXt hψ]
  simp

end Zeta


section Identity

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

theorem q40b_integral_Fm_swap {t : ℝ} (ht : 0 ≤ t) {H : ℝ → Ω → ℝ}
    (hint : Integrable (fun p : ℝ × Ω => H p.1 p.2) ((volume.restrict (Set.Ioc 0 t)).prod P)) :
    ∫ ω, (∫ r in (0 : ℝ)..t, H r ω) ∂P = ∫ r in (0 : ℝ)..t, ∫ ω, H r ω ∂P := by
  simp_rw [intervalIntegral.integral_of_le ht]
  exact (integral_integral_swap hint).symm

/-- The centered duality identity for one test function (Proposition 5.14, TeX identity
`C:eq:centered-identity`). -/
theorem q40b_centered_identity (hd : 1 ≤ d) {D : DynData d} (hM : D.M = -1)
    (hV : Torus.IsCk 2 D.V) {t : ℝ} (ht : 0 < t) {ρ : ℝ → Torus d → ℝ} {Λ B : ℝ}
    (hρ : IsMeanFieldSolution D t ρ) (hreg : IsRegularMF 3 Λ t ρ)
    (hρJ : ContinuousOn (fun p : ℝ × Torus d => ρ p.1 p.2) (Set.Icc 0 t ×ˢ Set.univ))
    (hB : ∀ r ∈ Set.Icc 0 t, ∀ x, ρ r x ≤ B)
    {φ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ) {F : ℝ → Torus d → ℝ}
    (hF : IsClassicalAdjointSolution D ρ t φ F)
    (hFp : ∀ r ∈ Set.Icc 0 t, propagator D ρ r t φ = F r)
    (hN : 2 ≤ N) [NeZero N] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hsol : IsStrongSolution P D t X₀ W X) (hfilt : IsFilteredSolution P ℱ W' W X)
    {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (hL1 : ∀ r ∈ Set.Icc 0 t, ∫⁻ ω, ‖Fm d D.s F ρ X r ω‖ₑ ∂P ≤ K) :
    ∀ᵐ ω ∂P, zetaStat P X t φ ω =
      zetaStat P X 0 (propagator D ρ 0 t φ) ω +
        Real.sqrt N * empiricalMartingale P ℱ W' D t (fun r => propagator D ρ r t φ) X
          (Real.toNNReal t) ω -
        integratedRemainder D ρ P X t φ ω := by
  classical
  have ht0 : 0 ≤ t := ht.le
  have hN0 : 0 < N := by omega
  -- the contact/occupation hypotheses of the duality identity
  have hocc : D.M = 0 ∨ NullContactOccupation P t X := Or.inr (by
    unfold NullContactOccupation
    filter_upwards [hsol.no_collision] with ω hω
    have : {s : ℝ | s ∈ Set.Icc 0 t ∧ X s.toNNReal ω ∈ collisionSet d N} = ∅ := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hs hc
      refine hω s.toNNReal ?_ hc
      rw [Real.coe_toNNReal _ hs.1]; exact hs.2
    rw [this]; simp)
  have hdual := duality_identity_final hd hN hV hρ hreg hsol.toContact hfilt hocc ⟨ht, le_rfl⟩ hφ ⟨F, hF⟩
  have hFc : ∀ r ∈ Set.Icc 0 t, Torus.IsCk 2 (F r) := hF.c2
  have hcont2 : ∀ {g : Torus d → ℝ}, Torus.IsCk 2 g → Continuous g := fun {g} hg =>
    PDE.MFAux.continuous_of_isCk (PDE.ClassicalAux.isCk_of_le (by norm_num) hg)
  have hφc : Continuous φ := hcont2 hφ
  have hψ0 : propagator D ρ 0 t φ = F 0 := hFp 0 ⟨le_rfl, ht0⟩
  have hF0c : Continuous (F 0) := hcont2 (hFc 0 ⟨le_rfl, ht0⟩)
  -- the noise integrand only sees `F` on `[0,t]`
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
  rw [hMeq] at hdual ⊢
  have hprog : IsProgressiveL2 P ℱ (empiricalNoiseIntegrand D t F X) :=
    isProgressiveL2_empiricalNoiseIntegrand hfilt.progressive ht0 hF.isC12Test
  have hMint : Integrable (fun ω => empiricalMartingale P ℱ W' D t F X (Real.toNNReal t) ω) P :=
    ((memLp_two_itoIntegral hfilt.brownian hprog _).integrable one_le_two)
  have hMzero : ∫ ω, empiricalMartingale P ℱ W' D t F X (Real.toNNReal t) ω ∂P = 0 :=
    integral_itoIntegral hfilt.brownian hprog _
  have hXt : Measurable (X t.toNNReal) := hsol.adapted _
  have hX0 : Measurable (X 0) := hsol.adapted _
  -- the forcing
  have hmeasFm := q40b_Fm_meas (N := N) (s := D.s) ht0 D.hsd hF.isC12Test hρJ hρ.density hfilt.progressive
  have hintFm := q40b_integrable_prod ht0 hmeasFm hK (fun r hr => hL1 r ⟨hr.1.le, hr.2⟩)
  have hswap := q40b_integral_Fm_swap ht0 hintFm
  set m : ℝ → ℝ := fun r => ∫ ω, Fm d D.s F ρ X r ω ∂P with hm
  have hIeq : ∀ ω, ∫ r in (0 : ℝ)..t, flucInteraction D (propagator D ρ r t φ) (X r.toNNReal ω) (ρ r)
      = -∫ r in (0 : ℝ)..t, Fm d D.s F ρ X r ω := by
    intro ω
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le ht0] at hr
    rw [hFp r hr]
    exact q40b_fluc_eq_neg hd hM (hFc r hr) (hρ.density r hr) (hB r hr) hN0 _
  have hReq : ∀ ω, integratedRemainder D ρ P X t φ ω =
      ∫ r in (0 : ℝ)..t, Real.sqrt N * (Fm d D.s F ρ X r ω - m r) := by
    intro ω
    unfold integratedRemainder
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le ht0] at hr
    unfold centeredCommutatorForcing
    rw [hFp r hr]
    rfl
  rw [hψ0] at hdual ⊢
  have hflp : ∀ (τ : ℝ) (ψ : Torus d → ℝ) (ρτ : Torus d → ℝ) (ω : Ω),
      flucPair (X τ.toNNReal ω) ρτ ψ =
        (1 / (N : ℝ)) * ∑ i, ψ (X τ.toNNReal ω i) - pair (withDensityReal ρτ) ψ := by
    intro τ ψ ρτ ω
    unfold flucPair; rw [pair_empirical hN0, one_div]
  have hPt : Integrable (fun ω => flucPair (X t.toNNReal ω) (ρ t) φ) P := by
    simp_rw [hflp]
    exact (q40b_integrable_stat hXt hφc).sub (integrable_const _)
  have hX0' : Measurable (X (Real.toNNReal 0)) := hsol.adapted _
  have hP0 : Integrable (fun ω => flucPair (X 0 ω) (ρ 0) (F 0)) P := by
    have := hflp 0 (F 0) (ρ 0)
    simp only [Real.toNNReal_zero] at this
    simp_rw [this]
    exact (q40b_integrable_stat (by simpa using hX0') hF0c).sub (integrable_const _)
  set Iω : Ω → ℝ := fun ω => ∫ r in (0 : ℝ)..t,
    flucInteraction D (propagator D ρ r t φ) (X r.toNNReal ω) (ρ r) with hI
  have hIae : Iω =ᵐ[P] fun ω => flucPair (X t.toNNReal ω) (ρ t) φ - flucPair (X 0 ω) (ρ 0) (F 0) -
      empiricalMartingale P ℱ W' D t F X (Real.toNNReal t) ω := by
    filter_upwards [hdual] with ω h
    rw [h]; ring
  have hIint : Integrable Iω P := ((hPt.sub hP0).sub hMint).congr hIae.symm
  have hEq : ∫ ω, flucPair (X t.toNNReal ω) (ρ t) φ ∂P =
      ∫ ω, flucPair (X 0 ω) (ρ 0) (F 0) ∂P + ∫ ω, Iω ω ∂P := by
    have h := integral_congr_ae hdual
    have e1 := integral_add (μ := P) (f := fun ω => flucPair (X 0 ω) (ρ 0) (F 0) +
      empiricalMartingale P ℱ W' D t F X (Real.toNNReal t) ω) (g := Iω) (hP0.add hMint) hIint
    have e2 := integral_add (μ := P) (f := fun ω => flucPair (X 0 ω) (ρ 0) (F 0))
      (g := fun ω => empiricalMartingale P ℱ W' D t F X (Real.toNNReal t) ω) hP0 hMint
    rw [h, e1, e2, hMzero]; ring
  have hEI : ∫ ω, Iω ω ∂P = -∫ r in (0 : ℝ)..t, m r := by
    have : ∫ ω, Iω ω ∂P = ∫ ω, (-∫ r in (0 : ℝ)..t, Fm d D.s F ρ X r ω) ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => hIeq ω)
    rw [this, integral_neg, hswap]
  have hmI : IntervalIntegrable m volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht0]
    exact hintFm.integral_prod_left
  filter_upwards [hdual, hintFm.prod_left_ae] with ω h hω
  have hFmI : IntervalIntegrable (fun r => Fm d D.s F ρ X r ω) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht0]
    exact hω
  have hR : integratedRemainder D ρ P X t φ ω =
      Real.sqrt N * ((∫ r in (0 : ℝ)..t, Fm d D.s F ρ X r ω) - ∫ r in (0 : ℝ)..t, m r) := by
    rw [hReq ω, intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hFmI hmI]
  have hz1 := q40b_zeta_eq hN0 (P := P) (X := X) t hXt hφc (ρ t) ω
  have hz0 := q40b_zeta_eq hN0 (P := P) (X := X) 0 hX0' hF0c (ρ 0) ω
  simp only [Real.toNNReal_zero] at hz0
  rw [hz1, hz0, hR, hEq, hEI]
  rw [h, hIeq ω]
  ring

end Identity

end HRS.Q40b
