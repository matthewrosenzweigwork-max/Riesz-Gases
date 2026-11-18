import HRS.MP.SelfSimP5LimB
import HRS.MP.SelfSimP4Limit

/-!
# MPP5D (10c): Fisher lower semicontinuity, measurability in time, bookkeeping; `ss5_limit`

`HRS.MP.SelfSimP5Impl.ss5_limit_proof` has the statement of `HRS.MP.SelfSimP5.ss5_limit`.  Namespace
`HRS.MP.SelfSimP5Impl`, helpers `ss5l_`.

Route.  For a configuration test field `ζ` (compact support `K` away from collisions) and a fixed time `r`, the law of
`Y_r` is carried by the closed cone.  A cut-off `χ` (equal to `1` near the chamber image of `K ∩ closed cone`, compactly
supported in the open chamber, `ss5l_choose`) gives a smooth compactly supported chamber field `η = χ · (toCh ∘ ζ ∘ unrank)`
with the same Fisher integrand on the closed chamber (`ss5l_integrand_eq`), which for `ε_n` below the minimal gap of
`supp χ` no longer depends on `n` (`ss5l_gradU_eq`): the functionals are continuous under narrow convergence
(`ss5l_narrow`), so `𝓘_Ḡ(law Y_r) ≤ liminf 𝓘_{U_n}(law Z^n_r)` (`ss5l_fisher_lsc`).  The level Fisher information is
lower semicontinuous, hence measurable, in `r` (`ss5l_fish_aemeasurable`).  The final assembly uses the entropy lower
semicontinuity of `SelfSimP5LimB`, the initial bound `ss5_initial_bound_proof` and the bookkeeping
`p4_limit_bookkeeping_proof` (Fatou in `r`, `liminf` in `EReal`).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open HRS HRS.MP.SelfSimP5 HRS.MP.SelfSim HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MP.SelfSimP5Impl

/-! ### Fisher integrands of test fields -/

theorem ss5l_div_cont {N : ℕ} {η : Ch5 N → Ch5 N} (hη : ContDiff ℝ ∞ η) : Continuous (ss5_div η) := by
  unfold ss5_div
  refine continuous_finsetSum _ fun k _ => ?_
  have hc : ContDiff ℝ ∞ (fun w : Ch5 N => η w k) :=
    (EuclideanSpace.proj k : Ch5 N →L[ℝ] ℝ).contDiff.comp hη
  exact (hc.continuous_fderiv (by simp)).clm_apply continuous_const

theorem ss5l_gradient_cont {N : ℕ} {U : Ch5 N → ℝ} (hU : ContDiff ℝ 2 U) : Continuous (gradient U) := by
  show Continuous fun x => (InnerProductSpace.toDual ℝ (Ch5 N)).symm (fderiv ℝ U x)
  exact (InnerProductSpace.toDual ℝ (Ch5 N)).symm.continuous.comp (hU.continuous_fderiv (by norm_num))

theorem ss5l_fiU_zero {N : ℕ} (θ : ℝ) (U : Ch5 N → ℝ) {η : Ch5 N → Ch5 N} {z : Ch5 N}
    (h : η =ᶠ[𝓝 z] fun _ => 0) : ss5l_fiU θ U η z = 0 := by
  unfold ss5l_fiU
  rw [ss5l_div_zero h, h.self_of_nhds]
  simp

theorem ss5l_fiU_props {N : ℕ} (θ : ℝ) {U : Ch5 N → ℝ} (hU : ContDiff ℝ 2 U) {η : Ch5 N → Ch5 N}
    (hη : ss5_IsTestField η) :
    Continuous (ss5l_fiU θ U η) ∧ HasCompactSupport (ss5l_fiU θ U η) := by
  refine ⟨?_, ?_⟩
  · unfold ss5l_fiU
    have hc : Continuous η := hη.smooth.continuous
    refine Continuous.sub (Continuous.add (continuous_const.mul (ss5l_div_cont hη.smooth)) ?_) ?_
    · exact continuous_const.mul ((ss5l_gradient_cont hU).inner hc)
    · exact hc.norm.pow 2
  · refine HasCompactSupport.intro hη.compact fun z hz => ?_
    exact ss5l_fiU_zero θ U (notMem_tsupport_iff_eventuallyEq.1 hz)

/-! ### Narrow convergence from almost sure convergence -/

theorem ss5l_narrow {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q] {N : ℕ}
    {X : ℕ → Ω → Ch5 N} {X' : Ω → Ch5 N} (hX : ∀ n, Measurable (X n)) (hX' : Measurable X')
    (hlim : ∀ᵐ ζ ∂Q, Tendsto (fun n => X n ζ) atTop (𝓝 (X' ζ))) :
    ∀ ψ : Ch5 N → ℝ, Continuous ψ → (∃ C, ∀ x, |ψ x| ≤ C) →
      Tendsto (fun n => ∫ x, ψ x ∂(Q.map (X n))) atTop (𝓝 (∫ x, ψ x ∂(Q.map X'))) := by
  intro ψ hψ ⟨C, hC⟩
  simp_rw [integral_map (hX _).aemeasurable hψ.aestronglyMeasurable]
  rw [integral_map hX'.aemeasurable hψ.aestronglyMeasurable]
  refine tendsto_integral_of_dominated_convergence (fun _ => C)
    (fun n => (hψ.measurable.comp (hX n)).aestronglyMeasurable) (integrable_const C)
    (fun n => Eventually.of_forall fun ζ => ?_) ?_
  · simpa [Real.norm_eq_abs] using hC (X n ζ)
  · filter_upwards [hlim] with ζ hζ
    exact (hψ.tendsto _).comp hζ

/-! ### Lower semicontinuity of the Fisher information -/

theorem ss5l_gradU_eq {N : ℕ} {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε') {z : Ch5 N}
    (h1 : ∀ k l : Fin N, k < l → ε ≤ z l - z k) (h2 : ∀ k l : Fin N, k < l → ε' ≤ z l - z k) :
    gradient (ss5_U N ε) z = gradient (ss5_U N ε') z := by
  rw [ss5t_gradient_U hε, ss5t_gradient_U hε']
  congr 1
  unfold ss5t_pairGrad
  congr 1
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  by_cases hkl : k < l
  · simp only [hkl, ite_true]
    unfold ss5t_d1
    rw [if_pos (h1 k l hkl), if_pos (h2 k l hkl)]
  · simp [hkl]


theorem ss5l_chiTest {N : ℕ} (σ : Equiv.Perm (Fin N)) {ζ : EucConfig 1 N → EucConfig 1 N}
    (hζ : ContDiff ℝ ∞ ζ) {χ : Ch5 N → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    ss5_IsTestField (fun z : Ch5 N => χ z • ss5_toCh σ (ζ (ss5l_unrank σ z))) := by
  refine ⟨?_, ?_⟩
  · have h1 : ContDiff ℝ ∞ (fun z : Ch5 N => ss5_toCh σ (ζ (ss5l_unrank σ z))) :=
      (ss5l_toChL σ).contDiff.comp (hζ.comp (ss5l_unrankL σ).contDiff)
    exact hχ.smul h1
  · exact HasCompactSupport.smul_right (f := χ) (f' := fun z : Ch5 N => ss5_toCh σ (ζ (ss5l_unrank σ z))) hχc

/-- **Fisher information lower semicontinuity** for a fixed time. -/
theorem ss5l_fisher_lsc {N : ℕ} (hN : 0 < N) (σ : Equiv.Perm (Fin N)) {θ : ℝ} (hθ : 0 < θ)
    (ν : Measure (EucConfig 1 N)) [IsProbabilityMeasure ν]
    (hνc : ∀ᵐ ξ ∂ν, ss5_toCh σ ξ ∈ ss5l_cch N) (μn : ℕ → Measure (Ch5 N))
    [∀ n, IsProbabilityMeasure (μn n)]
    (hconv : ∀ ψ : Ch5 N → ℝ, Continuous ψ → (∃ C, ∀ x, |ψ x| ≤ C) →
      Tendsto (fun n => ∫ x, ψ x ∂(μn n)) atTop (𝓝 (∫ x, ψ x ∂(ν.map (ss5_toCh σ))))) :
    fisherInfoW (selfSimWeight 1 0 θ N 0) ν ≤
      liminf (fun n => ss5_fish θ (ss5_U N (ss5_eps n)) (μn n)) atTop := by
  have hT : Measurable (ss5_toCh σ : EucConfig 1 N → Ch5 N) := (ss5i_toCh_mp σ).measurable
  unfold fisherInfoW
  refine iSup₂_le fun ζ hζ => ?_
  obtain ⟨K, hK, hKd, hKz⟩ := hζ.support
  obtain ⟨χ, hχs, hχc, hχC, ⟨δ, hδ, hgapδ⟩, hχ1⟩ := ss5l_choose σ hK hKd
  obtain ⟨n0, hn0⟩ := exists_nat_one_div_lt hδ
  have hε0 : 0 < ss5_eps n0 := ss5_eps_pos n0
  have hεδ : ss5_eps n0 < δ := by unfold ss5_eps; exact hn0
  set η : Ch5 N → Ch5 N := fun z => χ z • ss5_toCh σ (ζ (ss5l_unrank σ z)) with hη
  have hηt : ss5_IsTestField η := ss5l_chiTest σ hζ.smooth hχs hχc
  have hUc : ContDiff ℝ 2 (ss5_U N (ss5_eps n0)) := ss5t_contDiff_U hε0
  obtain ⟨hJc, hJs⟩ := ss5l_fiU_props θ hUc hηt
  -- the configuration integrand is `J ∘ toCh` on the closed chamber
  have hK1 : ∀ ξ ∈ K, ss5_toCh σ ξ ∈ ss5l_cch N → (χ =ᶠ[𝓝 (ss5_toCh σ ξ)] fun _ => 1) ∧
      ∀ k l : Fin N, k < l → ss5_eps n0 < ss5_toCh σ ξ l - ss5_toCh σ ξ k := by
    intro ξ hξ hcc
    have h1 := hχ1 ξ hξ hcc
    refine ⟨h1, fun k l hkl => lt_of_lt_of_le hεδ (hgapδ _ ?_ k l hkl)⟩
    refine subset_tsupport _ ?_
    have := h1.self_of_nhds
    simp only [Function.mem_support, this]
    exact one_ne_zero
  have hint : ∫ ξ, ss5l_fiC N θ ζ ξ ∂ν =
      ∫ z, ss5l_fiU θ (ss5_U N (ss5_eps n0)) η z ∂(ν.map (ss5_toCh σ)) := by
    rw [integral_map hT.aemeasurable hJc.aestronglyMeasurable]
    refine integral_congr_ae ?_
    filter_upwards [hνc] with ξ hξ
    exact ss5l_integrand_eq σ θ hζ.smooth hK.isClosed hKz hε0 hK1 ξ hξ
  -- the level integrands are eventually equal to `J`
  have hev : ∀ n, n0 ≤ n → ss5l_fiU θ (ss5_U N (ss5_eps n)) η =
      ss5l_fiU θ (ss5_U N (ss5_eps n0)) η := by
    intro n hn
    funext z
    unfold ss5l_fiU
    by_cases hχz : χ z = 0
    · have : η z = 0 := by simp [hη, hχz]
      simp [this]
    · have hz : z ∈ tsupport χ := subset_tsupport _ hχz
      have hge : ∀ k l : Fin N, k < l → ss5_eps n ≤ z l - z k := fun k l hkl => by
        have h1 : ss5_eps n ≤ ss5_eps n0 := by
          unfold ss5_eps
          exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
        exact h1.trans (hεδ.le.trans (hgapδ z hz k l hkl))
      have hge0 : ∀ k l : Fin N, k < l → ss5_eps n0 ≤ z l - z k := fun k l hkl =>
        hεδ.le.trans (hgapδ z hz k l hkl)
      rw [ss5l_gradU_eq (ss5_eps_pos n) hε0 hge hge0]
  -- narrow convergence of the integrals of `J`
  obtain ⟨C, hC⟩ := hJc.bounded_above_of_compact_support hJs
  have hlim := hconv _ hJc ⟨C, fun x => by simpa [Real.norm_eq_abs] using hC x⟩
  have hlim' := ENNReal.tendsto_ofReal hlim
  show ENNReal.ofReal (∫ ξ, ss5l_fiC N θ ζ ξ ∂ν) ≤ _
  rw [hint]
  rw [← hlim'.liminf_eq]
  refine liminf_le_liminf ?_
  filter_upwards [Filter.eventually_ge_atTop n0] with n hn
  refine le_iSup₂_of_le η hηt ?_
  show ENNReal.ofReal (∫ x, ss5l_fiU θ (ss5_U N (ss5_eps n0)) η x ∂(μn n)) ≤
    ENNReal.ofReal (∫ x, ss5l_fiU θ (ss5_U N (ss5_eps n)) η x ∂(μn n))
  rw [hev n hn]


/-! ### Measurability in time of the level Fisher information -/

theorem ss5l_fish_aemeasurable {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    {N : ℕ} (θ : ℝ) {U : Ch5 N → ℝ} (hU : ContDiff ℝ 2 U) {Z : ℝ → Ω → Ch5 N}
    (hZc : ∀ ζ, Continuous fun t => Z t ζ) (hZm : ∀ t, 0 ≤ t → Measurable (Z t)) (S : ℝ) :
    AEMeasurable (fun r => ss5_fish θ U (Q.map (Z r))) (volume.restrict (Icc (0 : ℝ) S)) := by
  have hL : LowerSemicontinuous (fun r : ℝ => ss5_fish θ U (Q.map (Z (max r 0)))) := by
    unfold ss5_fish
    refine lowerSemicontinuous_biSup (fun ζ hζ => ?_)
    obtain ⟨hc, hs⟩ := ss5l_fiU_props θ hU hζ
    obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
    have hcont : Continuous fun r : ℝ => ∫ z, ss5l_fiU θ U ζ z ∂(Q.map (Z (max r 0))) := by
      have e : (fun r : ℝ => ∫ z, ss5l_fiU θ U ζ z ∂(Q.map (Z (max r 0)))) =
          fun r => ∫ w, ss5l_fiU θ U ζ (Z (max r 0) w) ∂Q := by
        funext r
        exact integral_map (hZm _ (le_max_right _ _)).aemeasurable hc.aestronglyMeasurable
      rw [e]
      refine continuous_of_dominated (bound := fun _ => C)
        (fun r => (hc.measurable.comp (hZm _ (le_max_right _ _))).aestronglyMeasurable)
        (fun r => Eventually.of_forall fun w => by simpa [Real.norm_eq_abs] using hC (Z (max r 0) w))
        (integrable_const C) (Eventually.of_forall fun w => ?_)
      exact hc.comp ((hZc w).comp (continuous_id.max continuous_const))
    exact (ENNReal.continuous_ofReal.comp hcont).lowerSemicontinuous
  refine (hL.measurable.aemeasurable).congr ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => ?_)
  simp [max_eq_left hr.1]


/-! ### The passage to the limit -/

/-- **10 (passage to the limit `ε → 0`).**  Statement of `HRS.MP.SelfSimP5.ss5_limit`. -/
theorem ss5_limit_proof (N : ℕ) (hN : 2 ≤ N) (invβ : ℝ) (hβ : 0 < invβ) (S : ℝ) (hS : 0 < S)
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q] (σ : Equiv.Perm (Fin N))
    {Y : ℝ≥0 → Ω → EucConfig 1 N} (hYm : ∀ t, Measurable (Y t))
    (hord : ∀ᵐ ζ ∂Q, ∀ t : ℝ≥0, (t : ℝ) ≤ S → ∀ k k' : Fin N, k ≤ k' → Y t ζ (σ k) 0 ≤ Y t ζ (σ k') 0)
    (h0 : ∀ᵐ ζ ∂Q, Y 0 ζ ∈ ss5_cone σ)
    {Z : ℕ → ℝ → Ω → Ch5 N} (hZc : ∀ n ζ, Continuous fun t => Z n t ζ)
    (hZm : ∀ n t, 0 ≤ t → Measurable (Z n t))
    (hZ0 : ∀ n, ∀ᵐ ζ ∂Q, Z n 0 ζ = ss5_toCh σ (Y 0 ζ))
    (hconv : ∀ᵐ ζ ∂Q, ∀ t ∈ Icc (0 : ℝ) S,
      Tendsto (fun n => Z n t ζ) atTop (𝓝 (ss5_toCh σ (Y (Real.toNNReal t) ζ))))
    (hdiss : ∀ n, ∀ t ∈ Icc (0 : ℝ) S,
      ss5_ent invβ (ss5_U N (ss5_eps n)) (Q.map (Z n t)) +
        ((ENNReal.ofReal invβ * ∫⁻ r in Icc (0 : ℝ) t,
          ss5_fish invβ (ss5_U N (ss5_eps n)) (Q.map (Z n r)) : ℝ≥0∞) : EReal)
        ≤ ss5_ent invβ (ss5_U N (ss5_eps n)) (Q.map (Z n 0))) :
    SSEntropyIneq 1 0 invβ N S Q Y := by
  have hN0 : 0 < N := by omega
  have hw : ∀ τ : ℝ, selfSimWeight 1 0 invβ N τ = selfSimWeight 1 0 invβ N 0 := by
    intro τ; funext Ξ; simp [selfSimWeight, selfSimPotential, aSelfSim]
  unfold SSEntropyIneq
  simp only [hw]
  have hTc : Measurable (ss5_toCh σ : EucConfig 1 N → Ch5 N) := (ss5h_toCh_continuous σ).measurable
  have hZp : ∀ n t, 0 ≤ t → IsProbabilityMeasure (Q.map (Z n t)) := fun n t ht =>
    (Measure.isProbabilityMeasure_map_iff (hZm n t ht).aemeasurable).2 inferInstance
  have hYp : ∀ t : ℝ≥0, IsProbabilityMeasure (law Q (Y t)) := fun t =>
    (Measure.isProbabilityMeasure_map_iff (hYm t).aemeasurable).2 inferInstance
  have hTY : ∀ t : ℝ≥0, Measurable (fun ζ => ss5_toCh σ (Y t ζ)) := fun t => hTc.comp (hYm t)
  have hlaw : ∀ t : ℝ≥0, (law Q (Y t)).map (ss5_toCh σ) = Q.map (fun ζ => ss5_toCh σ (Y t ζ)) :=
    fun t => Measure.map_map hTc (hYm t)
  have hnarrow : ∀ τ ∈ Icc (0 : ℝ) S, ∀ ψ : Ch5 N → ℝ, Continuous ψ → (∃ C, ∀ x, |ψ x| ≤ C) →
      Tendsto (fun n => ∫ x, ψ x ∂(Q.map (Z n τ))) atTop
        (𝓝 (∫ x, ψ x ∂((law Q (Y (Real.toNNReal τ))).map (ss5_toCh σ)))) := by
    intro τ hτ
    rw [hlaw]
    refine ss5l_narrow Q (X := fun n => Z n τ) (X' := fun ζ => ss5_toCh σ (Y (Real.toNNReal τ) ζ))
      (fun n => hZm n τ hτ.1) (hTY _) ?_
    filter_upwards [hconv] with ζ hζ using hζ τ hτ
  refine HRS.MP.SelfSimP4Impl.p4_limit_bookkeeping_proof (θ := invβ) (S := S)
    (H := fun τ => gibbsEntropyW (selfSimWeight 1 0 invβ N 0) (law Q (Y (Real.toNNReal τ))))
    (HM := fun n τ => ss5_ent invβ (ss5_U N (ss5_eps n)) (Q.map (Z n τ)))
    (I := fun r => fisherInfoW (selfSimWeight 1 0 invβ N 0) (law Q (Y (Real.toNNReal r))))
    (D := fun n r => ss5_fish invβ (ss5_U N (ss5_eps n)) (Q.map (Z n r)))
    (R := gibbsEntropyW (selfSimWeight 1 0 invβ N 0) (law Q (Y 0))) ?_ ?_ ?_ ?_
  · intro n
    exact ss5l_fish_aemeasurable Q invβ (ss5t_contDiff_U (ss5_eps_pos n)) (hZc n) (hZm n) S
  · intro τ hτ
    haveI := hYp (Real.toNNReal τ)
    haveI : ∀ n, IsProbabilityMeasure (Q.map (Z n τ)) := fun n => hZp n τ hτ.1
    exact ss5l_entropy_lsc hN0 σ hβ (law Q (Y (Real.toNNReal τ))) (fun n => Q.map (Z n τ))
      (hnarrow τ hτ)
  · intro r hr
    haveI := hYp (Real.toNNReal r)
    haveI : ∀ n, IsProbabilityMeasure (Q.map (Z n r)) := fun n => hZp n r hr.1
    refine ss5l_fisher_lsc hN0 σ hβ (law Q (Y (Real.toNNReal r))) ?_ (fun n => Q.map (Z n r))
      (hnarrow r hr)
    have hmeas : MeasurableSet {ξ : EucConfig 1 N | ss5_toCh σ ξ ∈ ss5l_cch N} :=
      hTc (ss5l_cch_closed N).measurableSet
    refine (ae_map_iff (hYm _).aemeasurable hmeas).2 ?_
    filter_upwards [hord] with ζ hζ
    intro k l hkl
    exact hζ (Real.toNNReal r) (by rw [Real.coe_toNNReal _ hr.1]; exact hr.2) k l hkl.le
  · intro n τ hτ
    refine (hdiss n τ hτ).trans ?_
    have := ss5_initial_bound_proof N hN invβ hβ Q σ (hYm 0) h0 (ss5_eps_pos n)
    rwa [Measure.map_congr (hZ0 n)]

example := (@ss5_limit_proof : type_of% @HRS.MP.SelfSimP5.ss5_limit)

end HRS.MP.SelfSimP5Impl
