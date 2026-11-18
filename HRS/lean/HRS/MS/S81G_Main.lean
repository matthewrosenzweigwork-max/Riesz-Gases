import HRS.MS.S81G_Sing
import HRS.MS.S81G_Conv
import HRS.MS.S81G_Ent
import HRS.MS.S81G_Mom
import HRS.MS.S81G_Smooth
import HRS.MS.S81G_Couple

/-!
# S81G, packet G6: `GibbsEntropyContraction` and `GibbsInvariant` (frozen predicates of `HRS/Whole/Headline.lean`)

Proof (Pro paper S81, smooth approximation and one-sided domination), with the S.B.1 machinery for the smooth level:
1. `canonicalGibbs = sb1Gam D g N` (G1); `Γ_M = sb1Gam D k_M N`, `k_M` truncated Riesz kernels (G2): `Z ≤ Z_M → Z`,
   `Γ_M → Γ` setwise, `(Z/Z_M) Γ ≤ Γ_M`.
2. `H(ν₀ | Γ_M) ≤ H(ν₀ | Γ) + log (Z_M/Z)` (G3, one-sided domination), `ν₀` has a finite second moment (G3b).
3. `H(law Y^M_t | Γ_M) ≤ H(ν₀ | Γ_M)` for the regularised flow of the arbitrary initial law `ν₀` (G4).
4. `Y^M = X` on `[0,T]` for `M ≥ M(ω)` a.s. on the original space (G5), so the laws converge setwise;
   joint lower semicontinuity of `klDiv` (`p4lm_klDiv_liminf`) gives `H(law X_t | Γ) ≤ liminf H(law Y^M_t | Γ_M) ≤ H(ν₀ | Γ)`.
Parameter hypotheses (not part of the predicates): `1 ≤ d`, `0 ≤ s`, `0 < a`, `0 < β`; `d ≥ 2`, `s < d`, `N ≥ 2` are not needed.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open HRS HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl HRS.MS.MfeConf HRS.MD.EQLawPath
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S81G

variable {d N : ℕ}

theorem s81g_core (D : Whole.WholeDyn d) (H : S81Hyp D) (hM : D.M = -1) {B : ℝ} (P : Sb1Pot D.V B)
    {T : ℝ} (hT : 0 < T)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} (hW : IsVectorBrownian Pm W)
    {X₀ : Ω → Whole.EucConfig d N} {X : ℝ≥0 → Ω → Whole.EucConfig d N}
    (hX : Whole.IsWholeStrongSolution Pm D T X₀ W X)
    (hind : IndepFun X₀ (fun ζ t => W t ζ) Pm) {t : ℝ≥0} (ht : (t : ℝ) ≤ T) :
    klDiv (Pm.map (X t)) (sb1Gam D (Whole.rieszKernel d D.s) N) ≤
      klDiv (Pm.map (X 0)) (sb1Gam D (Whole.rieszKernel d D.s) N) := by
  by_cases hfin : klDiv (Pm.map (X 0)) (sb1Gam D (Whole.rieszKernel d D.s) N) = ⊤
  · rw [hfin]; exact le_top
  obtain ⟨cV, CV, hcV, hV⟩ := H.conf
  haveI hΓp := s81g_sing_prob (N := N) H
  haveI hν : IsProbabilityMeasure (Pm.map (X 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hX.adapted 0).aemeasurable).2 inferInstance
  haveI hRp : ∀ M : ℕ, IsProbabilityMeasure (sb1Gam D (sb1kM d D.s M) N) := fun M => s81g_reg_prob H M
  have hmom := s81g_second_moment H.invβ_pos (s81g_sing_meas H) (s81g_riesz_lower H.s_nonneg) hcV hV
    (Pm.map (X 0)) hfin
  obtain ⟨ℱ, W', hB, Ys, hmeas, hlaw, hae, hset⟩ := s81g_couple D hM H.s_nonneg P hT hW hX hind
  have hzs := s81g_sing_gz_pos (N := N) H
  have hdomM : ∀ M : ℕ, klDiv (Pm.map (X 0)) (sb1Gam D (sb1kM d D.s M) N) ≠ ⊤ ∧
      (klDiv (Pm.map (X 0)) (sb1Gam D (sb1kM d D.s M) N)).toReal ≤
        (klDiv (Pm.map (X 0)) (sb1Gam D (Whole.rieszKernel d D.s) N)).toReal -
          Real.log (sb1Gz D (Whole.rieszKernel d D.s) N / sb1Gz D (sb1kM d D.s M) N) := fun M =>
    s81g_kl_dom (Pm.map (X 0)) (sb1Gam D (Whole.rieszKernel d D.s) N) (sb1Gam D (sb1kM d D.s M) N)
      (div_pos hzs (s81g_reg_gz_pos H M)) (s81g_gam_dom H M) hfin
  have hτ0 : (0 : ℝ) ≤ (t : ℝ) := t.2
  have hτX : Real.toNNReal (t : ℝ) = t := Real.toNNReal_coe
  have hsm : ∀ M : ℕ, klDiv (Pm.map (Ys M (t : ℝ))) (sb1Gam D (sb1kM d D.s M) N) ≤
      klDiv (Pm.map (X 0)) (sb1Gam D (sb1kM d D.s M) N) := fun M => by
    rw [hlaw M (t : ℝ) hτ0]
    exact s81g_smooth_contraction D (sb1kM_isKernel D.s H.s_nonneg M) P H.invβ_pos hcV hV
      (Pm.map (X 0)) hmom (hdomM M).1 hB hτ0
  haveI hμp : IsProbabilityMeasure (Pm.map (X t)) :=
    (Measure.isProbabilityMeasure_map_iff (hX.adapted t).aemeasurable).2 inferInstance
  haveI hμnp : ∀ M : ℕ, IsProbabilityMeasure (Pm.map (Ys M (t : ℝ))) := fun M =>
    (Measure.isProbabilityMeasure_map_iff (hmeas M _).aemeasurable).2 inferInstance
  have hsetw : ∀ A : Set (Whole.EucConfig d N), MeasurableSet A →
      Tendsto (fun M : ℕ => Pm.map (Ys M (t : ℝ)) A) atTop (𝓝 (Pm.map (X t) A)) := fun A hA => by
    have := hset (t : ℝ) hτ0 ht A hA
    rwa [hτX] at this
  have hlsc := p4lm_klDiv_liminf (μ := Pm.map (X t)) (ρ := sb1Gam D (Whole.rieszKernel d D.s) N)
    (μn := fun M : ℕ => Pm.map (Ys M (t : ℝ))) (ρn := fun M : ℕ => sb1Gam D (sb1kM d D.s M) N)
    (fun ψ hψ ⟨C, hC⟩ => p4m_setwise_integral hsetw hψ hC)
    (fun ψ hψ ⟨C, hC⟩ => p4m_setwise_integral (fun A hA => s81g_gam_setwise H hA) hψ hC)
  set K : ℝ := (klDiv (Pm.map (X 0)) (sb1Gam D (Whole.rieszKernel d D.s) N)).toReal with hK
  have hbound : ∀ M : ℕ, klDiv (Pm.map (Ys M (t : ℝ))) (sb1Gam D (sb1kM d D.s M) N) ≤
      ENNReal.ofReal (K - Real.log (sb1Gz D (Whole.rieszKernel d D.s) N / sb1Gz D (sb1kM d D.s M) N)) :=
    fun M => by
      calc _ ≤ klDiv (Pm.map (X 0)) (sb1Gam D (sb1kM d D.s M) N) := hsm M
        _ = ENNReal.ofReal (klDiv (Pm.map (X 0)) (sb1Gam D (sb1kM d D.s M) N)).toReal :=
          (ENNReal.ofReal_toReal (hdomM M).1).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal (hdomM M).2
  have hc1 : Tendsto (fun M : ℕ => sb1Gz D (Whole.rieszKernel d D.s) N / sb1Gz D (sb1kM d D.s M) N) atTop
      (𝓝 1) := by
    have := (tendsto_const_nhds (x := sb1Gz D (Whole.rieszKernel d D.s) N)).div (s81g_Z_tendsto H) hzs.ne'
    rwa [div_self hzs.ne'] at this
  have hlog : Tendsto (fun M : ℕ =>
      Real.log (sb1Gz D (Whole.rieszKernel d D.s) N / sb1Gz D (sb1kM d D.s M) N)) atTop (𝓝 0) := by
    have := ((Real.continuousAt_log one_ne_zero).tendsto).comp hc1
    simpa [Function.comp_def, Real.log_one] using this
  have hlim : Tendsto (fun M : ℕ => ENNReal.ofReal (K -
      Real.log (sb1Gz D (Whole.rieszKernel d D.s) N / sb1Gz D (sb1kM d D.s M) N))) atTop
      (𝓝 (ENNReal.ofReal K)) := by
    refine ENNReal.tendsto_ofReal ?_
    simpa using (tendsto_const_nhds (x := K)).sub hlog
  calc klDiv (Pm.map (X t)) (sb1Gam D (Whole.rieszKernel d D.s) N)
      ≤ liminf (fun M : ℕ => klDiv (Pm.map (Ys M (t : ℝ))) (sb1Gam D (sb1kM d D.s M) N)) atTop := hlsc
    _ ≤ liminf (fun M : ℕ => ENNReal.ofReal (K -
          Real.log (sb1Gz D (Whole.rieszKernel d D.s) N / sb1Gz D (sb1kM d D.s M) N))) atTop :=
        liminf_le_liminf (Eventually.of_forall hbound)
    _ = ENNReal.ofReal K := hlim.liminf_eq
    _ = klDiv (Pm.map (X 0)) (sb1Gam D (Whole.rieszKernel d D.s) N) := ENNReal.ofReal_toReal hfin

/-- **`GibbsEntropyContraction`** (frozen predicate of `HRS/Whole/Headline.lean`) -/
theorem s81g_gibbsEntropyContraction (hd : 1 ≤ d) {s a β : ℝ} (hs : 0 ≤ s) (ha : 0 < a) (hβ : 0 < β) :
    Whole.GibbsEntropyContraction d s a β N := by
  intro Ω' _ P' _ T X₀' W' X' hW hind hX t ht
  set D : Whole.WholeDyn d := Whole.quadraticGradientDyn d s a β with hD
  have hDi : D.invβ = β⁻¹ := rfl
  have hDM : D.M = -1 := rfl
  have H : S81Hyp D :=
    ⟨hs, hd, by rw [hDi]; exact inv_pos.2 hβ,
      show Continuous (Whole.confinement a : Euc d → ℝ) from
        (continuous_const.mul (continuous_norm.pow 2)).div_const 2,
      ⟨a / 2, 0, by positivity, fun x => s81g_conf_lower a x⟩⟩
  obtain ⟨B, P⟩ := s81g_pot (d := d) a
  have hΓ : Whole.canonicalGibbs (Whole.rieszKernel d s) (Whole.confinement a) N β =
      sb1Gam D (Whole.rieszKernel d D.s) N :=
    s81g_canonical_eq (D := D) (k := Whole.rieszKernel d D.s) (by rw [hDi, inv_inv])
      (s81g_riesz_even s) (s81g_sing_gz_pos H)
  have hlaw0 : Measure.map (X' 0) P' = Measure.map X₀' P' := Measure.map_congr hX.init
  show klDiv (law P' (X' t)) (Whole.canonicalGibbs (Whole.rieszKernel d s) (Whole.confinement a) N β) ≤
    klDiv (law P' X₀') (Whole.canonicalGibbs (Whole.rieszKernel d s) (Whole.confinement a) N β)
  rw [hΓ]
  change klDiv (Measure.map (X' t) P') _ ≤ klDiv (Measure.map X₀' P') _
  rw [← hlaw0]
  by_cases h0 : (t : ℝ) = 0
  · have : t = 0 := by exact_mod_cast h0
    subst this
    exact le_rfl
  · have htpos : (0 : ℝ) < t := lt_of_le_of_ne t.2 (Ne.symm h0)
    exact s81g_core D H hDM P (htpos.trans_le ht) hW hX hind ht

/-- **`GibbsInvariant`** (frozen predicate of `HRS/Whole/Headline.lean`) -/
theorem s81g_gibbsInvariant (hd : 1 ≤ d) {s a β : ℝ} (hs : 0 ≤ s) (ha : 0 < a) (hβ : 0 < β) :
    Whole.GibbsInvariant d s a β N := by
  intro Ω' _ P' _ T X₀' W' X' hW hind hlaw hX t ht
  have hC : Whole.GibbsEntropyContraction d s a β N := s81g_gibbsEntropyContraction hd hs ha hβ
  unfold Whole.GibbsEntropyContraction at hC
  have h1 := @hC Ω' _ P' _ T X₀' W' X' hW hind hX t ht
  set D : Whole.WholeDyn d := Whole.quadraticGradientDyn d s a β with hD
  have hDi : D.invβ = β⁻¹ := rfl
  have H : S81Hyp D :=
    ⟨hs, hd, by rw [hDi]; exact inv_pos.2 hβ,
      show Continuous (Whole.confinement a : Euc d → ℝ) from
        (continuous_const.mul (continuous_norm.pow 2)).div_const 2,
      ⟨a / 2, 0, by positivity, fun x => s81g_conf_lower a x⟩⟩
  have hΓ : Whole.canonicalGibbs (Whole.rieszKernel d s) (Whole.confinement a) N β =
      sb1Gam D (Whole.rieszKernel d D.s) N :=
    s81g_canonical_eq (D := D) (k := Whole.rieszKernel d D.s) (by rw [hDi, inv_inv])
      (s81g_riesz_even s) (s81g_sing_gz_pos H)
  haveI hΓp := s81g_sing_prob (N := N) H
  haveI : IsProbabilityMeasure (law P' (X' t)) :=
    (Measure.isProbabilityMeasure_map_iff (hX.adapted t).aemeasurable).2 inferInstance
  unfold HRS.relEntropy at h1
  rw [hlaw, hΓ, klDiv_self] at h1
  have h2 : klDiv (law P' (X' t)) (sb1Gam D (Whole.rieszKernel d D.s) N) = 0 :=
    le_antisymm (by simpa using h1) bot_le
  rw [hΓ]
  exact klDiv_eq_zero_iff.1 h2

end HRS.MS.S81G
