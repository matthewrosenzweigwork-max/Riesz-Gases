import HRS.MS.ShiftFldAux5

/-!
# S79: `s79_core`, the deterministic-shift comparison for a window `[a₀, a₀ + T]`

Given the exactly centered window `ζ_N^{a₀+·}` and a Gaussian window `Z^{a₀+·}` with `ζ_N^{a₀+·}` and `Z^{a₀+·}` a.e. measurable,
the mean-field-centered window `η_N^{a₀+·} = √N(μ_N^{a₀+·} - μ)` is a.e. measurable and
`d_{C_b²}(Law η, Law(Z + N^{3/2-p} 𝐛)) ≤ d_{C_b²}(Law ζ, Law Z) + K N^{3/2-p-θ}`,
`W_1(Law η, Law(Z + N^{3/2-p} 𝐛)) ≤ W_1(Law ζ, Law Z) + K N^{3/2-p-θ}`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Whole.S79

open HRS (Euc)

variable {d : ℕ} {s : ℝ}

theorem s79_core (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {m : ℝ} (hmd : (d : ℝ) < m) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (T a₀ : ℝ) (ρβ : Euc d → ℝ), IsThermalEquilibrium d s a β ρβ →
      ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
        IsCanonicalRealization d s a β N P X₀ W X →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → OscDual d m),
        AEMeasurable (zetaPathW m T a₀ P X) P → AEMeasurable (processWindow m T a₀ Z) P' →
        AEMeasurable (flucPathW m T a₀ (Real.sqrt N) X (fun _ => ρβ)) P ∧
        AEMeasurable (fun ζ' => processWindow m T a₀ Z ζ' +
          constPath m T ((N : ℝ) ^ (3 / 2 - biasP d s) • biasField m d s β ρβ)) P' ∧
        HRS.smoothDist 2 (HRS.law P (flucPathW m T a₀ (Real.sqrt N) X (fun _ => ρβ)))
            (HRS.law P' (fun ζ' => processWindow m T a₀ Z ζ' +
              constPath m T ((N : ℝ) ^ (3 / 2 - biasP d s) • biasField m d s β ρβ))) ≤
          HRS.smoothDist 2 (HRS.law P (zetaPathW m T a₀ P X)) (HRS.law P' (processWindow m T a₀ Z)) +
            K * (N : ℝ) ^ (3 / 2 - biasP d s - biasTheta d s) ∧
        HRS.wassersteinE 1 (HRS.law P (flucPathW m T a₀ (Real.sqrt N) X (fun _ => ρβ)))
            (HRS.law P' (fun ζ' => processWindow m T a₀ Z ζ' +
              constPath m T ((N : ℝ) ^ (3 / 2 - biasP d s) • biasField m d s β ρβ))) ≤
          HRS.wassersteinE 1 (HRS.law P (zetaPathW m T a₀ P X))
              (HRS.law P' (processWindow m T a₀ Z)) +
            ENNReal.ofReal (K * (N : ℝ) ^ (3 / 2 - biasP d s - biasTheta d s)) := by
  obtain ⟨K, hK0, hK⟩ := s79_shift_remainder hd hs hsd ha hβ hmd (s := s)
  refine ⟨K, hK0, ?_⟩
  intro T a₀ ρβ hρβ N hN Ω _ P _ X₀ W X hR Ω' _ P' _ Z hzm hZm
  have hN1 : 1 ≤ N := by omega
  obtain ⟨hGprob, hrem⟩ := hK N hN ρβ hρβ
  set G := canonicalGibbs (rieszKernel d s) (confinement a) N β with hG
  haveI := hGprob
  haveI hμ : IsProbabilityMeasure (withDensityReal ρβ) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hρβ.2.1
  haveI : IsProbabilityMeasure (meanEmpirical G) := meanEmpirical_isProbabilityMeasure G hN1
  set μ := withDensityReal ρβ with hμdef
  set cc : OscDual d m := Real.sqrt N • OscDual.ofMeasureDiff m (meanEmpirical G) μ with hcc
  set c' : OscDual d m := (N : ℝ) ^ (3 / 2 - biasP d s) • biasField m d s β ρβ with hc'
  have hzeta_eq : ∀ ζ, zetaPathW m T a₀ P X ζ =
      windowPathOf m T a₀ (fun t => zetaB m G (X (Real.toNNReal t) ζ)) := by
    intro ζ
    unfold zetaPathW
    simp only [s79_law_X_eq hR]
    rfl
  have hfl_eq : ∀ ζ, flucPathW m T a₀ (Real.sqrt N) X (fun _ => ρβ) ζ =
      windowPathOf m T a₀ (fun t => zetaB m G (X (Real.toNNReal t) ζ) + cc) := by
    intro ζ
    unfold flucPathW
    congr 1
    funext t
    exact eta_eq_zeta_add m hmd G μ (X (Real.toNNReal t) ζ) hN1
  have hae : ∀ᵐ ζ ∂P, flucPathW m T a₀ (Real.sqrt N) X (fun _ => ρβ) ζ =
      zetaPathW m T a₀ P X ζ + constPath m T cc := by
    filter_upwards [(hR.solution 0).cont] with ζ hζ
    rw [hfl_eq, hzeta_eq]
    apply s79_windowPathOf_add_const
    exact (s79_continuous_window (by omega) hmd (meanEmpirical G) a₀ T (fun t => X t ζ)
      (continuous_pi hζ)).const_smul (Real.sqrt N)
  have hflm : AEMeasurable (flucPathW m T a₀ (Real.sqrt N) X (fun _ => ρβ)) P :=
    (hzm.add_const (constPath m T cc)).congr (hae.mono fun ζ h => h.symm)
  have hZ' : AEMeasurable (fun ζ' => processWindow m T a₀ Z ζ' + constPath m T c') P' :=
    hZm.add_const (constPath m T c')
  have hlaw1 : HRS.law P (flucPathW m T a₀ (Real.sqrt N) X (fun _ => ρβ)) =
      (HRS.law P (zetaPathW m T a₀ P X)).map (· + constPath m T cc) := by
    unfold HRS.law
    rw [Measure.map_congr hae]
    exact (AEMeasurable.map_map_of_aemeasurable (measurable_add_const _).aemeasurable hzm).symm
  have hlawZ : ∀ w : OscPath d m T, HRS.law P' (fun ζ' => processWindow m T a₀ Z ζ' + w) =
      (HRS.law P' (processWindow m T a₀ Z)).map (· + w) := by
    intro w
    unfold HRS.law
    exact (AEMeasurable.map_map_of_aemeasurable (measurable_add_const _).aemeasurable hZm).symm
  have hnorm : ‖constPath m T cc - constPath m T c'‖ ≤
      K * (N : ℝ) ^ (3 / 2 - biasP d s - biasTheta d s) := by
    refine le_trans ?_ hrem
    refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun t => ?_
    exact le_rfl
  refine ⟨hflm, hZ', ?_, ?_⟩
  · rw [hlaw1, hlawZ]
    exact (s79_smoothDist_shifted_le _ _ _ _).trans (add_le_add le_rfl hnorm)
  · rw [hlaw1, hlawZ]
    calc HRS.wassersteinE 1 ((HRS.law P (zetaPathW m T a₀ P X)).map (· + constPath m T cc))
          ((HRS.law P' (processWindow m T a₀ Z)).map (· + constPath m T c'))
        ≤ HRS.wassersteinE 1 ((HRS.law P (zetaPathW m T a₀ P X)).map (· + constPath m T cc))
            ((HRS.law P' (processWindow m T a₀ Z)).map (· + constPath m T cc)) +
          HRS.wassersteinE 1 ((HRS.law P' (processWindow m T a₀ Z)).map (· + constPath m T cc))
            ((HRS.law P' (processWindow m T a₀ Z)).map (· + constPath m T c')) :=
          HRS.wassersteinE_triangle 1 le_rfl _ _ _
      _ ≤ HRS.wassersteinE 1 (HRS.law P (zetaPathW m T a₀ P X))
              (HRS.law P' (processWindow m T a₀ Z)) +
            ENNReal.ofReal (K * (N : ℝ) ^ (3 / 2 - biasP d s - biasTheta d s)) := by
          refine add_le_add (s79_wassersteinE_map_add_le 1 _ _ _) ?_
          rw [← hlawZ, ← hlawZ]
          exact (HRS.wassersteinE_translate P' 1 le_rfl _ hZm _ _).trans
            (ENNReal.ofReal_le_ofReal (by simpa using hnorm.trans' (le_refl _)))

end HRS.Whole.S79
