import HRS.MS.MovEntAux18

/-!
# S6.6, packet P5 (part 2): Itô's formula for `N⁻¹∑|x_i|²` along a filtered whole-space strong solution

`s66_ito_m`: the application of `ito_formula_additive_time_independent` to `f = sumLift N |·|²` on `(ℝ^d)^N` (the pattern of
`HRS/MH/DualityRdA4.lean`, with a generic `C²` test function and no boundedness).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovEnt

open HRS.Whole HRS.MH.DualityRd

variable {d : ℕ}

theorem s66_ito_m {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {N : ℕ}
    (D : WholeDyn d) (hVm : Measurable (gradient D.V)) {T : ℝ} (hT : 0 ≤ T)
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : IsWholeStrongSolution P D T X₀ W X)
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hF : IsWholeFilteredSolution P ℱ W' W X) :
    ∀ᵐ ζ ∂P,
      IntegrableOn (fun s : ℝ =>
          fderiv ℝ (HRS.sumLift N (fun x : Euc d => ‖x‖ ^ 2)) (X (Real.toNNReal s) ζ)
            (particleDriftW D (X (Real.toNNReal s) ζ)) +
          (1 / 2) * ∑ k : Fin N × Fin d,
            fderiv ℝ (fderiv ℝ (HRS.sumLift N (fun x : Euc d => ‖x‖ ^ 2))) (X (Real.toNNReal s) ζ)
              (noiseDir D k) (noiseDir D k)) (Set.Icc 0 T) ∧
      ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      HRS.sumLift N (fun x : Euc d => ‖x‖ ^ 2) (X t ζ) =
        HRS.sumLift N (fun x : Euc d => ‖x‖ ^ 2) (X 0 ζ) +
        (∫ s in Set.Icc (0 : ℝ) t,
          fderiv ℝ (HRS.sumLift N (fun x : Euc d => ‖x‖ ^ 2)) (X (Real.toNNReal s) ζ)
            (particleDriftW D (X (Real.toNNReal s) ζ)) +
          (1 / 2) * ∑ k : Fin N × Fin d,
            fderiv ℝ (fderiv ℝ (HRS.sumLift N (fun x : Euc d => ‖x‖ ^ 2))) (X (Real.toNNReal s) ζ)
              (noiseDir D k) (noiseDir D k)) +
        HRS.localItoIntegral P ℱ W'
          (itoIntegrand T Set.univ (fun _ x => HRS.sumLift N (fun x : Euc d => ‖x‖ ^ 2) x)
            (ofNNRealTime X) (fun _ _ => noiseDir D)) t ζ := by
  have hZint : ∀ᵐ ζ ∂P, ∀ τ : ℝ≥0, (τ : ℝ) ≤ T →
      X τ ζ = X 0 ζ + (∫ s in Set.Icc (0 : ℝ) τ, particleDriftW D (X (Real.toNNReal s) ζ))
        + ∑ k, (W' τ ζ k - W' 0 ζ k) • noiseDir D k := by
    filter_upwards [hX.eqn, hF.coords] with ζ h1 h2 τ hτ
    obtain ⟨hI, h1⟩ := h1 τ hτ
    have e : ∀ k : Fin N × Fin d, W' τ ζ k - W' 0 ζ k
        = (fun l => W τ ζ l - W 0 ζ l) k.1 k.2 := by
      intro k
      have h3 := h2 τ k.1 k.2
      have h4 := h2 0 k.1 k.2
      rw [Prod.mk.eta] at h3 h4
      rw [h3, h4]
      simp
    funext i
    have hsum : (∑ k : Fin N × Fin d, (W' τ ζ k - W' 0 ζ k) • noiseDir D k) i
        = Real.sqrt (2 * D.invβ) • (W τ ζ i - W 0 ζ i) := by
      simp only [e]
      exact da4_sum_noiseDir_apply D (fun l => W τ ζ l - W 0 ζ l) i
    have hIi : Integrable (fun s : ℝ => particleDriftW D (X (Real.toNNReal s) ζ)) (volume.restrict (Set.Icc 0 (τ : ℝ))) :=
      integrable_pi_iff.2 hI
    simp only [Pi.add_apply]
    rw [hsum, da4_integral_apply _ i hIi, ← h1 i]
  have hbint : ∀ᵐ ζ ∂P, IntegrableOn (fun s : ℝ => particleDriftW D (X (Real.toNNReal s) ζ)) (Set.Icc 0 T) := by
    filter_upwards [hX.eqn] with ζ h1
    have htt : ((Real.toNNReal T : ℝ≥0) : ℝ) = T := Real.coe_toNNReal T hT
    obtain ⟨hI, -⟩ := h1 (Real.toNNReal T) (le_of_eq htt)
    rw [htt] at hI
    exact integrable_pi_iff.2 hI
  have hX₀ : ∀ s : ℝ, Measurable[ℱ s] (X 0) := by
    intro s
    rcases le_or_gt 0 s with hs | hs
    · exact (hF.adapted 0).mono (ℱ.mono (by simpa using hs)) le_rfl
    · have h := hF.progressive.adapted s
      have e : ofNNRealTime X s = X 0 := by
        funext ξ
        simp [ofNNRealTime_apply, Real.toNNReal_of_nonpos hs.le]
      rw [e] at h
      exact h
  have hb : MeasureTheory.IsProgressive ℱ
      (ofNNRealTime (fun (s : ℝ≥0) (ξ : Ω) => particleDriftW D (X s ξ))) :=
    fun i => (Q09B.q09b_measurable_driftVec D hVm).comp (hF.progressive i)
  have h := ito_formula_additive (P := P) (ℱ := ℱ) hF.brownian hT
    (fun _ x => HRS.sumLift N (fun x : Euc d => ‖x‖ ^ 2) x)
    (isC12On_of_contDiff T Set.univ _ (HRS.contDiff_sumLift (contDiff_norm_sq ℝ)))
    (noiseDir D) X hX.adapted hX₀ (fun (s : ℝ≥0) (ξ : Ω) => particleDriftW D (X s ξ)) hb hbint hZint
  filter_upwards [h] with ζ hζ
  obtain ⟨hI, hEq⟩ := hζ
  have hd : ∀ s : ℝ, itoDrift T (fun _ x => HRS.sumLift N (fun x : Euc d => ‖x‖ ^ 2) x) (ofNNRealTime X)
      (ofNNRealTime (fun (s : ℝ≥0) (ξ : Ω) => particleDriftW D (X s ξ))) (fun _ _ => noiseDir D) s ζ =
      fderiv ℝ (HRS.sumLift N (fun x : Euc d => ‖x‖ ^ 2)) (X (Real.toNNReal s) ζ)
            (particleDriftW D (X (Real.toNNReal s) ζ)) +
          (1 / 2) * ∑ k : Fin N × Fin d,
            fderiv ℝ (fderiv ℝ (HRS.sumLift N (fun x : Euc d => ‖x‖ ^ 2))) (X (Real.toNNReal s) ζ)
              (noiseDir D k) (noiseDir D k) := by
    intro s
    simp [itoDrift]
  refine ⟨?_, fun t ht => ?_⟩
  · refine hI.congr_fun (fun s _ => hd s) measurableSet_Icc
  · rw [hEq t ht]
    congr 2
    exact setIntegral_congr_fun measurableSet_Icc fun s _ => hd s

end HRS.MS.MovEnt

end
