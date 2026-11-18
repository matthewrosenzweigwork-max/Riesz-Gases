import HRS.MS.R2InterpAux133

/-!
# S10.2 (worker S10S), part 134 (packet C2): the time-marginal density bound for an abstract preparation exponent, and for the corner `γ = 0 = s`

`s102_time_density_gen` is `s102_time_density` (Aux78) with the quench density (S9.3) and the well-definedness of `Q_{N,γ}` as hypotheses.
For `γ = 0`, `s = 0` they follow from `s113x_X4_generic` (log-gas normalizer at small negative inverse temperature).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.Wr HRS.MS.PrepStat HRS.MS.R2Mt

variable {d N : ℕ}

theorem s102_time_density_gen (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) (hN : 2 ≤ N)
    (hinv : GibbsInvariant d s a β N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hreal : IsR2Realization d s a β P X₀ W X) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsWholeFilteredSolution P ℱ W' W X)
    (hlaw : P.map X₀ = HRS.Whole.modulatedGibbs (rieszKernel d s) N γ (HRS.Whole.withDensityReal ρ)) (T : ℝ)
    (hW0 : GibbsWellDefined (fun x y => rieszKernel d s (x - y)) N γ (HRS.Whole.withDensityReal ρ))
    (hdensQ : ∃ p K : ℝ, 1 < p ∧ ∀ κ : Kernel (EucConfig d N) (EucConfig d N), IsMarkovKernel κ →
      (HRS.Whole.modulatedGibbs (rieszKernel d s) N β (HRS.Whole.withDensityReal ρ)).bind κ =
        HRS.Whole.modulatedGibbs (rieszKernel d s) N β (HRS.Whole.withDensityReal ρ) →
      HasR2ActualDensity s β p K (HRS.Whole.withDensityReal ρ)
        ((HRS.Whole.modulatedGibbs (rieszKernel d s) N γ (HRS.Whole.withDensityReal ρ)).bind κ)) :
    ∃ p K : ℝ, 1 < p ∧ ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      HasR2ActualDensity s β p K (HRS.Whole.withDensityReal ρ) (P.map (X t)) := by
  classical
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  obtain ⟨M, L, c, hRD, hGU⟩ := HRS.MS.R2S11.s11_thermal_round2 hd hs0 hs ha hβ hρ
  obtain ⟨p, K, hp, hdens⟩ := hdensQ
  refine ⟨p, K, hp, fun t ht => ?_⟩
  set μ := HRS.Whole.withDensityReal ρ with hμ
  haveI hμp : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu hρ.2.1
  -- the Gibbs laws and the tilt
  obtain ⟨C0, hC0, hnorm⟩ := s92_normalizer_bounds hd hs0 hs M L (β / 2) (β + 1) (by positivity) (by linarith)
  obtain ⟨hWb, -⟩ := hnorm ρ hRD N hN β ⟨by linarith, by linarith⟩
  have hGm := wr9_rieszKernel_pair_meas (d := d) s
  have htilt := s32_tilt (G := fun x y => rieszKernel d s (x - y)) (N := N) (μ := μ) (a := γ) (b := β) hGm hW0 hWb
  haveI hQprob : IsProbabilityMeasure (pairGibbs (fun x y => rieszKernel d s (x - y)) N β μ) := wr9_gibbs_prob hWb
  set Q := pairGibbs (fun x y => rieszKernel d s (x - y)) N β μ with hQ
  set φ0 : EucConfig d N → ℝ≥0∞ := fun X => ENNReal.ofReal
    (pairNormalizer (fun x y => rieszKernel d s (x - y)) N β μ /
      pairNormalizer (fun x y => rieszKernel d s (x - y)) N γ μ *
      Real.exp ((-γ * N - -β * N) * pairEnergy (fun x y => rieszKernel d s (x - y)) X μ)) with hφ0
  have hφm : Measurable φ0 :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul (wr9_measurable_pairEnergy hGm))))
  have hφpos : ∀ x, 0 < φ0 x := fun x => by
    simp only [hφ0]
    exact ENNReal.ofReal_pos.2 (mul_pos (div_pos hWb.normalizer_pos hW0.normalizer_pos) (Real.exp_pos _))
  have hφfin : ∀ x, φ0 x ≠ ⊤ := fun x => ENNReal.ofReal_ne_top
  have hQγ : HRS.Whole.modulatedGibbs (rieszKernel d s) N γ μ = Q.withDensity φ0 := htilt.symm
  -- the canonical Gibbs law
  have hρeq : ρ = HRS.Whole.thermalDensity d s a β := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ
  have hcan : HRS.Whole.canonicalGibbs (rieszKernel d s) (HRS.Whole.confinement a) N β = Q := by
    have := HRS.MS.S21.s21_canonical_eq hd hs0 hsd ha hβ N
    rw [this]
    simp only [hQ, hμ, hρeq]
    rfl
  set Wt := s102_Wt W' with hWt
  have hae : ∀ᵐ ζ ∂P, ∀ t, Wt t ζ = W t ζ := by
    filter_upwards [hF.coords] with ζ h t
    funext i
    ext j
    exact h t i j
  have hcont : ∀ᵐ ζ ∂P, ∀ i j, Continuous fun t => Wt t ζ i j :=
    Eventually.of_forall fun ζ i j => (continuous_apply (i, j)).comp (hF.brownian.cont ζ)
  have hBt : IsVectorBrownian P Wt := s102_vecBrownian_of_ae hreal.brownian hae hcont
  have hX0m : Measurable (X 0) := (hreal.solution T).adapted 0
  have hX0ae : X 0 =ᵐ[P] X₀ := (hreal.solution T).init
  have hlaw0 : P.map (X 0) = Q.withDensity φ0 := by
    rw [Measure.map_congr hX0ae, hlaw, hQγ]
  have hWm : ∀ t, Measurable (Wt t) := s102_Wt_measurable W' hF.brownian.adapted
  have hWp : Measurable (fun ζ t => Wt t ζ) := measurable_pi_iff.2 hWm
  have hind : IndepFun (X 0) (fun ζ t => Wt t ζ) P := by
    refine hreal.indep.congr hX0ae.symm ?_
    filter_upwards [hae] with ζ h
    funext t
    exact (h t).symm
  have hsolW := s102_strong_ae (hreal.solution T) hae
  have hsol : IsWholeStrongSolution P (quadraticGradientDyn d s a β) T (X 0) Wt X :=
    ⟨Eventually.of_forall fun _ => rfl, hsolW.eqn, hsolW.cont, hsolW.adapted, hsolW.no_collision⟩
  have hac : s102_rew P (X 0) φ0 ≪ P := withDensity_absolutelyContinuous _ _
  haveI hP'prob := s102_rew_prob P (X 0) hX0m Q φ0 hφm hφpos hφfin hlaw0
  have hmap := s102_rew_map P (X 0) hX0m Q φ0 hφm hφpos hφfin hlaw0
  obtain ⟨-, hind'⟩ := s102_rew_indep P (X 0) hX0m Q φ0 hφm hφpos hφfin hlaw0 (fun ζ t => Wt t ζ) hWp hind
  have hB' := s102_vecBrownian_rew P (X 0) hX0m Q φ0 hφm hφpos hφfin hlaw0 Wt hWm hind hBt
  have hsol' := s102_strong_rew hsol hac
  have hlawcan : HRS.law (s102_rew P (X 0) φ0) (X 0) = HRS.Whole.canonicalGibbs (rieszKernel d s) (HRS.Whole.confinement a) N β := by
    rw [hcan]; exact hmap
  have hXt := hinv (s102_rew P (X 0) φ0) T (X 0) Wt X hB' hind' hlawcan hsol' t ht
  rw [hcan] at hXt
  obtain ⟨κ, hκ, hQκ, hlawκ⟩ := s102_transfer_density P (s102_rew P (X 0) φ0) (X 0) (X t) hX0m
    ((hreal.solution T).adapted t) Q φ0 hφm (s102_rew_inv P (X 0) hX0m φ0 hφm hφpos hφfin) hmap hXt
  rw [hlawκ, ← hQγ]
  exact hdens κ hκ hQκ


end HRS.MS.R2Interp

end
