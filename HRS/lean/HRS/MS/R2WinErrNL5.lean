import HRS.MS.R2WinErrNL4

/-!
# S10.4, nonlinear branch, part 5: `hobs` and `hdyn` along a nonlinear trajectory

`s104n_hobs` (measurability in the terminal time of the orbit slot) and `s104n_hdyn` (`S104RealInput` for every realization), both from the
terminal-time regularity input `S104nOrbit` (see `R2WinErrNL2`), the class bounds (density, boundedness) and `s104n_hjm`.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinErr

open HRS HRS.Whole HRS.MS.S53 HRS.MP.RdRem

variable {d : ℕ}

theorem s104n_hobs {C : WholeCoeff d} {φ : Euc d → ℝ} {T0 : ℝ} (horb : S104nOrbit C φ T0) {b T r : ℝ}
    (hT : 0 ≤ T) (hb : 0 ≤ b) (hbT : b + T ≤ T0) (hr : 0 ≤ r) (a' : Fin d) (x : Euc d) :
    AEStronglyMeasurable (fun u : ℝ => if r < b + u then gradComp a' (propagatorW C r (b + u)
      (generatorW C (b + u) φ)) x else 0) (volume.restrict (Icc (0 : ℝ) T)) := by
  by_cases hrT : r ≤ b + T
  swap
  · have : (fun u : ℝ => if r < b + u then gradComp a' (propagatorW C r (b + u)
        (generatorW C (b + u) φ)) x else 0) =ᵐ[volume.restrict (Icc (0 : ℝ) T)] fun _ => 0 := by
      refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun u hu => ?_)
      simp only [if_neg (not_lt.2 (by linarith [hu.2] : b + u ≤ r))]
    exact aestronglyMeasurable_const.congr this.symm
  have hrT0 : r ∈ Icc (0 : ℝ) T0 := ⟨hr, hrT.trans hbT⟩
  obtain ⟨G2, hG2, hd12⟩ := horb.diff12 r hrT0
  have hT0r : 0 ≤ T0 - r := by linarith [hrT0.2]
  have hcont : S53Cont (T0 - r) (fun τ => propagatorW C r (r + τ) (generatorW C (r + τ) φ)) :=
    s53_cont_of_diff (fun τ hτ => horb.cb1 hrT0 hτ) hG2 hd12
  have hjc := s53_grad_continuous hT0r (fun τ hτ => horb.cb1 hrT0 hτ) hcont
  set h : ℝ → ℝ := fun u => if r < b + u then
    gradient ((fun τ => propagatorW C r (r + τ) (generatorW C (r + τ) φ)) (s53_clamp (T0 - r) (b + u - r))) x a'
    else 0 with hh
  have hmeas : AEStronglyMeasurable h (volume.restrict (Icc (0 : ℝ) T)) := by
    have hcf : Continuous fun u : ℝ => gradient ((fun τ => propagatorW C r (r + τ) (generatorW C (r + τ) φ))
        (s53_clamp (T0 - r) (b + u - r))) x a' := by
      have h1 : Continuous fun u : ℝ => gradient ((fun τ => propagatorW C r (r + τ)
          (generatorW C (r + τ) φ)) (s53_clamp (T0 - r) (b + u - r))) x :=
        hjc.comp (Continuous.prodMk (by fun_prop) continuous_const)
      exact (EuclideanSpace.proj a' : Euc d →L[ℝ] ℝ).continuous.comp h1
    have : h = (Ioi (-(b - r))).indicator (fun u => gradient ((fun τ => propagatorW C r (r + τ)
        (generatorW C (r + τ) φ)) (s53_clamp (T0 - r) (b + u - r))) x a') := by
      funext u
      simp only [hh, Set.indicator_apply, Set.mem_Ioi]
      split_ifs with h1 h2 h2
      · rfl
      · exfalso; linarith
      · exfalso; linarith
      · rfl
    rw [this]
    exact (hcf.aestronglyMeasurable.indicator measurableSet_Ioi)
  refine hmeas.congr ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun u hu => ?_)
  by_cases hru : r < b + u
  · simp only [hh, if_pos hru]
    have hτ : b + u - r ∈ Icc (0 : ℝ) (T0 - r) := ⟨by linarith, by linarith [hu.2]⟩
    rw [s53_clamp_of_mem hτ]
    show gradient (propagatorW C r (r + (b + u - r)) (generatorW C (r + (b + u - r)) φ)) x a' =
      gradComp a' (propagatorW C r (b + u) (generatorW C (b + u) φ)) x
    rw [add_sub_cancel]
    rfl
  · simp only [hh, if_neg hru]

theorem s104n_hdyn {s a β T : ℝ} {ρ : ℝ → Euc d → ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hreal : IsR2Realization d s a β P X₀ W X) {b : ℝ} (hb : 0 ≤ b) (hT : 0 ≤ T) (C₀ : ℝ)
    (hρm : Measurable fun p : ℝ × Euc d => ρ (mrrClamp (b + T) p.1) p.2)
    (hden : ∀ t : ℝ, 0 ≤ t → HRS.Whole.IsProbDensity (ρ t) ∧ ∃ M : ℝ, ∀ x, ρ t x ≤ M)
    (horb : ∀ α : MultiIndex d, S104nOrbit ((quadraticGradientDyn d s a β).coeff ρ)
      (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) (b + T)) :
    S104RealInput d s a β T ρ N P X b C₀ := by
  obtain ⟨ℱ, W', hfilt⟩ := hreal.filtered
  have hprog := hfilt.progressive
  have hT0 : 0 ≤ b + T := by linarith
  have hNpos : 0 < N := by omega
  have hctx : ∀ r : ℝ, 0 ≤ r → ∃ Mρ, S53Ctx s (ρ r) Mρ := by
    intro r hr
    obtain ⟨hp, M, hM⟩ := hden r hr
    obtain ⟨Mρ, hM0, hrow⟩ := s53_rowConst (by omega : 1 ≤ d) hs0 hsd hp hM
    exact ⟨Mρ, ⟨hs0, hM0, hp, hrow⟩⟩
  have hρp : ∀ t : ℝ, 0 ≤ t → HRS.Whole.IsProbDensity (ρ t) := fun t ht => (hden t ht).1
  refine ⟨fun ζ α r t0 t hr0 hrt0 ht0t htT => ?_, fun α => ?_, fun α => ?_, fun α => ?_⟩
  · exact s104n_hevol hNpos (horb α) hctx X ζ hr0 hrt0 ht0t htT
  · exact s104n_M0 P ℱ X hprog (horb α) hρm hρp hb (by linarith)
  · exact s104n_M1 P ℱ X hprog (horb α) hρm hρp hb (by linarith)
  · exact s104n_M2 P ℱ X hprog (horb α) hρm hρp hb (by linarith)

end HRS.MS.R2WinErr
