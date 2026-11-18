import HRS.MS.WsPrepI3

/-!
# S21T packet 4: the INIT statement `S21InitWin` and the Gibbs preparation (`β₀ > 0`) over the admissible class

`S21InitWin d s a β β₀ T εstar c₁ C₁ Cinit` is the INIT interface of `HANDOFF_S21R.md` section 3 item 3: for every admissible
perturbation, every resulting solution `ρ`, every `N ≥ 2` and every window start `bw ≥ 0`, there is a probability measure `γ₀` on
`C([0,T];B_m)` whose finite-dimensional laws are the Gaussians with covariance `C_{β₀}(U^{0,bw+t}φ_α, U^{0,bw+s}φ_{α'})`
(`susceptibilityCov` at `ρ⁰`, `β₀`) and such that the law of the particle initial path `K_bw` (`s21iK`, centred at `ρ⁰`) under the
preparation `ℚ_{N,β₀}(ρ⁰)` is within `C(√N δ_N + i_N)` (smooth) and `C(√N δ_N + j_N)` (`W_1`) of `γ₀`.

`s21i_init_gibbs`: `S21InitWin` for `β₀ > 0` from the S10.3 orbit input (`S21iOrb`, uniform over the class) and the tilt class
(`S21iTiltClass`, the ψ-uniform S4.7).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath
open HRS (Euc cbNorm MemCb smoothDist)

variable {d : ℕ}

/-- The INIT conclusion. -/
def S21InitWin (d : ℕ) (s a β β₀ T εstar c₁ C₁ Cinit : ℝ) : Prop :=
  ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ ε : ℝ, ∀ ψ : Euc d → ℝ,
    IsAdmissiblePerturbation ρβ εstar ε ψ → ∀ ρ : ℝ → Euc d → ℝ,
    IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ → ∀ N : ℕ, 2 ≤ N → ∀ bw : ℝ, 0 ≤ bw →
    ∃ γ0 : Measure (OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T), IsProbabilityMeasure γ0 ∧
      (∀ (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T) (αs : Fin p → MultiIndex d),
        (Matrix.of fun i j => HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal (ρ 0)) β₀
          (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) 0 (bw + ts i)
            (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs i)))
          (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) 0 (bw + ts j)
            (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs j)))).PosSemidef ∧
        γ0.map (fun w : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T => (WithLp.toLp 2 fun i =>
            OscDual.coord (OscPath.at' w ⟨ts i, hts i⟩) (αs i) : EuclideanSpace ℝ (Fin p))) =
          multivariateGaussian 0 (Matrix.of fun i j => HRS.Whole.susceptibilityCov (rieszKernel d s)
            (HRS.Whole.withDensityReal (ρ 0)) β₀
            (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) 0 (bw + ts i)
              (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs i)))
            (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) 0 (bw + ts j)
              (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs j))))) ∧
      smoothDist 2 ((HRS.Whole.modulatedGibbs (rieszKernel d s) N β₀ (HRS.Whole.withDensityReal (ρ 0))).map
          (s21iK ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T
            (HRS.Whole.withDensityReal (ρ 0)) bw)) γ0 ≤
        Cinit * (Real.sqrt N * HRS.deltaN d s N + iN d s β₀ N) ∧
      wassersteinE 1 ((HRS.Whole.modulatedGibbs (rieszKernel d s) N β₀ (HRS.Whole.withDensityReal (ρ 0))).map
          (s21iK ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T
            (HRS.Whole.withDensityReal (ρ 0)) bw)) γ0 ≤
        ENNReal.ofReal (Cinit * (Real.sqrt N * HRS.deltaN d s N + jN d s β₀ N))

/-- The S10.3 orbit input, uniform over the class. -/
def S21iOrbClass (d : ℕ) (s a β T εstar c₁ C₁ Corb : ℝ) : Prop :=
  ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ ε : ℝ, ∀ ψ : Euc d → ℝ,
    IsAdmissiblePerturbation ρβ εstar ε ψ → ∀ ρ : ℝ → Euc d → ℝ,
    IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ → S21iOrb d T ((quadraticGradientDyn d s a β).coeff ρ) Corb

/-- The reference facts for `ρ⁰ = ρ 0` along a resulting solution. -/
theorem s21i_ref_resulting (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {ρβ : Euc d → ℝ} (hρβ : IsThermalEquilibrium d s a β ρβ) {εstar ε : ℝ} {ψ : Euc d → ℝ} {c₁ C₁ : ℝ}
    {ρ : ℝ → Euc d → ℝ} (hres : IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ) :
    HRS.Whole.IsProbDensity (ρ 0) ∧ ∃ M L : ℝ, (∀ x, ρ 0 x ≤ M) ∧ (s = 0 → HasLogMoment2 (HRS.Whole.withDensityReal (ρ 0)) L) := by
  have hρ0 : HRS.Whole.IsProbDensity (ρ 0) := (hres.global 0).density 0 ⟨le_rfl, le_rfl⟩
  obtain ⟨-, hpos, -⟩ := HRS.MS.MovEnt.s66_rho0_facts hd hs0 hsd ha hβ hρβ
  have hC₁ : 0 < C₁ := s21p_C₁_pos hpos hres
  exact ⟨hρ0, s21i_ref hd hs0 hsd ha hβ hρβ hρ0 hC₁.le (fun x => (hres.ratio 0 le_rfl x).2)⟩

theorem s21i_init_gibbs (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β β₀ : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (hβ₀ : 0 < β₀) {T : ℝ} (hT : 0 < T) {εstar c₁ C₁ Corb : ℝ}
    (horb : S21iOrbClass d s a β T εstar c₁ C₁ Corb) (htilt : S21iTiltClass d s a β β₀ (4 * d + 42) εstar) :
    ∃ Cinit : ℝ, 0 ≤ Cinit ∧ S21InitWin d s a β β₀ T εstar c₁ C₁ Cinit := by
  obtain ⟨Cst, Cs, hCst, hCs, htl⟩ := htilt
  -- the orbit constant is nonnegative as soon as the class is nonempty; otherwise the statement is vacuous
  by_cases hne : ∃ (ρβ : Euc d → ℝ), IsThermalEquilibrium d s a β ρβ ∧ ∃ (ε : ℝ) (ψ : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
      IsAdmissiblePerturbation ρβ εstar ε ψ ∧ IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ
  swap
  · refine ⟨0, le_rfl, fun ρβ hρβ ε ψ hψ ρ hρ => absurd ⟨ρβ, hρβ, ε, ψ, ρ, hψ, hρ⟩ hne⟩
  obtain ⟨ρβ₁, hρβ₁, ε₁, ψ₁, ρ₁, hψ₁, hρ₁⟩ := hne
  have hCorb : 0 ≤ Corb := (horb ρβ₁ hρβ₁ ε₁ ψ₁ hψ₁ ρ₁ hρ₁).1
  obtain ⟨Cg, hCg, hG⟩ := s21i_gibbs hd hs0 hsd hβ₀ hT hCorb hCst hCs
  refine ⟨Cg, hCg, fun ρβ hρβ ε ψ hψ ρ hρ N hN bw hbw => ?_⟩
  obtain ⟨hρ0, M, L, hM, hL⟩ := s21i_ref_resulting hd hs0 hsd ha hβ hρβ hρ
  have hst := htl ρβ hρβ ε ψ hψ N hN
  rw [← hρ.init] at hst
  obtain ⟨γ0, hγ0, hfdd, hsm, hw1⟩ := hG _ (horb ρβ hρβ ε ψ hψ ρ hρ) (ρ 0) hρ0 M L hM hL N hN hst bw hbw
  refine ⟨γ0, hγ0, hfdd, ?_, ?_⟩
  · refine hsm.trans (le_of_eq ?_)
    simp [iN, hβ₀.ne']
  · refine hw1.trans (le_of_eq ?_)
    simp [jN, hβ₀.ne']

end HRS.MS.S21
