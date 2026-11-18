import HRS.MS.S111X2Aux45
import HRS.MS.S111X2Aux20

/-!
# S11.1 X2, packet H02: the finite-projection covariance comparison (`S11X2H02`)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S111X2

open HRS HRS.Whole HRS.MS.R2Interp
open HRS.Whole.Q34

variable {d : ℕ}

theorem s111x2_lgcov_symm {C : WholeCoeff d} (q : ℝ) (C₀ : (Euc d → ℝ) → (Euc d → ℝ) → ℝ) (t t' : ℝ)
    (φ ψ : Euc d → ℝ) (hC : C₀ (propagatorW C 0 t φ) (propagatorW C 0 t' ψ) =
      C₀ (propagatorW C 0 t' ψ) (propagatorW C 0 t φ)) :
    linearGaussianCov C q C₀ t t' φ ψ = linearGaussianCov C q C₀ t' t ψ φ := by
  unfold linearGaussianCov
  rw [hC, s111x2_noise_symm]

/-- **H02** for a fixed thermal reference. -/
theorem s111x2_H02_fixed (hd : 2 ≤ d) (s a β γ T lam : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a)
    (hβ : 0 < β) (hγ : 0 ≤ γ) (hT : 0 < T) (hlam : 0 < lam) {ρ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d s a β ρ) (hP : IsR2Poincare (HRS.Whole.withDensityReal ρ) lam) :
    ∃ B : ℝ, 0 ≤ B ∧
    ∀ {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] (P₁ : Measure Ω₁) (P₂ : Measure Ω₂)
      [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
      (Z₁ : ℝ → Ω₁ → OscDual d (wholeSpaceIndex d : ℝ)) (Z₂ : ℝ → Ω₂ → OscDual d (wholeSpaceIndex d : ℝ)),
      (∀ T' : ℝ, IsLinearGaussianEvolutionW P₁ (s111x2_CC d s a β ρ) (wholeSpaceIndex d : ℝ) β⁻¹ T'
        (s111x2_C0 d s ρ γ) Z₁) →
      (∀ T' : ℝ, IsLinearGaussianEvolutionW P₂ (s111x2_CC d s a β ρ) (wholeSpaceIndex d : ℝ) β⁻¹ T'
        (s111x2_C0 d s ρ β) Z₂) →
      ∀ u : ℝ, 0 ≤ u → ∀ n : ℕ, ∀ M : (R2X d T) [×2]→L[ℝ] ℝ, ‖M‖ ≤ 1 →
        |∫ ζ, M ![s102_Pj (d := d) (m := (wholeSpaceIndex d : ℝ)) T hT n
            (processWindow (wholeSpaceIndex d : ℝ) T u Z₁ ζ),
            s102_Pj (d := d) (m := (wholeSpaceIndex d : ℝ)) T hT n
            (processWindow (wholeSpaceIndex d : ℝ) T u Z₁ ζ)] ∂P₁ -
          ∫ ζ, M ![s102_Pj (d := d) (m := (wholeSpaceIndex d : ℝ)) T hT n
            (processWindow (wholeSpaceIndex d : ℝ) T 0 Z₂ ζ),
            s102_Pj (d := d) (m := (wholeSpaceIndex d : ℝ)) T hT n
            (processWindow (wholeSpaceIndex d : ℝ) T 0 Z₂ ζ)] ∂P₂| ≤
          B * Real.exp (-2 * (lam / β) * u) := by
  classical
  obtain ⟨B₀, hB0, hmemU, hsums⟩ := s111x2_H01 hd s a β lam hs0 hs ha hβ hlam hρ hP
  obtain ⟨M₁, T₁⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  haveI := isProbabilityMeasure_nu T₁.prob
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  obtain ⟨M₀, c, S, hc, hTc⟩ := HRS.MS.TransOp.s611_tcref_of_thermal hd hs0 hsd ha hβ hρ
  obtain ⟨Mg, K, hK⟩ := s111x2_krep_of_tcref (by omega) hs0 hsd hc hTc
  refine ⟨4 * B₀ * (1 + T ^ 2), by positivity, fun {Ω₁ Ω₂} _ _ P₁ P₂ _ _ Z₁ Z₂ hZ₁ hZ₂ u hu n M hM => ?_⟩
  set κ : ℝ := lam / β with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set U : ℝ → MultiIndex d → Euc d → ℝ := fun τ α =>
    propagatorW (s111x2_CC d s a β ρ) 0 τ (oscTestFun (wholeSpaceIndex d : ℝ) α) with hU
  have hUm : ∀ τ, 0 ≤ τ → ∀ α, MemLp (U τ α) 2 (HRS.Whole.withDensityReal ρ) := fun τ hτ α => hmemU α τ hτ
  have h1 : ∀ (S : Finset (MultiIndex d)) (τ₁ : ℝ), 0 ≤ τ₁ →
      ∑ α ∈ S, s111x2_centeredSquare (HRS.Whole.withDensityReal ρ) (U τ₁ α) ≤ B₀ * Real.exp (-2 * κ * τ₁) :=
    fun S τ₁ hτ => (hsums S τ₁ τ₁ hτ le_rfl).1
  have h2 : ∀ (S : Finset (MultiIndex d)) (τ₁ τ₂ : ℝ), 0 ≤ τ₁ → τ₁ ≤ τ₂ →
      ∑ α ∈ S, s111x2_centeredSquare (HRS.Whole.withDensityReal ρ) (fun x => U τ₂ α x - U τ₁ α x) ≤
        B₀ * (τ₂ - τ₁) ^ 2 * Real.exp (-2 * κ * τ₁) :=
    fun S τ₁ τ₂ hτ h12 => (hsums S τ₁ τ₂ hτ h12).2
  -- the two expectations
  have E1 := s111x2_window_exp hd hs0 hs ha hβ hρ hγ hT n P₁ Z₁ hu (hZ₁ (u + T)) M
  have E2 := s111x2_window_exp hd hs0 hs ha hβ hρ hβ.le hT n P₂ Z₂ le_rfl (by simpa using hZ₂ (0 + T)) M
  rw [E1, E2, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  -- entrywise identification with the response Gram matrices
  have hRFβ := s111x2_responseForm hK hβ.le (le_refl β)
  have hRFγ := s111x2_responseForm hK hγ (le_refl γ)
  set Kθ : ℝ → ℕ × MultiIndex d → ℕ × MultiIndex d → ℝ := fun θ p q =>
    HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) θ
      (U (u + ((s102_node hT n p.1 : Set.Icc (0 : ℝ) T) : ℝ)) p.2)
      (U (u + ((s102_node hT n q.1 : Set.Icc (0 : ℝ) T) : ℝ)) q.2) with hKθ
  have hnn : ∀ i, 0 ≤ ((s102_node hT n i : Set.Icc (0 : ℝ) T) : ℝ) := fun i => (s102_node hT n i).2.1
  have hentry : ∀ p q : ℕ × MultiIndex d,
      linearGaussianCov (s111x2_CC d s a β ρ) β⁻¹ (s111x2_C0 d s ρ γ)
        (u + ((s102_node hT n p.1 : Set.Icc (0 : ℝ) T) : ℝ)) (u + ((s102_node hT n q.1 : Set.Icc (0 : ℝ) T) : ℝ))
        (oscTestFun (wholeSpaceIndex d : ℝ) p.2) (oscTestFun (wholeSpaceIndex d : ℝ) q.2) -
      linearGaussianCov (s111x2_CC d s a β ρ) β⁻¹ (s111x2_C0 d s ρ β)
        (0 + ((s102_node hT n p.1 : Set.Icc (0 : ℝ) T) : ℝ)) (0 + ((s102_node hT n q.1 : Set.Icc (0 : ℝ) T) : ℝ))
        (oscTestFun (wholeSpaceIndex d : ℝ) p.2) (oscTestFun (wholeSpaceIndex d : ℝ) q.2) =
      Kθ γ p q - Kθ β p q := by
    intro p q
    simp only [zero_add]
    have hsy : ∀ θ, 0 ≤ θ → ∀ p q : ℕ × MultiIndex d, Kθ θ p q = Kθ θ q p := by
      intro θ hθ p q
      have hRF := s111x2_responseForm hK hθ (le_refl θ)
      exact hRF.symmetry _ _ (hUm _ (by linarith [hnn p.1, hu]) _) (hUm _ (by linarith [hnn q.1, hu]) _)
    have key : ∀ p q : ℕ × MultiIndex d,
        ((s102_node hT n p.1 : Set.Icc (0 : ℝ) T) : ℝ) ≤ ((s102_node hT n q.1 : Set.Icc (0 : ℝ) T) : ℝ) →
        linearGaussianCov (s111x2_CC d s a β ρ) β⁻¹ (s111x2_C0 d s ρ γ)
          (u + ((s102_node hT n p.1 : Set.Icc (0 : ℝ) T) : ℝ)) (u + ((s102_node hT n q.1 : Set.Icc (0 : ℝ) T) : ℝ))
          (oscTestFun (wholeSpaceIndex d : ℝ) p.2) (oscTestFun (wholeSpaceIndex d : ℝ) q.2) -
        linearGaussianCov (s111x2_CC d s a β ρ) β⁻¹ (s111x2_C0 d s ρ β)
          ((s102_node hT n p.1 : Set.Icc (0 : ℝ) T) : ℝ) ((s102_node hT n q.1 : Set.Icc (0 : ℝ) T) : ℝ)
          (oscTestFun (wholeSpaceIndex d : ℝ) p.2) (oscTestFun (wholeSpaceIndex d : ℝ) q.2) =
        Kθ γ p q - Kθ β p q := by
      intro p q hpq
      obtain ⟨⟨f, hf⟩, -⟩ := s111x2_exist_osc hd hs0 hs ha hβ hρ p.2
        (H := u + ((s102_node hT n p.1 : Set.Icc (0 : ℝ) T) : ℝ)) (by linarith [hnn p.1])
      obtain ⟨⟨g, hg⟩, -⟩ := s111x2_exist_osc hd hs0 hs ha hβ hρ q.2
        (H := u + ((s102_node hT n q.1 : Set.Icc (0 : ℝ) T) : ℝ)) (by linarith [hnn q.1])
      exact s111x2_pair_diff_eq hd hs0 hs ha hβ hρ hu (hnn p.1) hpq hf hg
    rcases le_total ((s102_node hT n p.1 : Set.Icc (0 : ℝ) T) : ℝ) ((s102_node hT n q.1 : Set.Icc (0 : ℝ) T) : ℝ)
      with hpq | hqp
    · exact key p q hpq
    · have := key q p hqp
      rw [s111x2_lgcov_symm (C := s111x2_CC d s a β ρ) β⁻¹ (s111x2_C0 d s ρ γ) _ _
          (oscTestFun (wholeSpaceIndex d : ℝ) q.2) (oscTestFun (wholeSpaceIndex d : ℝ) p.2)
          (hRFγ.symmetry _ _ (hmemU _ _ (by linarith [hnn q.1, hu])) (hmemU _ _ (by linarith [hnn p.1, hu]))),
        s111x2_lgcov_symm (C := s111x2_CC d s a β ρ) β⁻¹ (s111x2_C0 d s ρ β) _ _
          (oscTestFun (wholeSpaceIndex d : ℝ) q.2) (oscTestFun (wholeSpaceIndex d : ℝ) p.2)
          (hRFβ.symmetry _ _ (hmemU _ _ (hnn q.1)) (hmemU _ _ (hnn p.1)))] at this
      rw [this, hsy γ hγ p q, hsy β hβ.le p q]
  have hsum : ∑ x ∈ s102_idx d n, ∑ x_1 ∈ s102_idx d n,
      (linearGaussianCov (s111x2_CC d s a β ρ) β⁻¹ (s111x2_C0 d s ρ γ) (u + ↑(s102_node hT n x.1))
          (u + ↑(s102_node hT n x_1.1)) (oscTestFun (wholeSpaceIndex d : ℝ) x.2)
          (oscTestFun (wholeSpaceIndex d : ℝ) x_1.2) *
        M ![s102_bpath T n x, s102_bpath T n x_1] -
      linearGaussianCov (s111x2_CC d s a β ρ) β⁻¹ (s111x2_C0 d s ρ β) (0 + ↑(s102_node hT n x.1))
          (0 + ↑(s102_node hT n x_1.1)) (oscTestFun (wholeSpaceIndex d : ℝ) x.2)
          (oscTestFun (wholeSpaceIndex d : ℝ) x_1.2) *
        M ![s102_bpath T n x, s102_bpath T n x_1]) =
      (∑ p ∈ s102_idx d n, ∑ q ∈ s102_idx d n, Kθ γ p q * M ![s102_bpath T n p, s102_bpath T n q]) -
      ∑ p ∈ s102_idx d n, ∑ q ∈ s102_idx d n, Kθ β p q * M ![s102_bpath T n p, s102_bpath T n q] := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← sub_mul, hentry p q, sub_mul]
  rw [hsum]
  have bγ := s111x2_gram_bound hK hγ (le_refl γ) hT n U hUm hu hB0 h1 h2 hκ0 M hM
  have bβ := s111x2_gram_bound hK hβ.le (le_refl β) hT n U hUm hu hB0 h1 h2 hκ0 M hM
  refine (abs_sub _ _).trans ?_
  have := add_le_add bγ bβ
  refine this.trans (le_of_eq ?_)
  ring

end HRS.MS.S111X2
