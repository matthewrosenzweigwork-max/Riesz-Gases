import HRS.MS.S111X2Aux23

/-!
# S11.1 X2, pair-level decay of the covariance difference (see `S111X2Aux23`)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X2

open HRS (Euc)
open HRS.Whole HRS.Whole.Q34

variable {d : ℕ}

theorem s111x2_sqrt_decay {c X Y η : ℝ} (hη : 0 < η) (hc : 0 ≤ c) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h : X ≤ η⁻¹ * Real.exp (-2 * c) * Y) :
    Real.sqrt X ≤ Real.sqrt η⁻¹ * Real.exp (-c) * Real.sqrt Y := by
  have h1 : Real.sqrt X ≤ Real.sqrt (η⁻¹ * Real.exp (-2 * c) * Y) := Real.sqrt_le_sqrt h
  refine h1.trans (le_of_eq ?_)
  have e : Real.exp (-2 * c) = Real.exp (-c) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), e, Real.sqrt_sq (Real.exp_pos _).le]

/-- **Pair-level decay of the window covariance difference.** -/
theorem s111x2_pair_diff (hd : 2 ≤ d) (s a β γ lam : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hβ : 0 < β) (hγ : 0 ≤ γ) (hlam : 0 < lam) :
    ∃ η : ℝ, 0 < η ∧ ∀ ρ : Euc d → ℝ, IsThermalEquilibrium d s a β ρ →
      IsR2Poincare (HRS.Whole.withDensityReal ρ) lam →
      ∀ u : ℝ, 0 ≤ u → ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → ∀ (φ ψ : Euc d → ℝ) (f g : ℝ → Euc d → ℝ),
        IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) (u + t₁) φ f →
        IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) (u + t₂) ψ g →
        |linearGaussianCov ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) β⁻¹
            (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ)
            (u + t₁) (u + t₂) φ ψ -
          linearGaussianCov ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) β⁻¹
            (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β)
            t₁ t₂ φ ψ| ≤
        2 * η⁻¹ * Real.exp (-2 * (lam / β) * u) *
          (Real.sqrt (s111x2_centeredSquare (HRS.Whole.withDensityReal ρ) φ) *
            Real.sqrt (s111x2_centeredSquare (HRS.Whole.withDensityReal ρ) ψ)) := by
  obtain ⟨η, hη0, hη1, hall⟩ := s111x2_sharp_decay hd s a β lam (max β γ) hs0 hs ha hβ hlam (le_max_left _ _)
  refine ⟨η, hη0, fun ρ hρ hP u hu t₁ t₂ ht₁ ht₁₂ φ ψ f g hf hg => ?_⟩
  obtain ⟨hRF, hdec⟩ := hall ρ hρ
  have hRFβ := hRF β ⟨hβ.le, le_max_left _ _⟩
  have hRFγ := hRF γ ⟨hγ, le_max_right _ _⟩
  obtain ⟨M, T⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  haveI := isProbabilityMeasure_nu T.prob
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set C := (quadraticGradientDyn d s a β).coeff (fun _ => ρ) with hC
  have ht₂ : 0 ≤ t₂ := ht₁.trans ht₁₂
  have hr1 : 0 ≤ u + t₁ := by linarith
  have hr2 : 0 ≤ u + t₂ := by linarith
  -- the two quench identities
  have Q1 := s111x2_quench_ge (γ := γ) hd hs0 hs ha hβ hρ hr1 (by linarith : u + t₁ ≤ u + t₂) hf hg
  have hf₀ := s111x2_cls_shift T hu ht₁ hf
  have hg₀ := s111x2_cls_shift T hu ht₂ hg
  have Q2 := s111x2_quench_ge (γ := β) hd hs0 hs ha hβ hρ ht₁ ht₁₂ hf₀ hg₀
  have hsh := s111x2_prop_shift hd hs0 hs ha hβ hρ hu ht₁ ht₁₂ hg
  rw [Q1, Q2, hsh]
  -- a and b
  set a₁ := propagatorW C 0 (u + t₁) φ with ha₁
  set b₁ := propagatorW C 0 (u + t₂) ψ with hb₁
  have hcl : ∀ {H : ℝ} {χ : Euc d → ℝ} {F : ℝ → Euc d → ℝ}, 0 ≤ H → IsClassicalAdjointW C H χ F →
      MemLp (propagatorW C 0 H χ) 2 μ ∧
      s111x2_centeredSquare μ (propagatorW C 0 H χ) ≤
        η⁻¹ * Real.exp (-2 * ((lam / β) * H)) * s111x2_centeredSquare μ χ := by
    intro H χ F hH hF
    obtain ⟨B0, B1, B2, hB0, -, -, hB⟩ := HRS.MS.S111X1.classical_bounds hF
    rw [s111x2_prop_eq hd hs0 hs ha hβ hρ hH hF ⟨le_rfl, hH⟩]
    refine ⟨MemLp.of_bound (hF.c2 0 ⟨le_rfl, hH⟩).continuous.aestronglyMeasurable B0
      (Filter.Eventually.of_forall fun x => (hB 0 ⟨le_rfl, hH⟩ x).1) |>.mono_exponent le_top, ?_⟩
    rcases hH.eq_or_lt with h0 | hpos
    · subst h0
      have : F 0 = χ := hF.terminal
      rw [this]
      simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
      have hcs : 0 ≤ s111x2_centeredSquare μ χ := integral_nonneg fun x => sq_nonneg _
      have : 1 ≤ η⁻¹ := (one_le_inv₀ hη0).2 hη1
      nlinarith
    · have := hdec hP H hpos χ F hF H ⟨hH, le_rfl⟩
      simpa [sub_self, mul_assoc, mul_comm, mul_left_comm] using this
  obtain ⟨m1, d1⟩ := hcl hr1 hf
  obtain ⟨m2, d2⟩ := hcl hr2 hg
  have hφL : 0 ≤ s111x2_centeredSquare μ φ := integral_nonneg fun x => sq_nonneg _
  have hψL : 0 ≤ s111x2_centeredSquare μ ψ := integral_nonneg fun x => sq_nonneg _
  have hc1 : 0 ≤ s111x2_centeredSquare μ a₁ := integral_nonneg fun x => sq_nonneg _
  have hc2 : 0 ≤ s111x2_centeredSquare μ b₁ := integral_nonneg fun x => sq_nonneg _
  have hκ : 0 ≤ lam / β := by positivity
  have s1 := s111x2_sqrt_decay (c := (lam / β) * (u + t₁)) hη0 (by positivity) hc1 hφL d1
  have s2 := s111x2_sqrt_decay (c := (lam / β) * (u + t₂)) hη0 (by positivity) hc2 hψL d2
  have bγ := s111x2_susc_le hRFγ m1 m2
  have bβ := s111x2_susc_le hRFβ m1 m2
  have hdiff : |HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) μ β φ
        (propagatorW C t₁ t₂ ψ) +
        HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) μ γ a₁ b₁ -
        HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) μ β a₁ b₁ -
      (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) μ β φ (propagatorW C t₁ t₂ ψ) +
        HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) μ β
          (propagatorW C 0 t₁ φ) (propagatorW C 0 t₂ ψ) -
        HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) μ β
          (propagatorW C 0 t₁ φ) (propagatorW C 0 t₂ ψ))| =
      |HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) μ γ a₁ b₁ -
        HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) μ β a₁ b₁| := by
    congr 1; ring
  rw [hdiff]
  refine (abs_sub _ _).trans ?_
  have hsq : Real.sqrt (s111x2_centeredSquare μ a₁) * Real.sqrt (s111x2_centeredSquare μ b₁) ≤
      (Real.sqrt η⁻¹ * Real.exp (-((lam / β) * (u + t₁))) * Real.sqrt (s111x2_centeredSquare μ φ)) *
      (Real.sqrt η⁻¹ * Real.exp (-((lam / β) * (u + t₂))) * Real.sqrt (s111x2_centeredSquare μ ψ)) :=
    mul_le_mul s1 s2 (Real.sqrt_nonneg _) (by positivity)
  have hexp : Real.exp (-((lam / β) * (u + t₁))) * Real.exp (-((lam / β) * (u + t₂))) ≤
      Real.exp (-2 * (lam / β) * u) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith [mul_nonneg hκ ht₁, mul_nonneg hκ ht₂]
  have hη2 : Real.sqrt η⁻¹ * Real.sqrt η⁻¹ = η⁻¹ := Real.mul_self_sqrt (by positivity)
  calc |HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) μ γ a₁ b₁| +
        |HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) μ β a₁ b₁|
      ≤ 2 * (Real.sqrt (s111x2_centeredSquare μ a₁) * Real.sqrt (s111x2_centeredSquare μ b₁)) := by
        linarith
    _ ≤ 2 * ((Real.sqrt η⁻¹ * Real.exp (-((lam / β) * (u + t₁))) * Real.sqrt (s111x2_centeredSquare μ φ)) *
      (Real.sqrt η⁻¹ * Real.exp (-((lam / β) * (u + t₂))) * Real.sqrt (s111x2_centeredSquare μ ψ))) := by
        gcongr
    _ = 2 * (Real.sqrt η⁻¹ * Real.sqrt η⁻¹) *
          (Real.exp (-((lam / β) * (u + t₁))) * Real.exp (-((lam / β) * (u + t₂)))) *
          (Real.sqrt (s111x2_centeredSquare μ φ) * Real.sqrt (s111x2_centeredSquare μ ψ)) := by ring
    _ = 2 * η⁻¹ * (Real.exp (-((lam / β) * (u + t₁))) * Real.exp (-((lam / β) * (u + t₂)))) *
          (Real.sqrt (s111x2_centeredSquare μ φ) * Real.sqrt (s111x2_centeredSquare μ ψ)) := by
        rw [hη2]
    _ ≤ 2 * η⁻¹ * Real.exp (-2 * (lam / β) * u) *
          (Real.sqrt (s111x2_centeredSquare μ φ) * Real.sqrt (s111x2_centeredSquare μ ψ)) := by
        gcongr

end HRS.MS.S111X2
