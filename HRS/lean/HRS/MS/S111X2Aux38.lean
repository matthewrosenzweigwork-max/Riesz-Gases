import HRS.MS.S111X2Aux37

/-!
# S11.1 X2, packet H01: summed `H¹`-type bounds for the Hermite observations (final statement)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X2

open HRS (Euc)
open HRS.Whole HRS.Whole.Q34

variable {d : ℕ}

/-- **H01.** -/
theorem s111x2_H01 (hd : 2 ≤ d) (s a β lam : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a) (hβ : 0 < β)
    (hlam : 0 < lam) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ)
    (hP : IsR2Poincare (HRS.Whole.withDensityReal ρ) lam) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ (α : MultiIndex d) (τ : ℝ), 0 ≤ τ → MemLp (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 τ
        (oscTestFun (wholeSpaceIndex d : ℝ) α)) 2 (HRS.Whole.withDensityReal ρ)) ∧
      ∀ (S : Finset (MultiIndex d)) (τ₁ τ₂ : ℝ), 0 ≤ τ₁ → τ₁ ≤ τ₂ →
        (∑ α ∈ S, s111x2_centeredSquare (HRS.Whole.withDensityReal ρ)
          (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 τ₁
            (oscTestFun (wholeSpaceIndex d : ℝ) α)) ≤ B * Real.exp (-2 * (lam / β) * τ₁)) ∧
        (∑ α ∈ S, s111x2_centeredSquare (HRS.Whole.withDensityReal ρ)
          (fun x => propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 τ₂
              (oscTestFun (wholeSpaceIndex d : ℝ) α) x -
            propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 τ₁
              (oscTestFun (wholeSpaceIndex d : ℝ) α) x) ≤
          B * (τ₂ - τ₁) ^ 2 * Real.exp (-2 * (lam / β) * τ₁)) := by
  obtain ⟨η₁, hη₁0, hη₁1, hall⟩ := s111x2_sharp_decay hd s a β lam β hs0 hs ha hβ hlam le_rfl
  obtain ⟨η₂, hη₂0, hη₂1, hinc⟩ := s111x2_orbit_incr hd s a β lam hs0 hs ha hβ hlam
  obtain ⟨-, hdec⟩ := hall ρ hρ
  obtain ⟨M, T⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  haveI := isProbabilityMeasure_nu T.prob
  obtain ⟨Λ, hΛ0, hΛ⟩ := s111x2_init_sum (by omega) T
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set C := (quadraticGradientDyn d s a β).coeff (fun _ => ρ) with hC
  set φ : MultiIndex d → Euc d → ℝ := fun α => oscTestFun (wholeSpaceIndex d : ℝ) α with hφdef
  have hmem2 : ∀ α, MemCb 2 (φ α) := fun α =>
    (S45.s45_cb_oscTest (d := d) (by omega) 2 (wholeSpaceIndex d : ℝ)).choose_spec.2 α |>.1
  set κ : ℝ := lam / β with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hi1 : 0 ≤ η₁⁻¹ := by positivity
  have hi2 : 0 ≤ η₂⁻¹ * η₂⁻¹ * Real.exp (2 * κ) := by positivity
  -- membership in `L²`
  have hmemU : ∀ (α : MultiIndex d) (τ : ℝ), 0 ≤ τ → MemLp (propagatorW C 0 τ (φ α)) 2 μ := by
    intro α τ hτ
    obtain ⟨⟨f, hf⟩, -⟩ := s111x2_exist_osc hd hs0 hs ha hβ hρ α (H := τ + 1) (by linarith)
    have hτI : τ ∈ Icc (0 : ℝ) (τ + 1) := ⟨hτ, by linarith⟩
    rw [s111x2_prop_orbit hd hs0 hs ha hβ hρ hf hτI]
    obtain ⟨B0, B1, B2, hB0, -, -, hB⟩ := HRS.MS.S111X1.classical_bounds hf
    have hI : τ + 1 - τ ∈ Icc (0 : ℝ) (τ + 1) := ⟨by linarith, by linarith⟩
    exact (MemLp.of_bound (hf.c2 _ hI).continuous.aestronglyMeasurable B0
      (Filter.Eventually.of_forall fun x => (hB _ hI x).1)).mono_exponent le_top
  refine ⟨(η₁⁻¹ + η₂⁻¹ * η₂⁻¹ * Real.exp (2 * κ)) * Λ, by positivity, hmemU, fun S τ₁ τ₂ h1 h12 => ?_⟩
  have hsumφ : ∑ α ∈ S, s111x2_centeredSquare μ (φ α) ≤ Λ := by
    refine le_trans (Finset.sum_le_sum fun α _ => ?_) (hΛ S)
    have := s111x2_cs_nonneg μ (generatorW C 0 (φ α))
    linarith
  have hexpn : 0 ≤ Real.exp (-2 * κ * τ₁) := (Real.exp_pos _).le
  refine ⟨?_, ?_⟩
  · -- initial slice
    calc ∑ α ∈ S, s111x2_centeredSquare μ (propagatorW C 0 τ₁ (φ α))
        ≤ ∑ α ∈ S, η₁⁻¹ * Real.exp (-2 * κ * τ₁) * s111x2_centeredSquare μ (φ α) := by
          refine Finset.sum_le_sum fun α _ => ?_
          obtain ⟨⟨f, hf⟩, -⟩ := s111x2_exist_osc hd hs0 hs ha hβ hρ α (H := τ₁ + 1) (by linarith)
          have hτI : τ₁ ∈ Icc (0 : ℝ) (τ₁ + 1) := ⟨h1, by linarith⟩
          rw [s111x2_prop_orbit hd hs0 hs ha hβ hρ hf hτI]
          exact hdec hP (τ₁ + 1) (by linarith) (φ α) f hf τ₁ hτI
      _ = η₁⁻¹ * Real.exp (-2 * κ * τ₁) * ∑ α ∈ S, s111x2_centeredSquare μ (φ α) := by rw [Finset.mul_sum]
      _ ≤ η₁⁻¹ * Real.exp (-2 * κ * τ₁) * Λ := by gcongr
      _ ≤ _ := by
          have : 0 ≤ η₂⁻¹ * η₂⁻¹ * Real.exp (2 * κ) * Λ * Real.exp (-2 * κ * τ₁) := by positivity
          nlinarith
  · -- increments
    calc ∑ α ∈ S, s111x2_centeredSquare μ (fun x => propagatorW C 0 τ₂ (φ α) x - propagatorW C 0 τ₁ (φ α) x)
        ≤ ∑ α ∈ S, (τ₂ - τ₁) ^ 2 * (η₂⁻¹ * η₂⁻¹ * Real.exp (2 * κ) * Real.exp (-2 * κ * τ₁) *
            (s111x2_centeredSquare μ (φ α) + s111x2_centeredSquare μ (generatorW C 0 (φ α)))) := by
          refine Finset.sum_le_sum fun α _ => ?_
          obtain ⟨⟨f, hf⟩, ⟨h, hh⟩⟩ := s111x2_exist_osc hd hs0 hs ha hβ hρ α (H := τ₂ + 1) (by linarith)
          have hτ1 : τ₁ ∈ Icc (0 : ℝ) (τ₂ + 1) := ⟨h1, by linarith⟩
          have hτ2 : τ₂ ∈ Icc (0 : ℝ) (τ₂ + 1) := ⟨by linarith, by linarith⟩
          have e1 : propagatorW C 0 τ₁ (φ α) = f (τ₂ + 1 - τ₁) :=
            s111x2_prop_orbit hd hs0 hs ha hβ hρ hf hτ1
          have e2 : propagatorW C 0 τ₂ (φ α) = f (τ₂ + 1 - τ₂) :=
            s111x2_prop_orbit hd hs0 hs ha hβ hρ hf hτ2
          have := hinc ρ hρ hP (τ₂ + 1) (by linarith) (φ α) (hmem2 α) f h hf hh τ₁ τ₂ h1 h12 (by linarith)
          simp only [e1, e2]
          exact this
      _ = (τ₂ - τ₁) ^ 2 * (η₂⁻¹ * η₂⁻¹ * Real.exp (2 * κ) * Real.exp (-2 * κ * τ₁)) *
            ∑ α ∈ S, (s111x2_centeredSquare μ (φ α) + s111x2_centeredSquare μ (generatorW C 0 (φ α))) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun α _ => by ring
      _ ≤ (τ₂ - τ₁) ^ 2 * (η₂⁻¹ * η₂⁻¹ * Real.exp (2 * κ) * Real.exp (-2 * κ * τ₁)) * Λ := by
          gcongr
          exact hΛ S
      _ ≤ _ := by
          have : 0 ≤ (τ₂ - τ₁) ^ 2 * (η₂⁻¹ * η₂⁻¹ * Real.exp (2 * κ) * Λ) * Real.exp (-2 * κ * τ₁) := by positivity
          have h2 : 0 ≤ (τ₂ - τ₁) ^ 2 * (η₁⁻¹ * Λ) * Real.exp (-2 * κ * τ₁) := by positivity
          nlinarith

end HRS.MS.S111X2
