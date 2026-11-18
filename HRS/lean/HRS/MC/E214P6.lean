import HRS.MC.E214P2
import HRS.MC.E214P3
import HRS.MC.E214P5
import HRS.MC.E214H9
import HRS.MC.E213Q2

/-!
# E214P6 (H): proof of `HRS.Main.hybrid_correction` (Corollary 2.14, hybrid correction)

Route: `hK.expansion` at the window start `a N` gives `E Φ(ζ) = E Φ(Z^a) + (6√N)⁻¹ E K_{a}(D³Φ(Z^a)) + O(ε_N/√N)`;
`hrel` replaces `K_a` by `Kst` (`p5_cubic_diff`); the first-order Gaussian comparison (`p3_compare`, applied to the `C²`
function `Kst ∘ D³Φ`, `p4_*`) with the covariance estimate `covariance_relaxation_proof` replaces `Z^{a}` by the
stationary window.  `N₀` is chosen from `ε_N → 0` and `a N → ∞` before `Ω, P, X, W, Z, Φ`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E214P

open HRS HRS.Main

variable {d : ℕ}

/-- The remainder `(1/6)(C e^{-c a} + (1/2)‖Kst‖ C₃ e^{-c₃ a})` tends to `0` along `a N → ∞`. -/
theorem p6_tail_tendsto (a : ℕ → ℝ) (ha : Tendsto a atTop atTop) (C c C₃ c₃ M : ℝ) (hc : 0 < c)
    (hc₃ : 0 < c₃) :
    Tendsto (fun N => (1 / 6) * (C * Real.exp (-c * a N) + (1 / 2) * M * (C₃ * Real.exp (-c₃ * a N))))
      atTop (𝓝 0) := by
  have h1 : Tendsto (fun N => Real.exp (-c * a N)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (ha.const_mul_atTop_of_neg (by linarith))
  have h2 : Tendsto (fun N => Real.exp (-c₃ * a N)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (ha.const_mul_atTop_of_neg (by linarith))
  have := (((h1.const_mul C).add ((h2.const_mul C₃).const_mul ((1 / 2) * M))).const_mul (1 / 6))
  simpa using this

theorem hybrid_correction_proof (S : PreparedData d) (β₀ m T : ℝ) (hE : EdgeworthHyp S β₀ m)
    (hT : 0 < T) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (K : ℝ → projTensor (PathSpace d m T) 3) (ε : ℕ → ℝ)
    (hK : IsWindowEdgeworth S β₀ m T K ε) (Kst : projTensor (PathSpace d m T) 3) (C c : ℝ)
    (hC : 0 < C) (hc : 0 < c)
    (hrel : ∀ a : ℝ, 0 ≤ a → ‖K a - Kst‖ ≤ C * Real.exp (-c * a))
    (a : ℕ → ℝ) (ha0 : ∀ N, 0 ≤ a N) (ha : Tendsto a atTop atTop)
    (ν : Measure (NegSobolev d m)) (hν : IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0))
    {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
    (Zs : ℝ → Ω'' → NegSobolev d m) (hZs : IsStationaryGaussianField P'' S.s S.β S.hs0 S.hsd S.hβ S.V ρβ m Zs) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P S.dyn (a N + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        law P X₀ = modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0 →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a N + T) ν P' Z₀ Z →
      ∀ Φ : PathSpace d m T → ℝ, Φ ∈ CbUnitBall (PathSpace d m T) 5 →
        |∫ z, Φ z ∂(law P (windowZeta m T (a N) P X)) -
            ∫ z, Φ z ∂(law P' (windowPath m T (a N) Z)) -
          (1 / (6 * Real.sqrt N)) * ∫ ω, ((Kst : projTensor (PathSpace d m T) 3) :
            TensorDual (PathSpace d m T) 3)
              (iteratedFDeriv ℝ 3 Φ (windowPath m T 0 Zs ω)) ∂P''| ≤ η / Real.sqrt N := by
  intro η hη
  obtain ⟨C₃, c₃, hC₃, hc₃, hcov⟩ := HRS.MC.E214H.covariance_relaxation_proof S β₀ m T hE hT ρβ hρβ
  set Mb : ℝ := ‖Kst‖ with hMb
  have hMb0 : 0 ≤ Mb := norm_nonneg _
  -- choice of `N₀`
  have hev1 : ∀ᶠ N in atTop, ε N < η / 2 :=
    hK.eps_tendsto.eventually (gt_mem_nhds (by linarith))
  have hev2 : ∀ᶠ N in atTop,
      (1 / 6) * (C * Real.exp (-c * a N) + (1 / 2) * Mb * (C₃ * Real.exp (-c₃ * a N))) < η / 2 :=
    (p6_tail_tendsto a ha C c C₃ c₃ Mb hc hc₃).eventually (gt_mem_nhds (by linarith))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hev1.and (hev2.and (eventually_ge_atTop 2)))
  refine ⟨N₀, fun N hN Ω _ P _ X₀ W X hsel hfilt hinit Ω' _ P' _ Z₀ Z hZ Φ hΦ => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hN₀ N hN
  have hexp := hK.expansion (a N) (ha0 N) N h3 P X₀ W X hsel hfilt hinit ν hν P' Z₀ Z hZ Φ hΦ
  -- Gaussianity of the two windows
  obtain ⟨hZm, hZg⟩ := HRS.MC.E213Q.e213q_prepared_window_gaussian S m T (a N) hT (ha0 N) ν hν.1 P' Z₀ Z hZ
  obtain ⟨hZsm, hZsg⟩ := p2_stationary_window_gaussian S.hd S.hs0 S.hsd S.V S.hβ ρβ m T hT P'' Zs hZs
  -- notation
  set Ca : ℝ := ∫ ω, ((K (a N) : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)
    (iteratedFDeriv ℝ 3 Φ (windowPath m T (a N) Z ω)) ∂P' with hCa
  set Ca' : ℝ := ∫ ω, ((Kst : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)
    (iteratedFDeriv ℝ 3 Φ (windowPath m T (a N) Z ω)) ∂P' with hCa'
  set Cst : ℝ := ∫ ω, ((Kst : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)
    (iteratedFDeriv ℝ 3 Φ (windowPath m T 0 Zs ω)) ∂P'' with hCst
  -- (3) replace `K a` by `Kst`
  have hstep3 : |Ca - Ca'| ≤ C * Real.exp (-c * a N) := by
    refine (p5_cubic_diff hZm hΦ _ _).trans ?_
    have : ‖((K (a N) : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3) -
        ((Kst : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)‖ =
        ‖K (a N) - Kst‖ := by
      rfl
    rw [this]
    exact hrel _ (ha0 N)
  -- (4) replace `Z^a` by the stationary window inside `Kst ∘ D³Φ`
  have hstep4 : |Ca' - Cst| ≤ (1 / 2) * Mb * (C₃ * Real.exp (-c₃ * a N)) := by
    set L : TensorDual (PathSpace d m T) 3 := ((Kst : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)
      with hL
    have hLn : ‖L‖ = Mb := rfl
    obtain ⟨b0, b1, b2⟩ := p4_bound hΦ L
    have hcmp := p3_compare P'' (windowPath m T 0 Zs) P' (windowPath m T (a N) Z) hZsm hZm hZsg hZg
      (Θ := fun x => L (iteratedFDeriv ℝ 3 Φ x)) (p4_contDiff hΦ L) (M0 := ‖L‖) (M1 := ‖L‖) (K := ‖L‖)
      b0 b1 b2
    have hcd := hcov (a N) (ha0 N) ν hν P' Z₀ Z hZ P'' Zs hZs
    rw [hLn] at hcmp
    refine hcmp.trans ?_
    have := mul_le_mul_of_nonneg_left hcd hMb0
    linarith
  -- assembling
  set s : ℝ := Real.sqrt N with hs
  have hspos : 0 < s := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < N))
  set A : ℝ := ∫ z, Φ z ∂(law P (windowZeta m T (a N) P X)) with hA
  set Bq : ℝ := ∫ z, Φ z ∂(law P' (windowPath m T (a N) Z)) with hB
  have e : A - Bq - (1 / (6 * s)) * Cst =
      ((s * (A - Bq) - (1 / 6) * Ca) + (1 / 6) * ((Ca - Ca') + (Ca' - Cst))) / s := by
    field_simp
    ring
  rw [e, abs_div, abs_of_pos hspos]
  refine div_le_div_of_nonneg_right ?_ hspos.le
  calc |(s * (A - Bq) - (1 / 6) * Ca) + (1 / 6) * ((Ca - Ca') + (Ca' - Cst))|
      ≤ |s * (A - Bq) - (1 / 6) * Ca| + |(1 / 6) * ((Ca - Ca') + (Ca' - Cst))| := abs_add_le _ _
    _ ≤ ε N + (1 / 6) * (C * Real.exp (-c * a N) + (1 / 2) * Mb * (C₃ * Real.exp (-c₃ * a N))) := by
        refine add_le_add hexp ?_
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 6)]
        refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hstep3 hstep4)) (by norm_num)
    _ ≤ η := by linarith

end HRS.MC.E214P

end
