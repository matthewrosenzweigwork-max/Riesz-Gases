/-
# HRS.ME.FamX (packet X1): the lower conjunct of `critical_family_path_sup`

`critical_family_path_sup_lower` is the lower bound `c N^{-1/2} ≤ sup_θ W₂(path laws)` of the frozen
`HRS.Main.critical_family_path_sup`, for every family of stationary Gibbs flows and stationary Gaussian
fields (`P θ`, `P' θ`) on the window `[0,T]` whose evaluation at time `0` is given.

Mechanism.  `HRS.ME.FamW.critical_family_sharpness_lower` gives `c'`, `N₀` with
`c' N^{-1/2} ≤ ∫_{[0,R]} W₂(rateLaw, rateGaussian(ρθ)) dθ` for `N ≥ N₀`.  Pointwise on `[0,R]`, the
evaluation map `L = rateEval` (norm `‖L‖`) carries the window path laws to `rateLaw` and `rateGaussian`
(`rate_zeta_law`, `rate_gauss_law`), so `W₂(rateLaw, rateGaussian) ≤ ‖L‖ W₂(path laws) ≤ ‖L‖ S` with
`S` the supremum over `[0,R]`.  Integrating gives `c' N^{-1/2} ≤ ‖L‖ R S`; cancel `D = (‖L‖+1) R`.
-/
import HRS.ME.FamWE
import HRS.ME.FamVE
import HRS.ME.FamVC
import HRS.ME.FamVD

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.FamX

theorem critical_family_path_sup_lower {d : ℕ} (hd : 2 ≤ d) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d)
    (β : ℝ) (hβ : 0 < β) (k : Lattice d) (hk : k ≠ 0) (m : ℝ) (hm : 24 * (d : ℝ) + 240 ≤ m)
    (T : ℝ) (hT : 0 < T) (ρ : ℝ → Torus d → ℝ)
    (hρ : ∀ θ, IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) (rateV k β θ) β (ρ θ)) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (Ω : ℝ → Type) [∀ θ, MeasurableSpace (Ω θ)] (P : ∀ θ, Measure (Ω θ))
        [∀ θ, IsProbabilityMeasure (P θ)] (X₀ : ∀ θ, Ω θ → Config d N)
        (W : ∀ θ, ℝ≥0 → Ω θ → (Fin N → Euc d)) (X : ∀ θ, ℝ≥0 → Ω θ → Config d N),
      (∀ θ ∈ Set.Icc (0 : ℝ) (16 * (1 + β * rieszCoeff d ((d : ℝ) / 2) k)),
        SelectedFlow (P θ) (PDE.mfData d ((d : ℝ) / 2) hs0 hsd (rateV k β θ) β hβ) T
          (X₀ θ) (W θ) (X θ) ∧ law (P θ) (X₀ θ) = rateGibbs d ((d : ℝ) / 2) k β θ N) →
      (∀ θ ∈ Set.Icc (0 : ℝ) (16 * (1 + β * rieszCoeff d ((d : ℝ) / 2) k)),
        ∃ (ℱ : MeasureTheory.Filtration ℝ (inferInstance : MeasurableSpace (Ω θ)))
          (W' : ℝ≥0 → Ω θ → (Fin N × Fin d) → ℝ), IsFilteredSolution (P θ) ℱ W' (W θ) (X θ)) →
      ∀ (Ω' : ℝ → Type) [∀ θ, MeasurableSpace (Ω' θ)] (P' : ∀ θ, Measure (Ω' θ))
        [∀ θ, IsProbabilityMeasure (P' θ)] (Z : ∀ θ, ℝ → Ω' θ → NegSobolev d m),
      (∀ θ ∈ Set.Icc (0 : ℝ) (16 * (1 + β * rieszCoeff d ((d : ℝ) / 2) k)),
        IsStationaryGaussianField (P' θ) ((d : ℝ) / 2) β hs0 hsd hβ (rateV k β θ) (ρ θ) m (Z θ)) →
        ENNReal.ofReal (c * (N : ℝ) ^ (-(1 : ℝ) / 2)) ≤
          ⨆ θ ∈ Set.Icc (0 : ℝ) (16 * (1 + β * rieszCoeff d ((d : ℝ) / 2) k)),
            wassersteinE 2 (law (P θ) (Main.windowZeta m T 0 (P θ) (X θ)))
              (law (P' θ) (Main.windowPath m T 0 (Z θ))) := by
  obtain ⟨c', hc', N₀, hN₀⟩ := HRS.ME.FamW.critical_family_sharpness_lower hd hβ k hk
  have hg : 0 ≤ rieszCoeff d ((d : ℝ) / 2) k := (rieszCoeff_pos hd hs0 hsd k hk).le
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hm2 : (d : ℝ) < 2 * m := by linarith
  set R : ℝ := 16 * (1 + β * rieszCoeff d ((d : ℝ) / 2) k) with hR
  have hRpos : 0 < R := by
    have := mul_nonneg hβ.le hg
    rw [hR]
    linarith
  obtain ⟨L, hL⟩ : ∃ L, L = HRS.ME.FamV.rateEval d m T hT.le k := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (‖L‖ + 1) * R := ⟨_, rfl⟩
  have hDpos : 0 < D := by
    rw [hD]
    exact mul_pos (by linarith [norm_nonneg L]) hRpos
  have hDne : D ≠ 0 := hDpos.ne'
  refine ⟨c' / D, div_pos hc' hDpos, max N₀ 2, fun N hN => ?_⟩
  have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  intro Ω _ P _ X₀ W X hflow hfilt Ω' _ P' _ Z hZ
  have hlow := hN₀ ρ hρ N hN0
  have hpt : ∀ θ ∈ Set.Icc (0 : ℝ) R,
      wassersteinE 2 (Main.rateLaw d ((d : ℝ) / 2) k β N θ)
        (Main.rateGaussian d ((d : ℝ) / 2) k β (ρ θ)) ≤
        ENNReal.ofReal ‖L‖ * wassersteinE 2 (law (P θ) (Main.windowZeta m T 0 (P θ) (X θ)))
          (law (P' θ) (Main.windowPath m T 0 (Z θ))) := by
    intro θ hθ
    have hF := (hflow θ hθ).1
    have hI := (hflow θ hθ).2
    have hX : HRS.LZ.IsStationaryGibbsFlow (P θ) ((d : ℝ) / 2) hs0 hsd (rateV k β θ) β hβ (0 + T)
        (X₀ θ) (W θ) (X θ) := by
      rw [zero_add]
      exact ⟨hF, hfilt θ hθ, hI⟩
    have h1 := HRS.ME.FamV.rate_zeta_law hd hs0 hsd hβ k θ hN2 hm2 hT.le (P θ) hX
    have h2 := HRS.ME.FamV.rate_gauss_law hd hs0 hsd hβ k (rateV k β θ) (ρ θ)
      (HRS.ME.FamV.rateV_isSmooth k β θ) (hρ θ) hT.le (P' θ) (Z θ) (hZ θ hθ)
    rw [← hL] at h1 h2
    rw [← h1, ← h2]
    exact HRS.Main.wassersteinE_map_clm_le L 2 (by norm_num) _ _
  obtain ⟨S, hS⟩ : ∃ S : ENNReal, S = ⨆ θ ∈ Set.Icc (0 : ℝ) R,
      wassersteinE 2 (law (P θ) (Main.windowZeta m T 0 (P θ) (X θ)))
        (law (P' θ) (Main.windowPath m T 0 (Z θ))) := ⟨_, rfl⟩
  have hSle : ∀ θ ∈ Set.Icc (0 : ℝ) R,
      wassersteinE 2 (law (P θ) (Main.windowZeta m T 0 (P θ) (X θ)))
        (law (P' θ) (Main.windowPath m T 0 (Z θ))) ≤ S := by
    intro θ hθ
    rw [hS]
    exact le_iSup₂ (f := fun θ (_ : θ ∈ Set.Icc (0 : ℝ) R) =>
      wassersteinE 2 (law (P θ) (Main.windowZeta m T 0 (P θ) (X θ)))
        (law (P' θ) (Main.windowPath m T 0 (Z θ)))) θ hθ
  have hint : ∫⁻ θ in Set.Icc (0 : ℝ) R,
        wassersteinE 2 (Main.rateLaw d ((d : ℝ) / 2) k β N θ)
          (Main.rateGaussian d ((d : ℝ) / 2) k β (ρ θ)) ≤
      ∫⁻ θ in Set.Icc (0 : ℝ) R, ENNReal.ofReal ‖L‖ * S :=
    setLIntegral_mono' measurableSet_Icc
      (fun θ hθ => (hpt θ hθ).trans (mul_le_mul' le_rfl (hSle θ hθ)))
  have hcalc : ∫⁻ θ in Set.Icc (0 : ℝ) R, ENNReal.ofReal ‖L‖ * S
      = ENNReal.ofReal ‖L‖ * S * ENNReal.ofReal R := by
    rw [setLIntegral_const, Real.volume_Icc, sub_zero]
  have hLR : ENNReal.ofReal ‖L‖ * ENNReal.ofReal R ≤ ENNReal.ofReal D := by
    rw [← ENNReal.ofReal_mul (norm_nonneg _), hD]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [norm_nonneg L]
  have hkey : ENNReal.ofReal (c' * (N : ℝ) ^ (-(1 : ℝ) / 2)) ≤ S * ENNReal.ofReal D := by
    have h3 := hlow.trans (hint.trans hcalc.le)
    calc ENNReal.ofReal (c' * (N : ℝ) ^ (-(1 : ℝ) / 2))
        ≤ ENNReal.ofReal ‖L‖ * S * ENNReal.ofReal R := h3
      _ = S * (ENNReal.ofReal ‖L‖ * ENNReal.ofReal R) := by ring
      _ ≤ S * ENNReal.ofReal D := mul_le_mul' le_rfl hLR
  have hcnn : 0 ≤ c' / D * (N : ℝ) ^ (-(1 : ℝ) / 2) :=
    mul_nonneg (div_nonneg hc'.le hDpos.le) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hA : ENNReal.ofReal (c' / D * (N : ℝ) ^ (-(1 : ℝ) / 2)) * ENNReal.ofReal D
      = ENNReal.ofReal (c' * (N : ℝ) ^ (-(1 : ℝ) / 2)) := by
    rw [← ENNReal.ofReal_mul hcnn]
    congr 1
    field_simp
  have hA0 : ENNReal.ofReal D ≠ 0 := (ENNReal.ofReal_pos.2 hDpos).ne'
  have hAtop : ENNReal.ofReal D ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfin : ENNReal.ofReal (c' / D * (N : ℝ) ^ (-(1 : ℝ) / 2)) ≤ S := by
    refine (ENNReal.mul_le_mul_iff_left hA0 hAtop).1 ?_
    rw [hA]
    exact hkey
  rw [hS] at hfin
  exact hfin

end HRS.ME.FamX
