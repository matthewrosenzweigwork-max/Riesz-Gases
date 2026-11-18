import HRS.MS.FinNoiseAux7

/-!
# S8.6 `finite_noise`, packet P-rec (S86): the reconstruction estimate in root-mean-square form

`s86_reconstruction_estimate`: for an `𝒦`-valued Hilbert martingale `D` with covariation `Σ` on `[0,H]` and
`E ∫_0^H Tr Σ ≤ A`, `(E sup_{t≤H} ‖𝒯 D^t‖²)^{1/2} ≤ C √A` with `C` depending on `H` only.  Statement adopted
from the Pro packet S8.6.06, checked: true (it is `u9_bound` with the Hilbert BDG constant).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.FinNoise

open HRS HRS.Whole HRS.MS.U9

theorem s86_reconstruction_estimate (d : ℕ) (m H : ℝ) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℝ mΩ) (D : ℝ → Ω → KSpace d m H)
        (Sg : ℝ → Ω → KSpace d m H →L[ℝ] KSpace d m H →L[ℝ] ℝ),
        IsHilbertMartingaleWithCovariation P ℱ H D Sg →
      ∀ A : ℝ, 0 ≤ A →
        (∫ z, (∫ r in Set.Icc (0 : ℝ) H, traceNormForm (Sg r z)) ∂P) ≤ A →
        (∫⁻ z, (⨆ t : Set.Icc (0 : ℝ) H,
          ENNReal.ofReal ‖reconstructPath m H D z t‖) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
            ENNReal.ofReal (C * Real.sqrt A) := by
  obtain ⟨C₂, hC₂, hbdg⟩ := HRS.HilbertBDG.hilbert_bdg 2 le_rfl
  refine ⟨Real.sqrt ((3 + Real.sqrt H) ^ 2 * C₂), Real.sqrt_nonneg _, ?_⟩
  intro Ω mΩ P hP ℱ D Sg hM A hA hJ
  have h1 := u9_bound hH hM C₂ hC₂ (hbdg Ω P ℱ (KSpace d m H) H D Sg hM)
  have hK : 0 ≤ (3 + Real.sqrt H) ^ 2 * C₂ := by positivity
  have h2 : (3 + Real.sqrt H) ^ 2 * C₂ *
      (∫ z, (∫ r in Set.Icc (0 : ℝ) H, traceNormForm (Sg r z)) ∂P) ≤
        (3 + Real.sqrt H) ^ 2 * C₂ * A := mul_le_mul_of_nonneg_left hJ hK
  calc (∫⁻ z, (⨆ t : Set.Icc (0 : ℝ) H, ENNReal.ofReal ‖reconstructPath m H D z t‖) ^ 2 ∂P) ^
        (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal ((3 + Real.sqrt H) ^ 2 * C₂ * A)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (h1.trans (ENNReal.ofReal_le_ofReal h2)) (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt ((3 + Real.sqrt H) ^ 2 * C₂ * A)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow]
    _ = ENNReal.ofReal (Real.sqrt ((3 + Real.sqrt H) ^ 2 * C₂) * Real.sqrt A) := by
        rw [Real.sqrt_mul hK]

end HRS.MS.FinNoise
