import HRS.Main.ThermLin2Ba1
import HRS.Main.ThermLin2Ba2
import HRS.Main.ThermLin2Ba6
import HRS.Main.ThermLin2Ly3

/-!
# THERMLIN2, packet As, part 1: helpers for the assembly `tl2_assembly`

* `tl2As_Wsystem`: for a `T25Ev` package `W`, the zero-start `W`-system `(P₂, Ĝ, Zb)` on a horizon `T'`
  (Gaussian martingale with covariation density `tl2CbDens`, measurable continuous stochastic convolution).
* `tl2As_swap_law`: the law of a process on `ν.prod Pg` is the law of the swapped process on `Pg.prod ν`.
* `tl2As_arith`: the final ENNReal bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P HRS.ThermLin

variable {d : ℕ}

/-- The zero-start `W`-system on the horizon `T'`. -/
theorem tl2As_Wsystem (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ) (hm : (d : ℝ) + 2 < m)
    {Cw cw Cmax T : ℝ} {Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
    (hEv : T25Ev m Cw cw T Cmax Wev) {T' : ℝ} (hT' : 0 < T') :
    ∃ (Ω₂ : Type) (_ : MeasurableSpace Ω₂) (P₂ : Measure Ω₂) (_ : IsProbabilityMeasure P₂)
      (ℱ₂ : Filtration ℝ ‹MeasurableSpace Ω₂›) (Ĝ Zb : ℝ → Ω₂ → NegSobolev d m),
      IsHilbertMartingaleWithCovariation P₂ ℱ₂ T' Ĝ (fun r _ => tl2CbDens S ρβ m T' r) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T',
        IsStochConv P₂ Wev (ContinuousLinearMap.id ℝ (NegSobolev d m)) Ĝ 0 t (Zb t)) ∧
      (∀ t, Measurable (Zb t)) ∧ (∀ᵐ ω ∂P₂, ContinuousOn (fun t => Zb t ω) (Set.Icc 0 T')) := by
  obtain ⟨hdet, hzero⟩ := tl2_CbDens_det_proof S h m hm hT'
  obtain ⟨Ω₂, mΩ₂, P₂, hP₂, ℱ₂, Ĝ, hGc, hGz, hG⟩ :=
    Q45.exists_gaussian_martingale T' hT'.le (tl2CbDens S ρβ m T') hdet
  have hG' : IsHilbertMartingaleWithCovariation P₂ ℱ₂ T' Ĝ (fun r _ => tl2CbDens S ρβ m T' r) := by
    have e : (fun (r : ℝ) (_ : Ω₂) => if r ≤ T' then tl2CbDens S ρβ m T' r else 0) =
        fun r _ => tl2CbDens S ρβ m T' r := by
      funext r ω
      by_cases hr : r ≤ T'
      · simp [hr]
      · have := hzero r (not_le.1 hr)
        simp [hr, this]
    rwa [e] at hG
  haveI := hP₂
  obtain ⟨Z, hZS, hZc, hZae⟩ := hEv.exists_conv T' hT' Ω₂ P₂ ℱ₂ Ĝ _ hG'
  obtain ⟨Zm, hZmm, hZmc, hZmae⟩ := thermlin_measurable_version (P := P₂) hT'.le Z hZae hZc
  exact ⟨Ω₂, mΩ₂, P₂, hP₂, ℱ₂, Ĝ, Zm, hG',
    fun t ht => thermlin_isStochConv_congr (hZS t ht) (hZmae t ht), hZmm, hZmc⟩

/-- Swapping the factors of a product measure. -/
theorem tl2As_swap_law {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) [SigmaFinite μ] (ν : Measure β) [SigmaFinite ν] (F : β × α → γ)
    (hF : AEMeasurable F (ν.prod μ)) :
    (ν.prod μ).map F = (μ.prod ν).map (fun w : α × β => F w.swap) := by
  have e : ν.prod μ = (μ.prod ν).map Prod.swap := (Measure.prod_swap).symm
  conv_lhs => rw [e]
  rw [AEMeasurable.map_map_of_aemeasurable (by rwa [← e]) measurable_swap.aemeasurable]
  rfl

/-- ENNReal bookkeeping for the final constants. -/
theorem tl2As_arith {x₀ x₁ x₂ : ℝ} (h₀ : 0 ≤ x₀) (h₁ : 0 ≤ x₁) (h₂ : 0 ≤ x₂) (M : ℝ≥0∞) :
    ENNReal.ofReal x₀ * M + ENNReal.ofReal x₁ + ENNReal.ofReal x₂ ≤ ENNReal.ofReal (x₀ + x₁ + x₂) * (1 + M) := by
  rw [ENNReal.ofReal_add (by positivity) h₂, ENNReal.ofReal_add h₀ h₁]
  have hM0 : ENNReal.ofReal x₀ * M ≤ (ENNReal.ofReal x₀ + ENNReal.ofReal x₁ + ENNReal.ofReal x₂) * M := by
    gcongr
    exact le_trans le_self_add le_self_add
  have h1 : ENNReal.ofReal x₁ ≤ ENNReal.ofReal x₀ + ENNReal.ofReal x₁ + ENNReal.ofReal x₂ := by
    calc ENNReal.ofReal x₁ ≤ ENNReal.ofReal x₀ + ENNReal.ofReal x₁ := le_add_self
      _ ≤ _ := le_self_add
  have h2 : ENNReal.ofReal x₂ ≤ ENNReal.ofReal x₀ + ENNReal.ofReal x₁ + ENNReal.ofReal x₂ := le_add_self
  have h12 : ENNReal.ofReal x₁ + ENNReal.ofReal x₂ ≤ ENNReal.ofReal x₀ + ENNReal.ofReal x₁ + ENNReal.ofReal x₂ := by
    rw [add_assoc]; exact le_add_self
  calc ENNReal.ofReal x₀ * M + ENNReal.ofReal x₁ + ENNReal.ofReal x₂
      = ENNReal.ofReal x₀ * M + (ENNReal.ofReal x₁ + ENNReal.ofReal x₂) := by rw [add_assoc]
    _ ≤ (ENNReal.ofReal x₀ + ENNReal.ofReal x₁ + ENNReal.ofReal x₂) * M +
        (ENNReal.ofReal x₀ + ENNReal.ofReal x₁ + ENNReal.ofReal x₂) := add_le_add hM0 h12
    _ = (ENNReal.ofReal x₀ + ENNReal.ofReal x₁ + ENNReal.ofReal x₂) * (1 + M) := by
      rw [mul_add, mul_one, add_comm]

end HRS.ThermLin.Plan2
