import HRS.MS.S88BDM02
import HRS.Whole.Orbits

/-!
# S8.8.M03: coordinate summation and exact square-root normalization

`s88_l2_maximal_decay`: summing the M02 coordinate maxima (Tonelli) gives
`E sup_i ‖Y(σ_i)‖²_{ℓ²} ≤ 64 K (1+T²) (∑ b_α) e^{-2cu}`, hence the half-power bound in `ℝ≥0∞`.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace HRS.MS.S88Breakdown

theorem s88_l2_maximal_decay {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {κ ι : Type*} [Countable κ] [Countable ι]
    (T K c u : ℝ) (hT : 0 < T) (hK : 0 ≤ K) (b : κ → ℝ)
    (hb : ∀ α, 0 ≤ b α) (hsum : Summable b) (Y : ℝ → Ω → κ → ℝ)
    (hmem : ∀ (α : κ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T → MemLp (fun z => Y t z α) 2 P)
    (hbase : ∀ α : κ,
      (∫⁻ z, ENNReal.ofReal ((Y 0 z α) ^ 2) ∂P) ≤
        ENNReal.ofReal (K * b α * Real.exp (-2 * c * u)))
    (hinc : ∀ (α : κ) (s : ℝ), s ∈ Set.Icc (0 : ℝ) T →
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) T →
        (∫⁻ z, ENNReal.ofReal ((Y s z α - Y t z α) ^ 2) ∂P) ≤
          ENNReal.ofReal (K * b α * Real.exp (-2 * c * u) * (s - t) ^ 2))
    (σ : ι → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc (0 : ℝ) T) :
    ((∫⁻ z, (⨆ i : ι, HRS.Whole.l2NormE (Y (σ i) z)) ^ 2 ∂P) ^ (1 / 2 : ℝ)) ≤
      ENNReal.ofReal (Real.sqrt (64 * K * (1 + T ^ 2) * ∑' α, b α) *
        Real.exp (-c * u)) := by
  set E : ℝ := Real.exp (-2 * c * u) with hE
  have hE0 : 0 < E := Real.exp_pos _
  -- coordinate maxima
  have hcoord : ∀ α : κ, AEMeasurable (fun z => ⨆ i : ι, ENNReal.ofReal ((Y (σ i) z α) ^ 2)) P ∧
      (∫⁻ z, (⨆ i : ι, ENNReal.ofReal ((Y (σ i) z α) ^ 2)) ∂P) ≤
        ENNReal.ofReal (64 * (K * b α * E + T ^ 2 * (K * b α * E))) := by
    intro α
    have hBD : 0 ≤ K * b α * E := by have := hb α; positivity
    exact s88_countable_maximal P T (K * b α * E) (K * b α * E) hT hBD hBD (fun t z => Y t z α)
      (hmem α) (hbase α) (hinc α) σ hσ
  -- pointwise: squared norm of the supremum
  have hpw : ∀ z, (⨆ i : ι, HRS.Whole.l2NormE (Y (σ i) z)) ^ 2 ≤
      ∑' α : κ, ⨆ i : ι, ENNReal.ofReal ((Y (σ i) z α) ^ 2) := by
    intro z
    have hi : ∀ i, HRS.Whole.l2NormE (Y (σ i) z) ≤
        (∑' α : κ, ⨆ i : ι, ENNReal.ofReal ((Y (σ i) z α) ^ 2)) ^ (1 / 2 : ℝ) := by
      intro i
      unfold HRS.Whole.l2NormE
      refine ENNReal.rpow_le_rpow (ENNReal.tsum_le_tsum fun α => ?_) (by norm_num)
      exact le_iSup (fun i => ENNReal.ofReal ((Y (σ i) z α) ^ 2)) i
    have h1 := iSup_le hi
    calc (⨆ i : ι, HRS.Whole.l2NormE (Y (σ i) z)) ^ 2
        ≤ ((∑' α : κ, ⨆ i : ι, ENNReal.ofReal ((Y (σ i) z α) ^ 2)) ^ (1 / 2 : ℝ)) ^ 2 :=
          pow_le_pow_left' h1 2
      _ = _ := by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          norm_num
  have hint : (∫⁻ z, (⨆ i : ι, HRS.Whole.l2NormE (Y (σ i) z)) ^ 2 ∂P) ≤
      ENNReal.ofReal (64 * K * (1 + T ^ 2) * (∑' α, b α) * E) := by
    calc _ ≤ ∫⁻ z, ∑' α : κ, ⨆ i : ι, ENNReal.ofReal ((Y (σ i) z α) ^ 2) ∂P :=
          lintegral_mono hpw
      _ = ∑' α : κ, ∫⁻ z, (⨆ i : ι, ENNReal.ofReal ((Y (σ i) z α) ^ 2)) ∂P :=
          lintegral_tsum fun α => (hcoord α).1
      _ ≤ ∑' α : κ, ENNReal.ofReal (64 * K * (1 + T ^ 2) * E * b α) := by
          refine ENNReal.tsum_le_tsum fun α => (hcoord α).2.trans (ENNReal.ofReal_le_ofReal ?_)
          refine le_of_eq ?_
          ring
      _ = ENNReal.ofReal (∑' α : κ, 64 * K * (1 + T ^ 2) * E * b α) := by
          refine (ENNReal.ofReal_tsum_of_nonneg (fun α => ?_) (hsum.mul_left _)).symm
          have := hb α; positivity
      _ = _ := by
          rw [tsum_mul_left]; ring_nf
  have hV0 : 0 ≤ 64 * K * (1 + T ^ 2) * (∑' α, b α) := by
    have : 0 ≤ ∑' α, b α := tsum_nonneg hb
    positivity
  calc ((∫⁻ z, (⨆ i : ι, HRS.Whole.l2NormE (Y (σ i) z)) ^ 2 ∂P) ^ (1 / 2 : ℝ))
      ≤ (ENNReal.ofReal (64 * K * (1 + T ^ 2) * (∑' α, b α) * E)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hint (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt (64 * K * (1 + T ^ 2) * ∑' α, b α) * Real.exp (-c * u)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
        congr 1
        rw [← Real.sqrt_eq_rpow, Real.sqrt_mul hV0, hE]
        congr 1
        rw [show -2 * c * u = (-c * u) + (-c * u) by ring, Real.exp_add]
        exact Real.sqrt_mul_self (Real.exp_pos _).le

end HRS.MS.S88Breakdown
