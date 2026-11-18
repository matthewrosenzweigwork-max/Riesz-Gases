import HRS.Uniform.Comparison
import HRS.Uniform.Q48dAux4

/-!
# T25MW, part 1: `WinMaxU` implies the repaired `MaxWindows`

A measurable-in-`t` stochastic convolution `Z` is a.e. equal to the witness `Z'` of `WinMaxU` at every time of the window
(uniqueness of the `L²` limit of the Riemann sums); with a.e. continuity of both paths and countably many rational
times, `Z = Z'` on the whole window almost surely, so the sup integrals agree.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.T25MW

open HRS.Uniform

theorem t25mw_maxWindows_of_winMaxU.{u} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    {V : ℝ → ℝ → H →L[ℝ] H} {T C : ℝ} (hW : HRS.Uniform.Q48d.WinMaxU.{u} V T C) :
    HRS.Uniform.MaxWindows.{u, 0} V T C := by
  intro Ω mΩ P hP ℱ a ha M Sg hM Z hZm hZ hZc
  obtain ⟨Z', h1, h2, h3, h4⟩ := hW Ω P ℱ a ha M Sg hM
  have hDm : ∀ τ ∈ Icc a (a + T), AEStronglyMeasurable (M τ) P := fun τ hτ =>
    (hM.sq_int τ ⟨ha.trans hτ.1, hτ.2⟩).aestronglyMeasurable
  have hae : ∀ t ∈ Icc a (a + T), Z t =ᵐ[P] Z' t := by
    intro t ht
    have hDt : ∀ τ ∈ Icc a t, AEStronglyMeasurable (M τ) P := fun τ hτ =>
      hDm τ ⟨hτ.1, hτ.2.trans ht.2⟩
    have hZs : AEStronglyMeasurable (Z t) P := (hZm t ht).aestronglyMeasurable
    exact Q48d.sc_unique (V := V) ht.1 hDt hZs (h2 t ht)
      ((Q48d.isStochConv_iff hZs hDt).1 (hZ t ht))
      ((Q48d.isStochConv_iff (h2 t ht) hDt).1 (h1 t ht))
  have hall : ∀ᵐ ω ∂P, ∀ t ∈ Icc a (a + T), Z t ω = Z' t ω := by
    by_cases hab : a ≤ a + T
    · have hq : ∀ᵐ ω ∂P, ∀ q ∈ Q48d.ratIcc a (a + T), Z q ω = Z' q ω := by
        rw [ae_ball_iff (Q48d.countable_ratIcc a (a + T))]
        intro q hq
        exact hae q (Q48d.ratIcc_subset hab hq)
      filter_upwards [hq, hZc, h3] with ω hω hc hc'
      exact Q48d.eqOn_Icc_of_ratIcc hab hc hc' hω
    · have : Icc a (a + T) = ∅ := Icc_eq_empty hab
      refine Eventually.of_forall fun ω t ht => ?_
      rw [this] at ht
      exact absurd ht (notMem_empty t)
  calc ∫⁻ ω, (⨆ t ∈ Icc a (a + T), ‖Z t ω‖ₑ) ^ 2 ∂P
      = ∫⁻ ω, (⨆ t ∈ Icc a (a + T), ‖Z' t ω‖ₑ) ^ 2 ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hall] with ω hω
        congr 1
        refine iSup_congr fun t => iSup_congr fun ht => ?_
        rw [hω t ht]
    _ ≤ _ := h4

end HRS.T25MW
