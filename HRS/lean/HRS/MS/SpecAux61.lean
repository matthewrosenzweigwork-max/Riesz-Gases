import HRS.MS.SpecAux60

/-!
# S8R: the trace bound `E ‖S_r - Sb_r‖²_HS` on the enlarged space (S8.7, packet C4)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.

* `s8p_good_ae_realization`: almost surely all particles are good points;
* `s8p_trace_realization`: `∫⁻ ∑_j ‖(S(π w) - Sb) b_j‖² dP' ≤ 4 · (stationary bound)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s8p_good_ae_realization {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {N : ℕ} (hN : 0 < N)
    {s a β Cs : ℝ} (hS : S45.S45Static d s a β Cs N) {Y : Ω → EucConfig d N} (hYm : Measurable Y)
    (hlaw : P.map Y = s8p_QN d s a β N) {om : ℕ → ℝ} {e : ℕ → Euc d → ℝ} {τ : ℝ}
    (hgood : ∀ᵐ x ∂(thermalMeasure d s a β), s8p_good om e τ x) :
    ∀ᵐ z ∂P, ∀ i, s8p_good om e τ (Y z i) := by
  rw [ae_all_iff]
  intro i
  have hev : Measurable fun X : EucConfig d N => X i := measurable_pi_apply i
  have h1 : P.map (fun z => Y z i) = HRS.Whole.firstMarginal (s8p_QN d s a β N) := by
    calc P.map (fun z => Y z i) = (P.map Y).map (fun X : EucConfig d N => X i) :=
          (Measure.map_map hev hYm).symm
      _ = (s8p_QN d s a β N).map (fun X : EucConfig d N => X i) := by rw [hlaw]
      _ = _ := s8p_map_eval hN hS.exch i
  have hac : HRS.Whole.firstMarginal (s8p_QN d s a β N) ≪ thermalMeasure d s a β :=
    Measure.absolutelyContinuous_of_le_smul (s8p_fm_le hS)
  have h2 : ∀ᵐ x ∂(HRS.Whole.firstMarginal (s8p_QN d s a β N)), s8p_good om e τ x := hac.ae_le hgood
  rw [← h1] at h2
  exact ae_of_ae_map (hev.comp hYm).aemeasurable h2

theorem s8p_trace_realization {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    {P' : Measure Ω'} {π : Ω' → Ω} (hπ : MeasurePreserving π P' P) {N : ℕ} (hN : 2 ≤ N)
    {s a β Cs : ℝ} (hCs : 0 ≤ Cs) (hS : S45.S45Static d s a β Cs N)
    [IsProbabilityMeasure (thermalMeasure d s a β)] (hβ : 0 < β) {om : ℕ → ℝ}
    (hom : ∀ l, 0 < om l) (hmono : Monotone om) {τ : ℝ} (hτ : 0 < τ)
    (hsum : Summable (s8p_dv β om τ)) {t₀ C4 : ℝ} (hC4 : 0 ≤ C4) (e : ℕ → Euc d → ℝ)
    (he : ∀ l, ContDiff ℝ ∞ (e l))
    (hgrad : ∀ i j, ∫ x, s8p_f e i j x ∂(thermalMeasure d s a β) = if i = j then om i else 0)
    (hL4 : ∀ l, eLpNorm (fun x => ‖gradient (e l) x‖) 4 (thermalMeasure d s a β) ≤
      ENNReal.ofReal (C4 * Real.exp (t₀ * om l)))
    {Y : Ω → EucConfig d N} (hYm : Measurable Y) (hlaw : P.map Y = s8p_QN d s a β N)
    (hgood : ∀ᵐ x ∂(thermalMeasure d s a β), s8p_good om e τ x)
    {S : Ω → SeqL2 →L[ℝ] SeqL2} {Sb : SeqL2 →L[ℝ] SeqL2}
    (hSsq : ∀ z, IsSqrtOfForm (S z) (hsCovForm (fun ia : Fin N × Fin d =>
      Real.sqrt (2 / (N * β)) • s8p_Gv om e τ (Y z ia.1) ia.2)))
    (hSb : IsSqrtOfForm Sb (s8p_Cdet hβ hom hτ)) :
    ∫⁻ w, ∑' j, ‖(S (π w) - Sb) (S45.s45_seqBasis j)‖ₑ ^ 2 ∂P' ≤
      4 * (ENNReal.ofReal (C4 ^ 4 / (β * om 0) * (Cs / N + Cs ^ 2 * HRS.deltaN d s N ^ 2)) *
        (∑' l, ENNReal.ofReal (Real.exp (-(τ / 2 - 2 * t₀) * om l))) ^ 2) := by
  have hN0 : 0 < N := by omega
  have hgoodY := s8p_good_ae_realization hN0 hS hYm hlaw hgood
  have hgoodY' : ∀ᵐ w ∂P', ∀ i, s8p_good om e τ (Y (π w) i) :=
    hπ.quasiMeasurePreserving.ae hgoodY
  have hQm := s8p_measurable_Qform (N := N) hN0 β om τ e he (thermalMeasure d s a β)
  calc ∫⁻ w, ∑' j, ‖(S (π w) - Sb) (S45.s45_seqBasis j)‖ₑ ^ 2 ∂P'
      ≤ ∫⁻ w, 4 * s8p_Qform β om τ e (thermalMeasure d s a β) (Y (π w)) ∂P' := by
        refine lintegral_mono_ae ?_
        filter_upwards [hgoodY'] with w hw
        exact s8p_config_hs_bound hN0 hβ hom hτ hsum e _ hgrad (Y (π w)) hw (hSsq (π w)) hSb
    _ = ∫⁻ z, 4 * s8p_Qform β om τ e (thermalMeasure d s a β) (Y z) ∂P :=
        hπ.lintegral_comp (measurable_const.mul (hQm.comp hYm) :
          Measurable fun z => 4 * s8p_Qform β om τ e (thermalMeasure d s a β) (Y z))
    _ = 4 * ∫⁻ X, s8p_Qform β om τ e (thermalMeasure d s a β) X ∂(s8p_QN d s a β N) := by
        rw [lintegral_const_mul (f := fun z => s8p_Qform β om τ e (thermalMeasure d s a β) (Y z)) 4
          (hQm.comp hYm), ← hlaw, lintegral_map hQm hYm]
    _ ≤ _ := by
        gcongr
        exact s8p_Q_sum_bound hN hCs hS hβ hom hmono hτ hC4 e he hgrad hL4

end HRS.MS.Spec
