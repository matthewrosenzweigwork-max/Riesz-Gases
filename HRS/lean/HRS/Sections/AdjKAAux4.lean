import HRS.Sections.AdjKAAux3

/-!
# ADJKA part 4: the window maximal estimate with exponent `p ≥ 2` for a quasi-contractive plain evolution

`adjka_winmax_p` is `Q48e.winmax_of_quasi` with the Kotelenez constant `CD p K T` for the `L^p` norm
(`Kot.sup_Z_bound` is stated for every `p ≥ 1`).
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.AdjK

open HRS HRS.MRep HRS.Uniform HRS.Uniform.Q48e

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

theorem adjka_winmax_p {V : ℝ → ℝ → E →L[ℝ] E} (hV : ∀ T : ℝ, 0 ≤ T → IsPlainEvolution V T) {K : ℝ}
    (hK : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖V t u‖ ≤ Real.exp (K * (t - u) / 2)) {T : ℝ} (hT : 0 ≤ T)
    {p : ℝ} (hp : 2 ≤ p) :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ mΩ) (a : ℝ), 0 ≤ a →
      ∀ (M : ℝ → Ω → E) (Sg : ℝ → Ω → (E →L[ℝ] E →L[ℝ] ℝ)),
        IsHilbertMartingaleWithCovariation P ℱ (a + T) M Sg →
        ∃ Z : ℝ → Ω → E,
          (∀ t ∈ Icc a (a + T), IsStochConv P V (ContinuousLinearMap.id ℝ E) M a t (Z t)) ∧
          (∀ t ∈ Icc a (a + T), AEStronglyMeasurable (Z t) P) ∧
          (∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Icc a (a + T))) ∧
          ∫⁻ ω, (⨆ t ∈ Icc a (a + T), ‖Z t ω‖ₑ) ^ p ∂P ≤
            ENNReal.ofReal (Kot.CD p K T) *
              ∫⁻ ω, (∫⁻ r in Icc a (a + T), ENNReal.ofReal (traceNormForm (Sg r ω))) ^ (p / 2) ∂P := by
  intro Ω mΩ P _ ℱ a ha M Sg hM
  have hcomp : IsCompleteFiltration P (augFiltration P ℱ) := augFiltration_isComplete ℱ
  have hM' := Kot.isHMC_aug hM
  have hW := isHMC_window hcomp ha hT hM'
  set V' : ℝ → ℝ → E →L[ℝ] E := fun t r => V (a + t) (a + r) with hV'def
  obtain ⟨hself, hcomp0, hcont0⟩ := hV (a + T) (by linarith)
  have hEV : Kot.EvolBound V' K T :=
    { norm_le := fun r t hr hrt htT => by
        have := hK (a + r) (a + t) (by linarith) (by linarith)
        simpa [hV'def, add_sub_add_left_eq_sub] using this
      comp := fun r t u hr hrt htu huT => by
        have := hcomp0 (a + r) (a + t) (a + u) (by linarith) (by linarith) (by linarith) (by linarith)
        exact this
      self := fun t ht0 htT => hself (a + t) ⟨by linarith, by linarith⟩ }
  have hcont' : ∀ x : E, ContinuousOn (fun p : ℝ × ℝ => V' p.1 p.2 x)
      {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T} := by
    intro x
    have h := hcont0 x
    have hc : ContinuousOn (fun p : ℝ × ℝ => (a + p.1, a + p.2)) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T} :=
      ((continuous_const.add continuous_fst).prodMk (continuous_const.add continuous_snd)).continuousOn
    refine h.comp hc fun p hp => ?_
    exact ⟨by linarith [hp.1], by linarith [hp.2.1], by linarith [hp.2.2]⟩
  have hcomp' : IsCompleteFiltration P (winFiltration (augFiltration P ℱ) a T) :=
    fun τ s hs h0 => hcomp (wt a T τ) s hs h0
  obtain ⟨m, Z', hm, hZc, hlim⟩ := Kot.exists_dyadic_limit hcomp' hW hEV hcont' hT
  have hmem : ∀ t ∈ Icc a (a + T), t - a ∈ Icc (0 : ℝ) T :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨fun t ω => Z' (t - a) ω, ?_, ?_, ?_, ?_⟩
  · -- the stochastic convolution
    intro t ht ε hε
    obtain ⟨δ, hδ, hconv⟩ := Kot.hconv_Z hcomp' hW hEV hcont' hT hm hlim (hmem t ht) ε hε
    refine ⟨δ, hδ, fun n r hr0 hrn hmono hmesh => ?_⟩
    have hr' := hconv n (fun i => r i - a) (by simp [hr0]) (by simp [hrn, sub_eq_zero]) 
      (fun i j h => by simpa using hmono h) (fun i => by simpa using hmesh i)
    refine lt_of_le_of_lt (le_of_eq ?_) hr'
    refine lintegral_congr fun ω => ?_
    congr 3
    rw [Q48d.riemannSum_id]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi1 : r i.castSucc - a ∈ Icc (0 : ℝ) T := by
      have := Q48d.mem_Icc_of_part hr0 hrn hmono i.castSucc
      exact ⟨by linarith [this.1], by linarith [this.2, ht.2]⟩
    have hi2 : r i.succ - a ∈ Icc (0 : ℝ) T := by
      have := Q48d.mem_Icc_of_part hr0 hrn hmono i.succ
      exact ⟨by linarith [this.1], by linarith [this.2, ht.2]⟩
    simp only [hV'def, wt_of_mem hi1, wt_of_mem hi2, add_sub_cancel]
    congr 1
    abel
  · -- measurability
    intro t ht
    have hτ := hmem t ht
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun k ω =>
      Kot.rsProc V' (fun τ ω => M (wt a T τ) ω - M a ω) (Kot.dy T (m k)) (2 ^ m k) (t - a) ω)
      (fun k => ?_) ?_
    · exact Kot.aestronglyMeasurable_rsTag hW (Kot.dy_mono hT _) (by rw [Kot.dy_zero]) (by rw [Kot.dy_top]) _ (t - a)
    · filter_upwards [hlim] with ω hω
      exact hω (t - a) hτ
  · -- continuity
    filter_upwards [hZc] with ω hω
    exact hω.comp (continuous_id.sub continuous_const).continuousOn fun t ht => hmem t ht
  · -- the bound
    have hb := Kot.sup_Z_bound hcomp' hW hEV hT hZc hlim (p := p) (by linarith)
    have hsup : ∀ ω, (⨆ t ∈ Icc a (a + T), ‖Z' (t - a) ω‖ₑ) = ⨆ τ ∈ Icc (0 : ℝ) T, ‖Z' τ ω‖ₑ := by
      intro ω
      refine le_antisymm (iSup₂_le fun t ht => ?_) (iSup₂_le fun τ hτ => ?_)
      · exact le_iSup₂ (f := fun τ (_ : τ ∈ Icc (0 : ℝ) T) => ‖Z' τ ω‖ₑ) (t - a) (hmem t ht)
      · have : a + τ ∈ Icc a (a + T) := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
        have h := le_iSup₂ (f := fun t (_ : t ∈ Icc a (a + T)) => ‖Z' (t - a) ω‖ₑ) (a + τ) this
        simpa using h
    calc ∫⁻ ω, (⨆ t ∈ Icc a (a + T), ‖Z' (t - a) ω‖ₑ) ^ p ∂P
        = ∫⁻ ω, (⨆ τ ∈ Icc (0 : ℝ) T, ‖Z' τ ω‖ₑ) ^ p ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [hsup ω]
      _ ≤ ENNReal.ofReal (Kot.CD p K T) * ∫⁻ ω, (∫⁻ r in Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm
            ((fun σ ω => if σ ≤ T then Sg (a + σ) ω else 0) r ω))) ^ (p / 2) ∂P := hb
      _ = ENNReal.ofReal (Kot.CD p K T) * ∫⁻ ω, (∫⁻ r in Icc a (a + T), ENNReal.ofReal (traceNormForm (Sg r ω))) ^ (p / 2) ∂P := by
          congr 1
          refine lintegral_congr fun ω => ?_
          congr 1
          rw [← lintegral_Icc_shift (fun r => ENNReal.ofReal (traceNormForm (Sg r ω))) a T]
          refine setLIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
          simp only [hσ.2, if_true]

end HRS.AdjK
