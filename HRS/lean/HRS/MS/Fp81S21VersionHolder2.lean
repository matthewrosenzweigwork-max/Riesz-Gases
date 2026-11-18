import HRS.MS.Fp81S21VersionHolder

set_option autoImplicit false
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.Fp81.S21
open HRS.MP.KC HRS.MS.ProClosureS111 HRS.Whole.AppendixALemmas

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- A fourth-increment estimate gives a measurable continuous modification,
with a uniform fourth-moment path bound and a quantitative dyadic envelope. -/
theorem fp81s21_fourth_continuous_version
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ → Ω → E)
    {H C M : ℝ} (hH : 0 < H) (hC : 0 ≤ C)
    (hX : ∀ t, Measurable (X t)) (hX0 : MemLp (X 0) 4 P)
    (hM : (∫ ω, ‖X 0 ω‖ ^ 4 ∂P) ≤ M)
    (hmom : ∀ s ∈ Set.Icc (0 : ℝ) H, ∀ t ∈ Set.Icc (0 : ℝ) H,
      (∫⁻ ω, ENNReal.ofReal (‖X t ω - X s ω‖ ^ 4) ∂P) ≤
        ENNReal.ofReal (C * |t - s| ^ 2)) :
    ∃ Y : Ω → C(Set.Icc (0 : ℝ) H, E), Measurable Y ∧ MemLp Y 4 P ∧
      (∀ t : Set.Icc (0 : ℝ) H, (fun ω => Y ω t) =ᵐ[P] X t) ∧
      (∫ ω, ‖Y ω‖ ^ 4 ∂P) ≤
        8 * (M + (mkc_c (9 / 10 : ℝ)) ^ 4 *
          (C * H ^ 2 / (1 - 1 / (2 * (9 / 10 : ℝ) ^ 4)))) ∧
      ∃ L : Ω → ℝ, (∀ ω, 0 ≤ L ω) ∧ MemLp L 4 P ∧
        (∫ ω, L ω ^ 4 ∂P) ≤ C * H ^ 2 / (1 - 1 / (2 * (9 / 10 : ℝ) ^ 4)) ∧
        ∀ᵐ ω ∂P, ∀ s t : Set.Icc (0 : ℝ) H, ∀ m : ℕ,
          |(t : ℝ) - s| ≤ H / 2 ^ m →
            ‖Y ω t - Y ω s‖ ≤ mkc_c (9 / 10 : ℝ) * (L ω * (9 / 10 : ℝ) ^ m) := by
  let r : ℝ := 9 / 10
  have hr0 : 0 < r := by norm_num [r]
  have hr1 : r < 1 := by norm_num [r]
  have hr : 1 < 2 * r ^ 4 := by norm_num [r]
  have hqr : 1 ≤ (9 / 10 : ℝ) * 2 ^ (1 : ℝ) * r ^ (4 : ℝ) := by
    norm_num [r, Real.rpow_natCast]
  have hmom' : ∀ s ∈ Set.Icc (0 : ℝ) H, ∀ t ∈ Set.Icc (0 : ℝ) H,
      (∫⁻ ω, ‖X t ω - X s ω‖ₑ ^ (4 : ℝ) ∂P) ≤
        ENNReal.ofReal (C * |t - s| ^ (1 + (1 : ℝ))) := by
    intro s hs t ht
    have he (ω : Ω) : ‖X t ω - X s ω‖ₑ ^ (4 : ℝ) =
        ENNReal.ofReal (‖X t ω - X s ω‖ ^ 4) := by
      calc
        _ = ‖X t ω - X s ω‖ₑ ^ (4 : ℕ) := ENNReal.rpow_natCast _ 4
        _ = _ := by rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
    simp_rw [he]
    simpa only [show (1 : ℝ) + 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] using hmom s hs t ht
  let Y : Ω → C(Set.Icc (0 : ℝ) H, E) := fun ω =>
    contPathOf H (fun t => mkc_Zc X H r t ω)
  have hY4 : MemLp Y 4 P :=
    continuous_modification_memLp_four_of_fourth_increments P X hH hr0 hr1 hr hX hX0 hC hmom
  have hYm : Measurable Y := by
    refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
    have he : (fun ω => Y ω t) = fun ω => mkc_Zc X H r t ω := by
      funext ω
      exact mkc_contPathOf_apply X hH hr0.le hr1 ω t
    rw [he]
    exact mkc_Zc_meas X H r hH hr0.le hr1 hX t
  have hYeq : ∀ t : Set.Icc (0 : ℝ) H, (fun ω => Y ω t) =ᵐ[P] X t := by
    intro t
    have he : (fun ω => Y ω t) = fun ω => mkc_Zc X H r t ω := by
      funext ω
      exact mkc_contPathOf_apply X hH hr0.le hr1 ω t
    rw [he]
    exact mkc_Zc_ae_eq X H r P hX hH (by norm_num) (by norm_num) hmom'
      hr0 hr1 (by norm_num : 0 < (9 / 10 : ℝ)) (by norm_num : (9 / 10 : ℝ) < 1)
      hqr t.property
  have hYbound := continuous_modification_fourth_moment_bound P X hH hr0 hr1 hr hX hX0 hC hmom
  obtain ⟨L, hL0, hL, hgood, hLbound⟩ :=
    fp81s21_fourth_dyadic_envelope P X hH hr0 hC hr hX hmom
  refine ⟨Y, hYm, hY4, hYeq, ?_, L, hL0, hL, ?_, ?_⟩
  · change (∫ ω, ‖Y ω‖ ^ 4 ∂P) ≤ _
    calc
      _ ≤ 8 * ((∫ ω, ‖X 0 ω‖ ^ 4 ∂P) +
          (mkc_c r) ^ 4 * (C * H ^ 2 / (1 - 1 / (2 * r ^ 4)))) := hYbound
      _ ≤ _ := by gcongr
  · exact hLbound
  · filter_upwards [hgood] with ω hω s t m hdist
    rw [show Y ω t = mkc_Zc X H r t ω from mkc_contPathOf_apply X hH hr0.le hr1 ω t,
      show Y ω s = mkc_Zc X H r s ω from mkc_contPathOf_apply X hH hr0.le hr1 ω s]
    exact mkc_Zc_dist_le X H r hH hr0.le hr1 (hL0 ω) hω t.property s.property m hdist

#print axioms fp81s21_fourth_continuous_version

end HRS.Fp81.S21
