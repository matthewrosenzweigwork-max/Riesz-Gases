import HRS.MC.S7FCW6F4

/-!
# Block B of the F5 packet: the shifted Doob inequality (proof of `fcf5_B1_shifted_doob`)

Route: the process `t ↦ M (a + clamp T t) - M a` (with `clamp T t = min (max t 0) T`) is a martingale for the
filtration `t ↦ ℱ (a + clamp T t)`; its supremum over `[0, T]` is the supremum of `|M - M a|` over `[a, a+T]`, and
F4 (`s7_FC_F4_doob_Lq_proof`, `S7FCW6F4.lean`) applies.  If `M (a+T)` is not integrable, the right-hand side is `∞`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCF5B

/-- The clamped time `t ↦ min (max t 0) T`. -/
def S7FCF5B_clamp (T t : ℝ) : ℝ := min (max t 0) T

lemma S7FCF5B_clamp_mono (T : ℝ) : Monotone (S7FCF5B_clamp T) := fun _ _ hst =>
  min_le_min_right _ (max_le_max hst le_rfl)

lemma S7FCF5B_clamp_cont (T : ℝ) : Continuous (S7FCF5B_clamp T) :=
  (continuous_id.max continuous_const).min continuous_const

lemma S7FCF5B_clamp_nonneg {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : 0 ≤ S7FCF5B_clamp T t :=
  le_min (le_max_right _ _) hT

lemma S7FCF5B_clamp_le (T t : ℝ) : S7FCF5B_clamp T t ≤ T := min_le_right _ _

lemma S7FCF5B_clamp_of_mem {T t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    S7FCF5B_clamp T t = t := by
  unfold S7FCF5B_clamp
  rw [max_eq_left ht.1, min_eq_left ht.2]

lemma S7FCF5B_clamp_top {T : ℝ} (hT : 0 ≤ T) : S7FCF5B_clamp T T = T :=
  S7FCF5B_clamp_of_mem ⟨hT, le_rfl⟩

/-- `x ≤ 1 + x ^ q` in `ℝ≥0∞` for `q ≥ 1`. -/
lemma S7FCF5B_enorm_le_one_add_rpow {q : ℝ} (hq : 1 ≤ q) (x : ℝ≥0∞) : x ≤ 1 + x ^ q := by
  rcases le_total x 1 with hx | hx
  · exact hx.trans le_self_add
  · calc x = x ^ (1 : ℝ) := (ENNReal.rpow_one x).symm
      _ ≤ x ^ q := ENNReal.rpow_le_rpow_of_exponent_le hx hq
      _ ≤ 1 + x ^ q := le_add_self

/-- **B1 (shifted Doob inequality)**, proof. -/
theorem fcf5_B1_shifted_doob_proof {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (M : ℝ → Ω → ℝ) (hM : Martingale M ℱ P)
    (hc : ∀ᵐ ω ∂P, Continuous fun t => M t ω) (q : ℝ) (hq : 1 < q) (a : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc a (a + T), ‖M t ω - M a ω‖ₑ) ^ q ∂P ≤
      ENNReal.ofReal ((q / (q - 1)) ^ q) * ∫⁻ ω, ‖M (a + T) ω - M a ω‖ₑ ^ q ∂P := by
  have hcpos : 0 < ENNReal.ofReal ((q / (q - 1)) ^ q) :=
    ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (div_pos (by linarith) (by linarith)) _)
  by_cases hint : Integrable (M (a + T)) P
  swap
  · -- the endpoint is not integrable: then `M a = 0` a.e. and the right-hand side is infinite
    have hMa : M a =ᵐ[P] 0 := by
      have h := hM.2 a (a + T) (by linarith)
      rw [condExp_of_not_integrable hint] at h
      exact h.symm
    have hinf : ∫⁻ ω, ‖M (a + T) ω - M a ω‖ₑ ^ q ∂P = ⊤ := by
      have hae : (fun ω => ‖M (a + T) ω - M a ω‖ₑ ^ q) =ᵐ[P] fun ω => ‖M (a + T) ω‖ₑ ^ q := by
        filter_upwards [hMa] with ω hω
        simp [hω]
      rw [lintegral_congr_ae hae]
      by_contra hne
      apply hint
      have hfin : ∫⁻ ω, ‖M (a + T) ω‖ₑ ^ q ∂P < ⊤ := lt_top_iff_ne_top.mpr hne
      refine ⟨((hM.1 (a + T)).mono (ℱ.le _)).aestronglyMeasurable, ?_⟩
      show ∫⁻ ω, ‖M (a + T) ω‖ₑ ∂P < ⊤
      have hle : ∫⁻ ω, ‖M (a + T) ω‖ₑ ∂P ≤ ∫⁻ ω, (1 + ‖M (a + T) ω‖ₑ ^ q) ∂P :=
        lintegral_mono fun ω => S7FCF5B_enorm_le_one_add_rpow hq.le _
      rw [lintegral_add_left measurable_const, lintegral_one, measure_univ] at hle
      exact lt_of_le_of_lt hle (ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, hfin⟩)
    rw [hinf, ENNReal.mul_top hcpos.ne']
    exact le_top
  -- the endpoint is integrable, hence so is `M v` for all `v ≤ a + T` (a conditional expectation)
  have hint_v : ∀ v : ℝ, v ≤ a + T → Integrable (M v) P := fun v hvT =>
    (integrable_condExp).congr (hM.2 v (a + T) hvT)
  let ℱ' : Filtration ℝ mΩ :=
    { seq := fun t => ℱ (a + S7FCF5B_clamp T t)
      mono' := fun s t hst => ℱ.mono (by have := S7FCF5B_clamp_mono T hst; linarith)
      le' := fun t => ℱ.le _ }
  have hM' : Martingale (fun t ω => M (a + S7FCF5B_clamp T t) ω - M a ω) ℱ' P := by
    refine ⟨fun t => ?_, fun i j hij => ?_⟩
    · exact (hM.1 (a + S7FCF5B_clamp T t)).sub
        ((hM.1 a).mono (ℱ.mono (le_add_of_nonneg_right (S7FCF5B_clamp_nonneg hT t))))
    · have hv : a + S7FCF5B_clamp T i ≤ a + S7FCF5B_clamp T j := by
        have := S7FCF5B_clamp_mono T hij
        linarith
      have hJ : Integrable (M (a + S7FCF5B_clamp T j)) P :=
        hint_v _ (by linarith [S7FCF5B_clamp_le T j])
      have hA : Integrable (M a) P := hint_v a (by linarith)
      have h1 : P[fun ω => M (a + S7FCF5B_clamp T j) ω - M a ω | ℱ' i] =ᵐ[P]
          P[M (a + S7FCF5B_clamp T j) | ℱ' i] - P[M a | ℱ' i] :=
        condExp_sub hJ hA _
      have h2 : P[M a | ℱ' i] = M a :=
        condExp_of_stronglyMeasurable (ℱ.le _)
          ((hM.1 a).mono (ℱ.mono (le_add_of_nonneg_right (S7FCF5B_clamp_nonneg hT i)))) hA
      have h3 : P[M (a + S7FCF5B_clamp T j) | ℱ' i] =ᵐ[P] M (a + S7FCF5B_clamp T i) :=
        hM.2 _ _ hv
      show P[fun ω => M (a + S7FCF5B_clamp T j) ω - M a ω | ℱ' i] =ᵐ[P]
        fun ω => M (a + S7FCF5B_clamp T i) ω - M a ω
      filter_upwards [h1, h3] with ω h1ω h3ω
      rw [h1ω, Pi.sub_apply, h3ω, h2]
  have hc' : ∀ᵐ ω ∂P, Continuous fun t => M (a + S7FCF5B_clamp T t) ω - M a ω := by
    filter_upwards [hc] with ω hω
    exact (hω.comp (continuous_const.add (S7FCF5B_clamp_cont T))).sub continuous_const
  have key : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M (a + S7FCF5B_clamp T t) ω - M a ω‖ₑ) ^ q ∂P ≤
      ENNReal.ofReal ((q / (q - 1)) ^ q) *
        ∫⁻ ω, ‖M (a + S7FCF5B_clamp T T) ω - M a ω‖ₑ ^ q ∂P :=
    HRS.MC.Sec7.S7FCW6.s7_FC_F4_doob_Lq_proof P ℱ' _ hM' hc' q hq hT
  have hsup : ∀ ω, (⨆ t ∈ Set.Icc a (a + T), ‖M t ω - M a ω‖ₑ) =
      ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M (a + S7FCF5B_clamp T t) ω - M a ω‖ₑ := by
    intro ω
    apply le_antisymm
    · refine iSup₂_le fun τ hτ => ?_
      have hmem : τ - a ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      refine le_iSup₂_of_le (τ - a) hmem ?_
      rw [S7FCF5B_clamp_of_mem hmem]
      simp
    · refine iSup₂_le fun t ht => ?_
      have hmem : a + t ∈ Set.Icc a (a + T) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      refine le_iSup₂_of_le (a + t) hmem ?_
      exact le_of_eq (by rw [S7FCF5B_clamp_of_mem ht])
  calc ∫⁻ ω, (⨆ t ∈ Set.Icc a (a + T), ‖M t ω - M a ω‖ₑ) ^ q ∂P
      = ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M (a + S7FCF5B_clamp T t) ω - M a ω‖ₑ) ^ q ∂P := by
        refine lintegral_congr fun ω => ?_
        rw [hsup ω]
    _ ≤ ENNReal.ofReal ((q / (q - 1)) ^ q) *
        ∫⁻ ω, ‖M (a + S7FCF5B_clamp T T) ω - M a ω‖ₑ ^ q ∂P := key
    _ = ENNReal.ofReal ((q / (q - 1)) ^ q) * ∫⁻ ω, ‖M (a + T) ω - M a ω‖ₑ ^ q ∂P := by
        rw [S7FCF5B_clamp_top hT]

end HRS.MC.Sec7.S7FCF5B

end
