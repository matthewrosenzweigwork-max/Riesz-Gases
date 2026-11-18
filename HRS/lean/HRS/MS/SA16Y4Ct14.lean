import HRS.MS.SA16Y4Ct13

/-!
# S.A.16 (SA16Y4) Ct14: localized Leibniz bound for a smooth compactly supported multiplier

`sa16y4_mul_loc_bound`: for `θ ∈ C_c^∞` with `tsupport θ ⊆ B(0,R₁)` there is `B' ≥ 0` with
`‖Jcc(θψ)‖ ≤ B' ∑_κ ‖1_{B(0,R₁)} (Jcc ψ)_κ‖_{L^p}` for every `ψ ∈ C_c^∞`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q Phase2SA16Evolution Phase2SA16Transfer

section Ct14
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16y4_mul_cc {θ : EuclideanSpace ℝ (Fin d) → ℝ} (hθ : ContDiff ℝ ∞ θ) {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : IsCcInfty ψ) : IsCcInfty (fun x => θ x * ψ x) := ⟨hθ.mul hψ.1, hψ.2.mul_left⟩

lemma sa16y4_comp_Jcc (k : ℕ) (ψ : ccSub d) (κ : WIndex d k) :
    sa16y4_comp k (sa16r_Jcc d k p ψ) κ =ᵐ[volume] partialDeriv κ.2 ψ.1 := by
  rw [sa16r_Jcc_eq]
  filter_upwards [sa16r_cc_elt_coe (p := p) ψ.2 k] with x hx
  exact congrFun hx κ

theorem sa16y4_mul_loc_bound (k : ℕ) {θ : EuclideanSpace ℝ (Fin d) → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hθc : HasCompactSupport θ) {R₁ : ℝ} (hsupp : tsupport θ ⊆ Metric.closedBall 0 R₁) :
    ∃ B' : ℝ, 0 ≤ B' ∧ ∀ ψ : ccSub d,
      ‖sa16r_Jcc d k p ⟨fun x => θ x * ψ.1 x, sa16y4_mul_cc hθ ψ.2⟩‖ ≤
        B' * ∑ κ : WIndex d k, sa16y4_loc k R₁ κ (sa16r_Jcc d k p ψ) := by
  have hp1r : 1 ≤ p := le_trans one_le_two (Fact.out : 2 ≤ p)
  have hp1 : (1 : ENNReal) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp1r
  have hbd : ∀ i : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ i θ x‖ ≤ C := fun i =>
    (hθ.continuous_iteratedFDeriv (m := i) (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hθc.iteratedFDeriv i)
  choose Cb hCb using hbd
  set B : ℝ := ∑ i ∈ Finset.range (k + 1), max (Cb i) 0 with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => le_max_right _ _
  have hBi : ∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i θ x‖ ≤ B := by
    intro i hi x
    calc ‖iteratedFDeriv ℝ i θ x‖ ≤ Cb i := hCb i x
      _ ≤ max (Cb i) 0 := le_max_left _ _
      _ ≤ B := Finset.single_le_sum (f := fun j => max (Cb j) 0) (fun j _ => le_max_right _ _)
        (Finset.mem_range.2 (by omega))
  refine ⟨B * ((d : ℝ) + 1) ^ k, by positivity, fun ψ => ?_⟩
  set K := Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R₁ with hK
  set B' : ℝ := B * ((d : ℝ) + 1) ^ k with hB'
  set f : WIndex d k → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun κ x => ‖K.indicator (sa16y4_comp k (sa16r_Jcc d k p ψ) κ) x‖ with hf
  have hae : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), ∀ κ : WIndex d k,
      sa16y4_comp k (sa16r_Jcc d k p ψ) κ x = partialDeriv κ.2 ψ.1 x :=
    ae_all_iff.2 fun κ => sa16y4_comp_Jcc k ψ κ
  have hpt : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      ‖wJet k (fun y => θ y * ψ.1 y) x‖ ≤ B' * ∑ κ : WIndex d k, f κ x := by
    filter_upwards [hae] with x hx
    by_cases hxK : x ∈ K
    · have h1 := sa16y_prod_jet_le hθ ψ.2.1 k x (fun i hi => hBi i hi x)
      have h2 : ‖wJet k ψ.1 x‖ ≤ ∑ κ : WIndex d k, f κ x := by
        refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)).2 fun τ => ?_
        refine le_trans ?_ (Finset.single_le_sum (f := fun κ : WIndex d k => f κ x)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ τ))
        simp only [hf, Set.indicator_of_mem hxK, hx τ]
        rfl
      calc ‖wJet k (fun y => θ y * ψ.1 y) x‖ ≤ B * ((d : ℝ) + 1) ^ k * ‖wJet k ψ.1 x‖ := h1
        _ ≤ B' * ∑ κ : WIndex d k, f κ x := mul_le_mul_of_nonneg_left h2 (by positivity)
    · have hnt : x ∉ tsupport θ := fun h => hxK (hsupp h)
      have h0 : ∀ i ≤ k, ‖iteratedFDeriv ℝ i θ x‖ ≤ 0 := fun i _ => by
        have : iteratedFDeriv ℝ i θ x = 0 := by
          by_contra h
          exact hnt (support_iteratedFDeriv_subset i (Function.mem_support.2 h))
        simp [this]
      have h1 := sa16y_prod_jet_le hθ ψ.2.1 k x h0
      have h3 : 0 ≤ B' * ∑ κ : WIndex d k, f κ x :=
        mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      have h4 : ‖wJet k (fun y => θ y * ψ.1 y) x‖ ≤ 0 := by simpa using h1
      exact h4.trans h3
  have hnorm := sa16y4_Jcc_norm' (p := p) k ⟨fun x => θ x * ψ.1 x, sa16y4_mul_cc hθ ψ.2⟩
  rw [hnorm]
  have hB'0 : 0 ≤ B' := by positivity
  have hmeas : AEStronglyMeasurable (fun x => ‖wJet k (fun y => θ y * ψ.1 y) x‖) volume :=
    (sa16j_jet_cont (sa16y4_mul_cc hθ ψ.2).1 k).norm.aestronglyMeasurable
  have h1 : eLpNorm (fun x => ‖wJet k (fun y => θ y * ψ.1 y) x‖) (ENNReal.ofReal p) volume ≤
      eLpNorm (fun x => B' * ∑ κ : WIndex d k, f κ x) (ENNReal.ofReal p) volume :=
    eLpNorm_mono_ae_real hmeas (hpt.mono fun x hx => by simpa using hx)
  have h2 : eLpNorm (fun x => B' * ∑ κ : WIndex d k, f κ x) (ENNReal.ofReal p) volume =
      ENNReal.ofReal B' * eLpNorm (∑ κ : WIndex d k, f κ) (ENNReal.ofReal p) volume := by
    rw [show (fun x => B' * ∑ κ : WIndex d k, f κ x) = B' • (∑ κ : WIndex d k, f κ) from by
      funext x; simp [Finset.sum_apply], eLpNorm_const_smul, Real.enorm_eq_ofReal hB'0]
  have h3 : eLpNorm (∑ κ : WIndex d k, f κ) (ENNReal.ofReal p) volume ≤
      ∑ κ : WIndex d k, eLpNorm (K.indicator (sa16y4_comp k (sa16r_Jcc d k p ψ) κ)) (ENNReal.ofReal p) volume := by
    refine (eLpNorm_sum_le hp1).trans (le_of_eq (Finset.sum_congr rfl fun κ _ => ?_))
    exact eLpNorm_norm _ ((sa16y4_comp_aesm k (sa16r_Jcc d k p ψ) κ).indicator measurableSet_closedBall)
  have hfin : ∀ κ ∈ (Finset.univ : Finset (WIndex d k)),
      eLpNorm (K.indicator (sa16y4_comp k (sa16r_Jcc d k p ψ) κ)) (ENNReal.ofReal p) volume ≠ ⊤ :=
    fun κ _ => sa16y4_loc_fin k R₁ κ _
  have hne : ENNReal.ofReal B' * ∑ κ : WIndex d k,
      eLpNorm (K.indicator (sa16y4_comp k (sa16r_Jcc d k p ψ) κ)) (ENNReal.ofReal p) volume ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.sum_ne_top.2 hfin)
  calc (eLpNorm (fun x => ‖wJet k (fun y => θ y * ψ.1 y) x‖) (ENNReal.ofReal p) volume).toReal
      ≤ (ENNReal.ofReal B' * ∑ κ : WIndex d k,
          eLpNorm (K.indicator (sa16y4_comp k (sa16r_Jcc d k p ψ) κ)) (ENNReal.ofReal p) volume).toReal :=
        ENNReal.toReal_mono hne (h1.trans (h2 ▸ mul_le_mul' le_rfl h3))
    _ = B' * ∑ κ : WIndex d k, sa16y4_loc k R₁ κ (sa16r_Jcc d k p ψ) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB'0, ENNReal.toReal_sum hfin]
        rfl
end Ct14

end HRS.Whole.AppendixA.Phase2SA16R
