import HRS.MS.SA16Y4Ct14

/-!
# S.A.16 (SA16Y4) Ct15: the multiplier operator `M_θ` on `WmpSpace`

`sa16y4_Mop`: for `θ ∈ C_c^∞` with `tsupport θ ⊆ B(0,R₁)` there is a CLM `M` on `W^{k,p}` with `M (Jcc ψ) = Jcc (θψ)` and the
localized bound `‖M Y‖ ≤ B' ∑_κ ‖1_{B(0,R₁)} Y_κ‖_{L^p}` (density from `sa16y4_mul_loc_bound`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q Phase2SA16Evolution Phase2SA16Transfer

section Ct15
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16y4_mul_mem {θ : EuclideanSpace ℝ (Fin d) → ℝ} (hθ : ContDiff ℝ ∞ θ) {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : IsCcInfty ψ) (k : ℕ) : (fun x => θ x * ψ x) ∈ sa16r_S d k p := by
  have hc := sa16y4_mul_cc hθ hψ
  exact ⟨hc.1, ⟨sa16r_Jcc d k p ⟨fun x => θ x * ψ x, hc⟩, by
    rw [sa16r_Jcc_eq]; exact sa16r_cc_elt_wrep (p := p) hc k⟩⟩

def sa16y4_Ml (k : ℕ) (p : ℝ) [Fact (2 ≤ p)] {θ : EuclideanSpace ℝ (Fin d) → ℝ} (hθ : ContDiff ℝ ∞ θ) :
    ccSub d →ₗ[ℝ] sa16r_S d k p where
  toFun ψ := ⟨fun x => θ x * ψ.1 x, sa16y4_mul_mem hθ ψ.2 k⟩
  map_add' ψ₁ ψ₂ := Subtype.ext (by funext x; simp [mul_add])
  map_smul' c ψ := Subtype.ext (by funext x; simp [mul_left_comm])

lemma sa16y4_Ml_eq (k : ℕ) {θ : EuclideanSpace ℝ (Fin d) → ℝ} (hθ : ContDiff ℝ ∞ θ) (ψ : ccSub d) :
    sa16r_J d k p (sa16y4_Ml k p hθ ψ) = sa16r_Jcc d k p ⟨fun x => θ x * ψ.1 x, sa16y4_mul_cc hθ ψ.2⟩ := by
  refine sa16r_wrep_inj d k p _ _ ?_
  have h2 : wrep d k p (sa16r_Jcc d k p ⟨fun x => θ x * ψ.1 x, sa16y4_mul_cc hθ ψ.2⟩) =ᵐ[volume]
      fun x => θ x * ψ.1 x := by
    rw [sa16r_Jcc_eq]
    exact sa16r_cc_elt_wrep (p := p) (sa16y4_mul_cc hθ ψ.2) k
  exact (sa16r_J_spec d k p (sa16y4_Ml k p hθ ψ)).trans h2.symm

theorem sa16y4_Mop (k : ℕ) {θ : EuclideanSpace ℝ (Fin d) → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hθc : HasCompactSupport θ) {R₁ : ℝ} (hsupp : tsupport θ ⊆ Metric.closedBall 0 R₁) :
    ∃ (M : WmpSpace d k p →L[ℝ] WmpSpace d k p) (B' : ℝ), 0 ≤ B' ∧
      (∀ ψ : ccSub d, M (sa16r_Jcc d k p ψ) = sa16r_Jcc d k p ⟨fun x => θ x * ψ.1 x, sa16y4_mul_cc hθ ψ.2⟩) ∧
      ∀ Y : WmpSpace d k p, ‖M Y‖ ≤ B' * ∑ κ : WIndex d k, sa16y4_loc k R₁ κ Y := by
  obtain ⟨B', hB'0, hB'⟩ := sa16y4_mul_loc_bound (p := p) k hθ hθc hsupp
  have hc0 : 0 ≤ B' * (Fintype.card (WIndex d k) : ℝ) := by positivity
  have hb : ∀ ψ : ccSub d, ‖sa16r_J d k p (sa16y4_Ml k p hθ ψ)‖ ≤
      B' * (Fintype.card (WIndex d k) : ℝ) * ‖sa16r_Jcc d k p ψ‖ := by
    intro ψ
    rw [sa16y4_Ml_eq]
    refine (hB' ψ).trans ?_
    have : ∑ κ : WIndex d k, sa16y4_loc k R₁ κ (sa16r_Jcc d k p ψ) ≤
        (Fintype.card (WIndex d k) : ℝ) * ‖sa16r_Jcc d k p ψ‖ := by
      calc ∑ κ : WIndex d k, sa16y4_loc k R₁ κ (sa16r_Jcc d k p ψ)
          ≤ ∑ κ : WIndex d k, ‖sa16r_Jcc d k p ψ‖ := Finset.sum_le_sum fun κ _ => sa16y4_loc_le_norm k R₁ κ _
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    nlinarith [this, hB'0]
  obtain ⟨M, -, hM2, -⟩ := sa16r_extend_cc d k k p (sa16y4_Ml k p hθ) hc0 hb
  have hMs : ∀ ψ : ccSub d, M (sa16r_Jcc d k p ψ) =
      sa16r_Jcc d k p ⟨fun x => θ x * ψ.1 x, sa16y4_mul_cc hθ ψ.2⟩ := fun ψ => by rw [hM2 ψ, sa16y4_Ml_eq]
  refine ⟨M, B', hB'0, hMs, fun Y => ?_⟩
  refine (sa16r_Jcc_dense d k p).induction_on Y (isClosed_le ?_ ?_) (fun ψ => ?_)
  · exact M.continuous.norm
  · exact continuous_const.mul (continuous_finset_sum _ fun κ _ => sa16y4_loc_cont k R₁ κ)
  · rw [hMs ψ]; exact hB' ψ
end Ct15

end HRS.Whole.AppendixA.Phase2SA16R
