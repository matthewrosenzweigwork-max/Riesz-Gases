import HRS.MS.MovLinAux19
import HRS.Whole.Moving

/-!
# S6.2 `mov_linear`: assembly and tie

Namespace `HRS.MS.MovLin`, helpers `movlin_`.

`mov_linear_proof : type_of% @HRS.Whole.mov_linear`.  Existence of `T` with `MovIsSemigroup` is `mov2d_isSemigroup`
(global Volterra flow on the scale `OscSpace d r`, transported to `L²_0`); uniqueness at every `t ≥ 0` is `mov2d_uniq_core`
(Schwartz core) plus the density of the core `mov2d_dense_core` (`movlin_uniq`); the decay rate `c = λ` is the `L²`-decay of
`T` on `L²_0` (`movlin_L2_decay`, from `mov2e_decay` and density); the two bounds of `MovSmoothingBounds` follow from
`movlin_abstract` (`L²` decay + short-time smoothing with arbitrary loss + the semigroup law) for `T` (`movlin_Hs_T`, from
`movlin_smooth`) and for the `L²_0`-adjoint (`movlin_Hs_adj`, by duality on the scale; the projection onto `L²_0` costs the
rank-one term `κ e₁`).
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.MS.MovLin

open HRS HRS.Whole

local notation "𝓢R" => SchwartzMap (Euc _) ℝ

lemma movlin_smoothing_mono {d : ℕ} {s : ℝ} {ρ : Euc d → ℝ} {m c C C' : ℝ}
    {U : ℝ → (MovL2Zero ρ →L[ℝ] MovL2Zero ρ)} (h : C ≤ C') (hb : MovSmoothingBounds d s ρ m c C U) :
    MovSmoothingBounds d s ρ m c C' U := by
  obtain ⟨h1, h2⟩ := hb
  have hnn : ∀ (r : ℝ) (f : Euc d → ℝ), 0 ≤ oscNorm r f := HRS.MS.MovC1.movc1_osc_nonneg
  refine ⟨fun t ht v hv => ?_, fun t ht v hv => ?_⟩
  · obtain ⟨hm, hn⟩ := h1 t ht v hv
    exact ⟨hm, hn.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h (Real.exp_pos _).le) (hnn _ _))⟩
  · obtain ⟨hm, hn⟩ := h2 t ht v hv
    refine ⟨hm, hn.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h (by have := Real.rpow_nonneg ht.le (-(movA d s) / 2); linarith))
      (Real.exp_pos _).le) (hnn _ _))⟩

lemma movlin_adjoint_one {d : ℕ} {ρ : Euc d → ℝ} :
    ContinuousLinearMap.adjoint (1 : MovL2Zero ρ →L[ℝ] MovL2Zero ρ) = 1 :=
  ContinuousLinearMap.adjoint_one

lemma movlin_adjoint_mul {d : ℕ} {ρ : Euc d → ℝ} (A B : MovL2Zero ρ →L[ℝ] MovL2Zero ρ) :
    ContinuousLinearMap.adjoint (A * B) = ContinuousLinearMap.adjoint B * ContinuousLinearMap.adjoint A :=
  ContinuousLinearMap.adjoint_comp _ _

lemma movlin_adjoint_dec {d : ℕ} {ρ : Euc d → ℝ} {A : MovL2Zero ρ →L[ℝ] MovL2Zero ρ} {K : ℝ}
    (hA : ‖A‖ ≤ K) (v : MovL2Zero ρ) : ‖ContinuousLinearMap.adjoint A v‖ ≤ K * ‖v‖ := by
  have h1 : ‖ContinuousLinearMap.adjoint A‖ = ‖A‖ := LinearIsometryEquiv.norm_map _ _
  have h2 : ‖ContinuousLinearMap.adjoint A‖ ≤ K := by rw [h1]; exact hA
  exact ((ContinuousLinearMap.adjoint A).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))

section Parts

variable {d : ℕ} {s : ℝ} {β q : ℝ} {ρ : Euc d → ℝ}

set_option maxHeartbeats 1600000 in
lemma movlin_part_T (H : Mov2dTh d s β q ρ) (ψ0 : SchwartzMap (Euc d) ℝ)
    (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x)) (lam C0 : ℝ) (hlam : 0 < lam) (hC0 : 1 ≤ C0)
    (hdec : ∀ t : ℝ, 0 ≤ t → ∀ v : MovL2Zero ρ,
      ‖mov2d_T H ψ0 hψ0 t v‖ ≤ C0 * Real.exp (-lam * t) * ‖v‖) {m : ℝ} (hm : movA d s ≤ m) :
    ∃ C : ℝ, MovSmoothingBounds d s ρ m lam C (mov2d_T H ψ0 hψ0) :=
  movlin_abstract s (mov2d_T H ψ0 hψ0) lam C0 hlam hC0 (mov2d_isSemigroup H ψ0 hψ0).zero
    (mov2d_isSemigroup H ψ0 hψ0).add hdec (movlin_Hs_T H ψ0 hψ0) hm

set_option maxHeartbeats 1600000 in
lemma movlin_part_adj (H : Mov2dTh d s β q ρ) (ψ0 : SchwartzMap (Euc d) ℝ)
    (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x)) (lam C0 : ℝ) (hlam : 0 < lam) (hC0 : 1 ≤ C0)
    (hdec : ∀ t : ℝ, 0 ≤ t → ∀ v : MovL2Zero ρ,
      ‖mov2d_T H ψ0 hψ0 t v‖ ≤ C0 * Real.exp (-lam * t) * ‖v‖) {m : ℝ} (hm : movA d s ≤ m) :
    ∃ C : ℝ, MovSmoothingBounds d s ρ m lam C (fun t => ContinuousLinearMap.adjoint (mov2d_T H ψ0 hψ0 t)) := by
  have hTs := mov2d_isSemigroup H ψ0 hψ0
  have hU0 : ContinuousLinearMap.adjoint (mov2d_T H ψ0 hψ0 0) = 1 :=
    (congrArg ContinuousLinearMap.adjoint hTs.zero).trans movlin_adjoint_one
  have hUadd : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      ContinuousLinearMap.adjoint (mov2d_T H ψ0 hψ0 (a + b)) =
        ContinuousLinearMap.adjoint (mov2d_T H ψ0 hψ0 a) * ContinuousLinearMap.adjoint (mov2d_T H ψ0 hψ0 b) := by
    intro a b ha hb
    have e2 : mov2d_T H ψ0 hψ0 (a + b) = mov2d_T H ψ0 hψ0 b * mov2d_T H ψ0 hψ0 a := by
      rw [add_comm]; exact hTs.add b a hb ha
    exact (congrArg ContinuousLinearMap.adjoint e2).trans (movlin_adjoint_mul _ _)
  have hUdec : ∀ t : ℝ, 0 ≤ t → ∀ v : MovL2Zero ρ,
      ‖ContinuousLinearMap.adjoint (mov2d_T H ψ0 hψ0 t) v‖ ≤ C0 * Real.exp (-lam * t) * ‖v‖ := by
    intro t ht v
    have hop : ‖mov2d_T H ψ0 hψ0 t‖ ≤ C0 * Real.exp (-lam * t) :=
      ContinuousLinearMap.opNorm_le_bound _ (by positivity) (hdec t ht)
    exact movlin_adjoint_dec hop v
  exact movlin_abstract s (fun t => ContinuousLinearMap.adjoint (mov2d_T H ψ0 hψ0 t)) lam C0 hlam hC0
    hU0 hUadd hUdec (movlin_Hs_adj H ψ0 hψ0) hm

set_option maxHeartbeats 1600000 in
lemma movlin_part_both (H : Mov2dTh d s β q ρ) (ψ0 : SchwartzMap (Euc d) ℝ)
    (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x)) (lam C0 : ℝ) (hlam : 0 < lam) (hC0 : 1 ≤ C0)
    (hdec : ∀ t : ℝ, 0 ≤ t → ∀ v : MovL2Zero ρ,
      ‖mov2d_T H ψ0 hψ0 t v‖ ≤ C0 * Real.exp (-lam * t) * ‖v‖) {m : ℝ} (hm : movA d s ≤ m) :
    ∃ C : ℝ, MovSmoothingBounds d s ρ m lam C (mov2d_T H ψ0 hψ0) ∧
      MovSmoothingBounds d s ρ m lam C (fun t => ContinuousLinearMap.adjoint (mov2d_T H ψ0 hψ0 t)) :=
  ⟨max (movlin_part_T H ψ0 hψ0 lam C0 hlam hC0 hdec hm).choose
      (movlin_part_adj H ψ0 hψ0 lam C0 hlam hC0 hdec hm).choose,
    movlin_smoothing_mono (le_max_left _ _) (movlin_part_T H ψ0 hψ0 lam C0 hlam hC0 hdec hm).choose_spec,
    movlin_smoothing_mono (le_max_right _ _) (movlin_part_adj H ψ0 hψ0 lam C0 hlam hC0 hdec hm).choose_spec⟩

end Parts

set_option maxHeartbeats 1600000 in
theorem mov_linear_proof {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β)
    (hq : 0 < q) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ) :
    ∃ T : ℝ → (MovL2Zero ρ →L[ℝ] MovL2Zero ρ), MovIsSemigroup d s β ρ T ∧
      (∀ T' : ℝ → (MovL2Zero ρ →L[ℝ] MovL2Zero ρ), MovIsSemigroup d s β ρ T' →
        ∀ t : ℝ, 0 ≤ t → T' t = T t) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ m : ℝ, movA d s ≤ m → ∃ C : ℝ,
        MovSmoothingBounds d s ρ m c C T ∧
        MovSmoothingBounds d s ρ m c C (fun t => ContinuousLinearMap.adjoint (T t)) := by
  have H : Mov2dTh d s β q ρ := ⟨hd, hs0, hsd, hβ, hq, hρ⟩
  obtain ⟨ψ0, hψ0⟩ := mov2d_sqrt_schwartz H
  obtain ⟨lam, hlam, C0, hC0, hdec⟩ := movlin_L2_decay H ψ0 hψ0
  refine ⟨mov2d_T H ψ0 hψ0, mov2d_isSemigroup H ψ0 hψ0, fun T' hT' t ht => movlin_uniq H ψ0 hψ0 hT' ht,
    lam, hlam, fun m hm => ?_⟩
  exact movlin_part_both H ψ0 hψ0 lam C0 hlam hC0 hdec hm

end HRS.MS.MovLin

example := (@HRS.MS.MovLin.mov_linear_proof : type_of% @HRS.Whole.mov_linear)
