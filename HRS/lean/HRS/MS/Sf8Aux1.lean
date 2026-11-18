import HRS.Whole.AppendixBKernel
import HRS.MS.FlowA
import HRS.MS.FlowDAux1

/-!
# MS-SF8II, geometry of the flow cells (route: `Sf8Plan.md`)

Bridge from the `Whole` drift/flow structures to `AppendixALemmas`, the bi-Lipschitz data of `Ψ τ` and its
(two-sided) inverse `Function.invFun (Ψ τ)`, `L²` mass of a cell, and the cell cover of a Euclidean ball:
`∫_{B(u,R)} w² ≤ (2LR+3)^d S²` if every flow cell carries `‖1_cell w‖₂ ≤ S`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MS.Sf8

open HRS.Whole

variable {d : ℕ}

theorem bridge_drift {m : ℕ} {Cb T : ℝ} {b : ℝ → Euc d → Euc d}
    (h : HRS.Whole.IsAdvectingDrift m Cb T b) :
    HRS.Whole.AppendixALemmas.IsDriftBounds T m Cb b where
  cont := h.cont
  smooth := fun τ hτ => by
    have := h.smooth τ hτ
    exact_mod_cast this
  deriv_bound := h.deriv_bdd
  growth := h.growth

theorem bridge_flow {T : ℝ} {b Ψ : ℝ → Euc d → Euc d} (h : HRS.Whole.IsNegDriftFlow T b Ψ) :
    HRS.Whole.AppendixALemmas.IsNegDriftFlow T b Ψ :=
  ⟨h.init, h.ode⟩

/-- Bi-Lipschitz data of `Ψ τ` with the inverse `Function.invFun (Ψ τ)`. -/
theorem flow_data {m : ℕ} {Cb T : ℝ} {b Ψ : ℝ → Euc d → Euc d}
    (hb : HRS.Whole.IsAdvectingDrift m Cb T b) (hΨ : HRS.Whole.IsNegDriftFlow T b Ψ) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) T) :
    0 ≤ Cb ∧ (∀ x y, ‖Ψ τ x - Ψ τ y‖ ≤ Real.exp (Cb * T) * ‖x - y‖) ∧
      (∀ y y', ‖Function.invFun (Ψ τ) y - Function.invFun (Ψ τ) y'‖ ≤
        Real.exp (Cb * T) * ‖y - y'‖) ∧
      (∀ x, Function.invFun (Ψ τ) (Ψ τ x) = x) ∧ (∀ y, Ψ τ (Function.invFun (Ψ τ) y) = y) := by
  have hT : 0 ≤ T := hτ.1.trans hτ.2
  have hCb : 0 ≤ Cb := (norm_nonneg _).trans (hb.deriv_bdd 0 ⟨le_rfl, hT⟩ 1 le_rfl (by omega) 0)
  have hb' := bridge_drift hb
  have hΨ' := bridge_flow hΨ
  have hexp : Real.exp (Cb * τ) ≤ Real.exp (Cb * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hτ.2 hCb)
  have hbij := hΨ.bij τ hτ
  have hΦΨ : ∀ x, Function.invFun (Ψ τ) (Ψ τ x) = x := Function.leftInverse_invFun hbij.1
  have hΨΦ : ∀ y, Ψ τ (Function.invFun (Ψ τ) y) = y := Function.rightInverse_invFun hbij.2
  refine ⟨hCb, fun x y => ?_, fun y y' => ?_, hΦΨ, hΨΦ⟩
  · exact (HRS.MS.FlowA.flow_lipschitz hT hb' hΨ' τ hτ x y).trans
      (mul_le_mul_of_nonneg_right hexp (norm_nonneg _))
  · obtain ⟨Φ, h1, h2, h3⟩ := HRS.MS.FlowA.flow_invertible hT hb' hΨ' τ hτ
    have e : ∀ y, Function.invFun (Ψ τ) y = Φ y := fun y => by
      calc Function.invFun (Ψ τ) y = Function.invFun (Ψ τ) (Ψ τ (Φ y)) := by rw [h2]
        _ = Φ y := hΦΨ _
    rw [e, e]
    exact (h3 y y').trans (mul_le_mul_of_nonneg_right hexp (norm_nonneg _))

theorem cube_eq (z : Fin d → ℤ) :
    {y : Euc d | ∀ i, 0 ≤ (y - latticePt z) i ∧ (y - latticePt z) i ≤ 1} =
      HRS.Whole.AppendixALemmas.latticeCell z := by
  ext y
  simp only [Set.mem_setOf_eq, HRS.Whole.AppendixALemmas.latticeCell, PiLp.sub_apply]
  constructor
  · intro h i; have := h i; exact ⟨by linarith [this.1], by linarith [this.2]⟩
  · intro h i; have := h i; exact ⟨by linarith [this.1], by linarith [this.2]⟩

theorem flowCell_eq (Ψ : ℝ → Euc d → Euc d) (τ : ℝ) (z : Fin d → ℤ) :
    flowCell Ψ τ z = Ψ τ '' HRS.Whole.AppendixALemmas.latticeCell z := by
  unfold flowCell
  rw [cube_eq]

theorem image_eq_preimage {f Φ : Euc d → Euc d} (h1 : ∀ x, Φ (f x) = x) (h2 : ∀ y, f (Φ y) = y)
    (A : Set (Euc d)) : f '' A = Φ ⁻¹' A := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    show Φ (f x) ∈ A
    rw [h1]; exact hx
  · intro h
    exact ⟨Φ y, h, h2 y⟩

theorem lip_continuous {Φ : Euc d → Euc d} {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ y y', ‖Φ y - Φ y'‖ ≤ L * ‖y - y'‖) : Continuous Φ :=
  (LipschitzWith.of_dist_le_mul (K := L.toNNReal) fun x y => by
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal L hL]; exact h x y).continuous

/-- `L²` mass of a measurable set from the `eLpNorm` of its indicator. -/
theorem cell_l2 {A : Set (Euc d)} (hA : MeasurableSet A) {w : Euc d → ℝ} (hw : Measurable w)
    {S : ℝ} (hS : 0 ≤ S) (h : eLpNorm (A.indicator w) 2 volume ≤ ENNReal.ofReal S) :
    ∫⁻ x in A, ENNReal.ofReal (w x ^ 2) ≤ ENNReal.ofReal (S ^ 2) := by
  have hf : AEStronglyMeasurable (A.indicator w) volume := (hw.indicator hA).aestronglyMeasurable
  have e1 := eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞)) (μ := volume)
    two_ne_zero ENNReal.ofNat_ne_top hf
  simp only [ENNReal.toReal_ofNat] at e1
  have e2 : ∫⁻ x, ‖A.indicator w x‖ₑ ^ (2 : ℝ) = (eLpNorm (A.indicator w) 2 volume) ^ (2 : ℝ) := by
    rw [e1, ← ENNReal.rpow_mul]
    norm_num
  have e3 : ∫⁻ x in A, ENNReal.ofReal (w x ^ 2) = ∫⁻ x, ‖A.indicator w x‖ₑ ^ (2 : ℝ) := by
    rw [← lintegral_indicator hA]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ A
    · simp only [Set.indicator_of_mem hx]
      rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
        Real.rpow_two, sq_abs]
    · simp [Set.indicator_of_notMem hx]
  rw [e3, e2]
  calc (eLpNorm (A.indicator w) 2 volume) ^ (2 : ℝ) ≤ (ENNReal.ofReal S) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = ENNReal.ofReal (S ^ 2) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hS (by norm_num), Real.rpow_two]

/-- The cell cover of a Euclidean ball. -/
theorem cell_cover {Ψτ Φ : Euc d → Euc d} {L : ℝ} (hL : 0 ≤ L) (hΦΨ : ∀ x, Φ (Ψτ x) = x)
    (hΨΦ : ∀ y, Ψτ (Φ y) = y) (hΦ : ∀ y y', ‖Φ y - Φ y'‖ ≤ L * ‖y - y'‖)
    {w : Euc d → ℝ} (hw : Measurable w) {S : ℝ} (hS : 0 ≤ S)
    (hcell : ∀ z' : Fin d → ℤ, eLpNorm ((Ψτ '' HRS.Whole.AppendixALemmas.latticeCell z').indicator w)
      2 volume ≤ ENNReal.ofReal S)
    (u : Euc d) {R : ℝ} (hR : 0 ≤ R) :
    ∫⁻ x in Metric.ball u R, ENNReal.ofReal (w x ^ 2) ≤
      ENNReal.ofReal ((2 * L * R + 3) ^ d * S ^ 2) := by
  have hΦc := lip_continuous hL hΦ
  have hmeas : ∀ k : Fin d → ℤ,
      MeasurableSet (Ψτ '' HRS.Whole.AppendixALemmas.latticeCell k) := by
    intro k
    rw [image_eq_preimage hΦΨ hΨΦ]
    exact ((HRS.MS.FlowD.isClosed_cell k).preimage hΦc).measurableSet
  have hLR : 0 ≤ L * R + 1 := by positivity
  obtain ⟨F, hF1, hF2⟩ := HRS.MS.FlowD.box_finset (fun i => (Φ u) i) (L * R + 1) hLR
  set g : Euc d → ℝ≥0∞ := fun x => ENNReal.ofReal (w x ^ 2) with hg
  have hgm : Measurable g := ENNReal.measurable_ofReal.comp (hw.pow_const 2)
  have hcov : ∀ x ∈ Metric.ball u R, ∃ k ∈ F, x ∈ Ψτ '' HRS.Whole.AppendixALemmas.latticeCell k := by
    intro x hx
    obtain ⟨k, hk⟩ := HRS.MS.FlowD.exists_cell (Φ x)
    refine ⟨k, hF1 k (fun i => ?_), ⟨Φ x, hk, hΨΦ x⟩⟩
    have hk' := (HRS.MS.FlowD.mem_cell_iff k (Φ x)).1 hk i
    have hxu : ‖x - u‖ < R := by rw [← dist_eq_norm]; exact hx
    have h1 : ‖Φ x - Φ u‖ ≤ L * R :=
      (hΦ x u).trans (mul_le_mul_of_nonneg_left hxu.le hL)
    have h2 : |(Φ x) i - (Φ u) i| ≤ L * R := by
      have := PiLp.norm_apply_le (Φ x - Φ u) i
      rw [PiLp.sub_apply, Real.norm_eq_abs] at this
      exact this.trans h1
    rw [abs_le] at h2 ⊢
    constructor <;> linarith [hk'.1, hk'.2, h2.1, h2.2]
  calc ∫⁻ x in Metric.ball u R, g x
      = ∫⁻ x, (Metric.ball u R).indicator g x := (lintegral_indicator measurableSet_ball g).symm
    _ ≤ ∫⁻ x, ∑ k ∈ F, (Ψτ '' HRS.Whole.AppendixALemmas.latticeCell k).indicator g x := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ Metric.ball u R
        · obtain ⟨k, hkF, hk⟩ := hcov x hx
          rw [Set.indicator_of_mem hx]
          calc g x = (Ψτ '' HRS.Whole.AppendixALemmas.latticeCell k).indicator g x :=
                (Set.indicator_of_mem hk g).symm
            _ ≤ _ := Finset.single_le_sum
                (f := fun k => (Ψτ '' HRS.Whole.AppendixALemmas.latticeCell k).indicator g x)
                (fun _ _ => zero_le) hkF
        · rw [Set.indicator_of_notMem hx]; exact zero_le
    _ = ∑ k ∈ F, ∫⁻ x in Ψτ '' HRS.Whole.AppendixALemmas.latticeCell k, g x := by
        rw [lintegral_finsetSum _ (fun k _ => hgm.indicator (hmeas k))]
        refine Finset.sum_congr rfl fun k _ => ?_
        exact lintegral_indicator (hmeas k) g
    _ ≤ ∑ _k ∈ F, ENNReal.ofReal (S ^ 2) :=
        Finset.sum_le_sum fun k _ => cell_l2 (hmeas k) hw hS (hcell k)
    _ = (F.card : ℝ≥0∞) * ENNReal.ofReal (S ^ 2) := by simp
    _ ≤ ENNReal.ofReal ((2 * L * R + 3) ^ d * S ^ 2) := by
        have hcard : (F.card : ℝ) ≤ (2 * L * R + 3) ^ d := by
          refine hF2.trans (le_of_eq ?_)
          congr 1; ring
        calc (F.card : ℝ≥0∞) * ENNReal.ofReal (S ^ 2)
            = ENNReal.ofReal (F.card * S ^ 2) := by
              rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
          _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard (sq_nonneg _))

end HRS.MS.Sf8
