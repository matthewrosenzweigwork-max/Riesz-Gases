import HRS.MS.SA12X5Defs
import HRS.MS.SA12X3C7A
import HRS.MS.SA12X3C7C17
import HRS.MS.SA12X2R36S4

/-!
# S.A.12 X5 N2: derivatives of a convolution with a locally integrable kernel; Young `L¹_loc * L²`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3 HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Near

variable {d : ℕ}

/-- `∂^{idx}` of the convolution with a locally integrable kernel. -/
theorem sa12x5_pd_convFun {K : Euc d → ℝ} (hK : LocallyIntegrable K (volume : Measure (Euc d))) :
    ∀ (n : ℕ) (Q : Euc d → ℝ), ContDiff ℝ n Q → HasCompactSupport Q → ∀ (idx : Fin n → Fin d) (x : Euc d),
      partialDeriv idx (HRS.Whole.convFun (K) Q) x =
        HRS.Whole.convFun (K) (partialDeriv idx Q) x := by
  have hfun : ∀ Q : Euc d → ℝ, HRS.Whole.convFun (K) Q =
      K ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] Q := by
    intro Q
    funext x'
    have h := integral_sub_left_eq_self (μ := volume) (fun t => K t * Q (x' - t)) x'
    simp only [sub_sub_cancel] at h
    simpa [convolution_def, HRS.Whole.convFun] using h
  have hcd : ∀ (n : ℕ) (Q : Euc d → ℝ), ContDiff ℝ n Q → HasCompactSupport Q →
      ContDiff ℝ n (HRS.Whole.convFun (K) Q) := by
    intro n Q hQ hQc
    rw [hfun]
    exact hQc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hK hQ
  intro n
  induction n with
  | zero =>
    intro Q hQ hQc idx x
    simp only [sa12z3_pd_zero_fun]
  | succ n ih =>
    intro Q hQ hQc idx x
    obtain ⟨i, idx', rfl⟩ : ∃ i idx', idx = (Fin.cons i idx' : Fin (n + 1) → Fin d) :=
      ⟨idx 0, Fin.tail idx, (Fin.cons_self_tail idx).symm⟩
    have hQn : ContDiff ℝ n Q := hQ.of_le (by exact_mod_cast Nat.le_succ n)
    have e1 : partialDeriv (Fin.cons i idx' : Fin (n + 1) → Fin d) (HRS.Whole.convFun (K) Q) x =
        D1 i (partialDeriv idx' (HRS.Whole.convFun (K) Q)) x :=
      sa12z3_pd_cons idx' i (hcd (n + 1) Q hQ hQc) x
    have e2 : D1 i (partialDeriv idx' (HRS.Whole.convFun (K) Q)) =
        D1 i (HRS.Whole.convFun (K) (partialDeriv idx' Q)) :=
      congrArg (D1 i) (funext fun y => ih Q hQn hQc idx' y)
    have hPQ : ContDiff ℝ 1 (partialDeriv idx' Q) := by
      have := sa12z3_pd_contDiff (k := n + 1) (n := n) hQ (by omega) idx'
      simpa using this
    have e3 : D1 i (HRS.Whole.convFun (K) (partialDeriv idx' Q)) x =
        HRS.Whole.convFun (K) (D1 i (partialDeriv idx' Q)) x :=
      convFun_D1 hK hPQ (sa12z3_pd_compact hQc idx') i x
    have e4 : partialDeriv (Fin.cons i idx' : Fin (n + 1) → Fin d) Q x = D1 i (partialDeriv idx' Q) x :=
      sa12z3_pd_cons idx' i hQ x
    rw [e1, e2, e3]
    unfold HRS.Whole.convFun
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [sa12z3_pd_cons idx' i hQ y]


theorem sa12x5_young_loc {K : Euc d → ℝ} (hKm : Measurable K) {ρ CK : ℝ}
    (hKi : IntegrableOn K (closedBall (0 : Euc d) ρ))
    (hCK : ∫ u in closedBall (0 : Euc d) ρ, |K u| ≤ CK)
    {c : Euc d} {R R' : ℝ} (hρ : R + R' ≤ ρ) {v w : Euc d → ℝ} (hv : Continuous v)
    (hvs : HasCompactSupport v) (hvsupp : Function.support v ⊆ closedBall c R')
    (hTm : AEStronglyMeasurable (fun x => ∫ y, K (x - y) * v y) volume)
    (hw : Continuous w) (hws : Function.support w ⊆ closedBall c R) (hw1 : ∀ x, |w x| ≤ 1) :
    ∫ x, (w x * ∫ y, K (x - y) * v y) ^ 2 ≤ CK ^ 2 * ∫ y, v y ^ 2 := by
  set T : Euc d → ℝ := fun x => ∫ y, K (x - y) * v y with hT
  set k : Euc d → ℝ≥0∞ := (closedBall (0 : Euc d) ρ).indicator (fun u => ENNReal.ofReal |K u|) with hk
  have hkm : Measurable k := (hKm.abs.ennreal_ofReal).indicator measurableSet_closedBall
  have hkI : ∫⁻ u, k u = ENNReal.ofReal (∫ u in closedBall (0 : Euc d) ρ, |K u|) := by
    rw [hk, lintegral_indicator measurableSet_closedBall]
    rw [ofReal_integral_eq_lintegral_ofReal hKi.abs (Eventually.of_forall fun u => abs_nonneg _)]
  have hk1 : ∫⁻ u, k u ≠ ⊤ := by rw [hkI]; exact ENNReal.ofReal_ne_top
  have hv2 : Integrable (fun y => v y ^ 2) := by
    refine Continuous.integrable_of_hasCompactSupport (hv.pow 2) ?_
    exact hvs.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
  set f : Euc d → ℝ≥0∞ := fun y => ‖v y‖ₑ with hf
  have hfm : Measurable f := hv.measurable.enorm
  have hYoung := HRS.MH.Screened.young_l1_l2_proof k f hkm hfm hk1
  set G : Euc d → ℝ≥0∞ := fun x => ∫⁻ y, k (x - y) * f y with hG
  have hpt : ∀ x, ENNReal.ofReal ((w x * T x) ^ 2) ≤ G x ^ 2 := by
    intro x
    by_cases hwx : w x = 0
    · simp [hwx]
    · have hxB : x ∈ closedBall c R := hws (Function.mem_support.2 hwx)
      have h1 : ‖T x‖ₑ ≤ G x := by
        refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun y => ?_)
        by_cases hv0 : v y = 0
        · simp [hv0]
        · have hyB : y ∈ closedBall c R' := hvsupp (Function.mem_support.2 hv0)
          have hxy : ‖x - y‖ ≤ ρ := by
            rw [← dist_eq_norm]
            have := dist_triangle_right x y c
            have h2 := mem_closedBall.1 hxB
            have h3 := mem_closedBall.1 hyB
            linarith [dist_comm y c]
          have hmem : x - y ∈ closedBall (0 : Euc d) ρ := mem_closedBall_zero_iff.2 hxy
          simp only [hk, hf, Set.indicator_of_mem hmem, enorm_mul]
          rw [Real.enorm_eq_ofReal_abs]
      have h2 : ‖w x * T x‖ₑ ≤ ‖T x‖ₑ := by
        rw [enorm_mul]
        calc ‖w x‖ₑ * ‖T x‖ₑ ≤ 1 * ‖T x‖ₑ := by
              gcongr
              rw [Real.enorm_eq_ofReal_abs]; simpa using ENNReal.ofReal_le_ofReal (hw1 x)
          _ = _ := one_mul _
      have h3 : ENNReal.ofReal ((w x * T x) ^ 2) = ‖w x * T x‖ₑ ^ 2 := by
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
      rw [h3]
      exact pow_le_pow_left₀ (by positivity) (h2.trans h1) 2
  have hlhs : ∫ x, (w x * T x) ^ 2 = (∫⁻ x, ENNReal.ofReal ((w x * T x) ^ 2)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg _)
      ((hw.aestronglyMeasurable.mul hTm).pow 2)
  have hrhs : ∫⁻ y, f y ^ 2 = ENNReal.ofReal (∫ y, v y ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hv2 (Eventually.of_forall fun y => sq_nonneg _)]
    refine lintegral_congr fun y => ?_
    rw [hf]; simp only
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  have hle : ∫⁻ x, ENNReal.ofReal ((w x * T x) ^ 2) ≤
      ENNReal.ofReal (CK ^ 2 * ∫ y, v y ^ 2) := by
    calc ∫⁻ x, ENNReal.ofReal ((w x * T x) ^ 2) ≤ ∫⁻ x, G x ^ 2 := lintegral_mono hpt
      _ ≤ (∫⁻ u, k u) ^ 2 * ∫⁻ y, f y ^ 2 := hYoung
      _ = ENNReal.ofReal ((∫ u in closedBall (0 : Euc d) ρ, |K u|) ^ 2 * ∫ y, v y ^ 2) := by
          rw [hkI, hrhs, ← ENNReal.ofReal_pow (integral_nonneg fun u => abs_nonneg _),
            ← ENNReal.ofReal_mul (sq_nonneg _)]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (integral_nonneg fun y => sq_nonneg _))
          exact pow_le_pow_left₀ (integral_nonneg fun u => abs_nonneg _) hCK 2
  rw [hlhs]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hle

end HRS.MH.AdjointRd.Phase2SA12X5
