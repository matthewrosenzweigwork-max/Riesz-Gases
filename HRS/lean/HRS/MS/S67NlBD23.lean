import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovThermAux2
import HRS.MS.S67NlBD05
import HRS.MS.S67NlBD44

/-!
# S6.7nl.23: far Gaussian output from `L¹` data and bounded kernel jets
Source pin `b66ab61cf3f03a9c6f5a899ef5de61f2b34c5e44`.

The convolution `κ * h` of a bounded-jet kernel with an `L¹` source is `C^N` with
`‖D^k (κ * h)‖ ≤ K ‖h‖₁` (the merged generic lemma `s67bd_conv_cb`, differentiation under the
integral with the `L¹` dominator `K |h|`).  Multiplying by `√ρ₀` (Gaussian derivative bounds,
Leibniz) gives a Gaussian envelope of amplitude `C ‖h‖₁` for every jet of order `≤ N`; packet 05
gives integer oscillator membership and `mo_mono` lowers the level to `r ≤ N`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

/-- Leibniz bound through order `N` for a product with a Gaussian-bounded factor. -/
theorem s67bd_far_prod_jet (N : ℕ) {w g : Euc d → ℝ} (hw : ContDiff ℝ (N : WithTop ℕ∞) w)
    (hg : ContDiff ℝ (N : WithTop ℕ∞) g) {c Cw G : ℝ} (hCw : 0 ≤ Cw)
    (hwb : ∀ k ≤ N, ∀ x, ‖iteratedFDeriv ℝ k w x‖ ≤ Cw * Real.exp (-c * ‖x‖ ^ 2))
    (hgb : ∀ k ≤ N, ∀ x, ‖iteratedFDeriv ℝ k g x‖ ≤ G) (k : ℕ) (hk : k ≤ N) (x : Euc d) :
    ‖iteratedFDeriv ℝ k (fun y => w y * g y) x‖ ≤ 2 ^ N * Cw * G * Real.exp (-c * ‖x‖ ^ 2) := by
  have hG : 0 ≤ G := (norm_nonneg _).trans (hgb 0 (Nat.zero_le _) x)
  have h1 := norm_iteratedFDeriv_mul_le hw hg x (n := k) (by exact_mod_cast hk)
  refine h1.trans ?_
  have hE := (Real.exp_pos (-c * ‖x‖ ^ 2)).le
  have hterm : ∀ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i w x‖ *
      ‖iteratedFDeriv ℝ (k - i) g x‖ ≤ (k.choose i : ℝ) * (Cw * G * Real.exp (-c * ‖x‖ ^ 2)) := by
    intro i hi
    have hik : i ≤ N := by have := Finset.mem_range.1 hi; omega
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    calc ‖iteratedFDeriv ℝ i w x‖ * ‖iteratedFDeriv ℝ (k - i) g x‖
        ≤ (Cw * Real.exp (-c * ‖x‖ ^ 2)) * G :=
          mul_le_mul (hwb i hik x) (hgb (k - i) (by omega) x) (norm_nonneg _)
            (mul_nonneg hCw hE)
      _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  have hsum : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) = 2 ^ k := by
    exact_mod_cast Nat.sum_range_choose k
  rw [← Finset.sum_mul, hsum]
  have hX : 0 ≤ Cw * G * Real.exp (-c * ‖x‖ ^ 2) := mul_nonneg (mul_nonneg hCw hG) hE
  have h2k : (2 : ℝ) ^ k ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hk
  calc (2 : ℝ) ^ k * (Cw * G * Real.exp (-c * ‖x‖ ^ 2))
      ≤ 2 ^ N * (Cw * G * Real.exp (-c * ‖x‖ ^ 2)) := mul_le_mul_of_nonneg_right h2k hX
    _ = _ := by ring

theorem s67bd_far_gaussian_output (H : Mov2dTh d s β q ρ₀)
    (r : ℝ) (hr : 0 ≤ r) (N : ℕ) (hrN : r ≤ N) (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ κ : Euc d → ℝ, ContDiff ℝ (N : WithTop ℕ∞) κ →
      (∀ k ≤ N, ∀ x, ‖iteratedFDeriv ℝ k κ x‖ ≤ K) →
      ∀ h : Euc d → ℝ, Integrable h volume →
      (∀ x : Euc d, Integrable (fun y => κ (x - y) * h y) volume) ∧
      MemOsc r (fun x => Real.sqrt (ρ₀ x) * ∫ y, κ (x - y) * h y) ∧
      oscNorm r (fun x => Real.sqrt (ρ₀ x) * ∫ y, κ (x - y) * h y) ≤
        C * ∫ x, |h x| := by
  obtain ⟨hws, -, c, hc, hk⟩ :=
    HRS.MS.Mov0.mv0_sqrt_gauss_thermal H.hd H.hs0 H.hsd H.hq H.hβ H.hρ
  choose Ck hCk using hk
  obtain ⟨Cosc, hCosc0, hCosc⟩ := s67bd_gaussian_osc d N c hc
  set Cw : ℝ := ∑ k ∈ Finset.range (N + 1), |Ck k| with hCwdef
  have hCw0 : 0 ≤ Cw := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hwb : ∀ k ≤ N, ∀ x, ‖iteratedFDeriv ℝ k (fun y => Real.sqrt (ρ₀ y)) x‖ ≤
      Cw * Real.exp (-c * ‖x‖ ^ 2) := by
    intro k hk x
    have hle : |Ck k| ≤ Cw :=
      Finset.single_le_sum (f := fun k => |Ck k|) (fun k _ => abs_nonneg _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
    exact (hCk k x).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans hle)
      (Real.exp_pos _).le)
  have hw : ContDiff ℝ (N : WithTop ℕ∞) (fun y => Real.sqrt (ρ₀ y)) := hws.of_le (by simp)
  refine ⟨Cosc * (2 ^ N * Cw * K), by positivity, fun κ hκ hb h hh => ?_⟩
  have hκc : Continuous κ := hκ.continuous
  have hb0 : ∀ z, ‖κ z‖ ≤ K := fun z => by simpa using hb 0 (Nat.zero_le _) z
  have hhI : Integrable (fun y => |h y|) volume := by simpa [Real.norm_eq_abs] using hh.norm
  have hint : ∀ x : Euc d, Integrable (fun y => κ (x - y) * h y) volume := by
    intro x
    refine Integrable.mono' (hhI.const_mul K)
      ((hκc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul
        hh.aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
    rw [norm_mul, Real.norm_eq_abs (κ (x - y)), Real.norm_eq_abs (h y)]
    exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hb0 (x - y)) (abs_nonneg _)
  obtain ⟨hcd, hjb⟩ := s67bd_conv_cb N ℝ κ K h hκ hb hh
  have hu : ∀ x, ∫ y, κ (x - y) * h y = ∫ y, h y • κ (x - y) := by
    intro x
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp [mul_comm]
  simp only [hu]
  refine ⟨hint, ?_⟩
  set I : ℝ := ∫ x, |h x| with hI
  have hI0 : 0 ≤ I := integral_nonneg fun x => abs_nonneg _
  have hA0 : 0 ≤ 2 ^ N * Cw * K * I := by positivity
  have hψb : ∀ k ≤ N, ∀ x, ‖iteratedFDeriv ℝ k
      (fun x => Real.sqrt (ρ₀ x) * ∫ y, h y • κ (x - y)) x‖ ≤
      (2 ^ N * Cw * K * I) * Real.exp (-c * ‖x‖ ^ 2) := by
    intro k hk x
    have := s67bd_far_prod_jet N hw hcd hCw0 hwb hjb k hk x
    calc _ ≤ _ := this
      _ = _ := by ring
  obtain ⟨hmo, hno⟩ := hCosc (2 ^ N * Cw * K * I) hA0 _ (hw.mul hcd) hψb
  obtain ⟨hm1, hm2⟩ := mo_mono hrN hmo
  refine ⟨hm1, hm2.trans (hno.trans ?_)⟩
  nlinarith [mul_nonneg hCosc0 hI0]

end HRS.MS.BreakdownS67
