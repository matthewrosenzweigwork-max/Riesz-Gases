import HRS.MS.R26T8AP29h
import HRS.MS.R26T8AW1
import HRS.MS.R26T8AP08b
import HRS.MS.R26T8AP10a13

/-!
# S8.2 T8A P29 (part i): pointwise pole bound of `pairJ` for a conormal kernel
Exact statement: for `Q ∈ Conormal 4 1 M (s-2) A` (`s = criticalS d`), `|pairJ Q x y| ≤ C A pairWeight (M+2) x y (1 + r^(-s))`.
Route: the two halves of `pairJ` are `G x y` and `G' y x` with `G` of `r26t8a_p11_Px_same` (k = 2, b = 0, sigma = s, so
`G ∈ Conormal 2 2 (M+2) 0`), the jet `(0,0)` of a conormal kernel, and `r26t8a_p29_logsq`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_p29_conormal_value {k b : ℕ} {M σ A : ℝ} {G : Euc d → Euc d → ℝ}
    (hG : Conormal k b M σ A G) (x y : Euc d) (hxy : x ≠ y) :
    |G x y| ≤ A * Phase2S82.pairWeight M x y *
      (1 + (min 1 ‖x - y‖) ^ (-(σ + ((0 : ℕ) : ℝ))) * (1 + |Real.log (min 1 ‖x - y‖)|) ^ b) := by
  have hz : x - y ≠ 0 := sub_ne_zero.2 hxy
  have h := hG.2 0 0 (by omega) ((1 / 2 : ℝ) • (x + y)) (x - y) hz
  have e1 : (1 / 2 : ℝ) • (x + y) + (1 / 2 : ℝ) • (x - y) = x := by
    module
  have e2 : (1 / 2 : ℝ) • (x + y) - (1 / 2 : ℝ) • (x - y) = y := by
    module
  rw [e1, e2] at h
  have e3 : ‖mixedJet 0 0 G ((1 / 2 : ℝ) • (x + y)) (x - y)‖ = |G x y| := by
    simp only [mixedJet, norm_iteratedFDeriv_zero, midPair, e1, e2, Real.norm_eq_abs]
  rwa [e3] at h

theorem r26t8a_p29_pairJ_bound (d : ℕ) (hd : 2 ≤ d) (a beta M : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ Q : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A → Conormal 4 1 M (criticalS d - 2) A Q →
      ∀ x y : Euc d, x ≠ y →
        |pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q x y| ≤
          C * A * Phase2S82.pairWeight (M + 2) x y * (1 + smallRadius x y ^ (-criticalS d)) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : (1 : ℝ) ≤ criticalS d := by unfold criticalS; linarith
  have hsd : criticalS d < d := by unfold criticalS; linarith
  obtain ⟨chi, hchi⟩ := r26t8a_p10a_exists_cutoff d
  obtain ⟨C1, hC10, hC1⟩ := r26t8a_p11_Px_same d hd 2 0 a beta M (criticalS d) ha hbeta hM hsd hchi
  refine ⟨20 * C1, by positivity, fun rho hrho Q A hA hQ x y hxy => ?_⟩
  set C0 := critCoeff d a beta rho with hC0
  set μ := HRS.Whole.withDensityReal rho with hμ
  have hQ' : Conormal 4 1 M (criticalS d - 2) A (fun x y => Q y x) := r26t8a_f24_conormal_swap hchi hQ
  have P1 := hC1 rho hrho Q A hA hQ
  have P2 := hC1 rho hrho (fun x y => Q y x) A hA hQ'
  set G : Euc d → Euc d → ℝ := fun x y => oneJ C0 (fun u => Q u y) x - ∫ x', oneJ C0 (fun u => Q u y) x' ∂μ with hG
  set G' : Euc d → Euc d → ℝ := fun x y => oneJ C0 (fun u => Q y u) x - ∫ x', oneJ C0 (fun u => Q y u) x' ∂μ with hG'
  have hpair : pairJ C0 μ Q x y = G x y + G' y x := by
    simp only [pairJ, HRS.Whole.projMean, HRS.Whole.pair, hG, hG']
  have hxy' : y ≠ x := hxy.symm
  have b1 := r26t8a_p29_conormal_value P1 x y hxy
  have b2 := r26t8a_p29_conormal_value P2 y x hxy'
  set r := smallRadius x y with hr
  have hr0 : 0 < r := by
    rw [hr, smallRadius]; exact lt_min one_pos (norm_pos_iff.2 (sub_ne_zero.2 hxy))
  have hr1 : r ≤ 1 := min_le_left _ _
  have hyx : min 1 ‖y - x‖ = r := by rw [norm_sub_rev]; rfl
  have hxr : min 1 ‖x - y‖ = r := rfl
  have hpw : Phase2S82.pairWeight (M + 2) y x = Phase2S82.pairWeight (M + 2) x y := by
    unfold Phase2S82.pairWeight; ring
  have hlg := r26t8a_p29_logsq (criticalS d) hs1 r hr0 hr1
  have hpos := r26t8a_p29_pw_nonneg (d := d) (M + 2) x y
  simp only [hxr, hyx, hpw, sub_self, zero_add, Nat.cast_zero, neg_zero, Real.rpow_zero, one_mul] at b1 b2
  rw [hpair]
  refine (abs_add_le _ _).trans ?_
  have hC1A : 0 ≤ C1 * A := mul_nonneg hC10 hA
  have key : ∀ B : ℝ, B ≤ C1 * A * Phase2S82.pairWeight (M + 2) x y * (1 + (1 + |Real.log r|) ^ 2) →
      B ≤ 10 * (C1 * A * Phase2S82.pairWeight (M + 2) x y * (1 + r ^ (-criticalS d))) := by
    intro B hB
    refine hB.trans ?_
    have h0 : 0 ≤ C1 * A * Phase2S82.pairWeight (M + 2) x y := mul_nonneg hC1A hpos
    nlinarith
  have k1 := key _ b1
  have k2 := key _ b2
  have : 20 * C1 * A * Phase2S82.pairWeight (M + 2) x y * (1 + r ^ (-criticalS d)) =
      2 * (10 * (C1 * A * Phase2S82.pairWeight (M + 2) x y * (1 + r ^ (-criticalS d)))) := by ring
  rw [this]
  linarith

end HRS.MS.R26T8A

end
