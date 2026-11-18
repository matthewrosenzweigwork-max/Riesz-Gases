import HRS.MS.SA16Y3Pd1
import HRS.MS.SA16Y3Jt1

/-!
# S.A.16 (SA16Y3) Mem1: `P_μ φ ∈ sa16r_S d m p` and `‖J_m (P_μ φ)‖ ≤ C Λ ‖J_{m+2} φ‖` (packet P7 iso, step (a))

`sa16y3_P_jetbound`: `‖wJet m (P_μ φ)‖_p ≤ K Λ ‖wJet (m+2) φ‖_p` for `φ ∈ C_c^∞`, `μ ∈ C^∞`, `‖D^kμ‖ ≤ Λ` (`k ≤ m+2`).
`sa16y3_P_memS`: `P_μ φ ∈ sa16r_S d m p`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Mem1
variable {d : ℕ} {s p : ℝ} [Fact (2 ≤ p)]

theorem sa16y3_P_jetbound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {μ φ : Euc d → ℝ}, ContDiff ℝ ∞ μ → IsCcInfty φ → ∀ {Λ : ℝ}, 0 ≤ Λ →
      sa16z_Cb (m + 2) Λ μ →
      eLpNorm (wJet m (sa16z_P s μ φ)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (K * Λ) * eLpNorm (wJet (m + 2) φ) (ENNReal.ofReal p) volume := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hp : 1 < p := by linarith
  choose Kj hKj0 hKj using fun j : ℕ => sa16y3_pd_P_bound (s := s) hd hs0 hsd hθ1 hp j
  set cS : ℝ := ∑ k ∈ Finset.range (m + 2 + 1), ((d : ℝ) ^ k + 1) with hcS
  set cK : ℝ := ∑ j ∈ Finset.range (m + 1), (d : ℝ) ^ j * Kj j with hcK
  have hcS0 : 0 ≤ cS := Finset.sum_nonneg fun _ _ => by positivity
  have hcK0 : 0 ≤ cK := Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (hKj0 j)
  refine ⟨cK * cS, mul_nonneg hcK0 hcS0, fun {μ φ} hμ hφ {Λ} hΛ hCb => ?_⟩
  have hPs : ContDiff ℝ ∞ (sa16z_P s μ φ) := sa16z_P_smooth hs0 hsd hμ hφ
  have key : ∀ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d,
      eLpNorm (partialDeriv idx (sa16z_P s μ φ)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal ((d : ℝ) ^ j * (Kj j * Λ)) * sa16z_S p φ (m + 2) := by
    intro j hj
    have hjm : j ≤ m := by have := Finset.mem_range.1 hj; omega
    have h1 : ∀ idx : Fin j → Fin d, eLpNorm (partialDeriv idx (sa16z_P s μ φ)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (Kj j * Λ) * sa16z_S p φ (m + 2) := fun idx =>
      (hKj j hμ hφ hΛ (sa16z_Cb_mono (by omega) hCb) idx).trans (by gcongr; exact sa16z_S_mono φ (by omega))
    refine (Finset.sum_le_sum fun idx _ => h1 idx).trans (le_of_eq ?_)
    have e : ((d ^ j : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((d : ℝ) ^ j) := by
      rw [← ENNReal.ofReal_natCast]; push_cast; rfl
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, e,
      ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  calc eLpNorm (wJet m (sa16z_P s μ φ)) (ENNReal.ofReal p) volume
      ≤ ∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d,
          eLpNorm (partialDeriv idx (sa16z_P s μ φ)) (ENNReal.ofReal p) volume := sa16y3_jet_le_pd hPs m
    _ ≤ ∑ j ∈ Finset.range (m + 1), ENNReal.ofReal ((d : ℝ) ^ j * (Kj j * Λ)) * sa16z_S p φ (m + 2) :=
        Finset.sum_le_sum key
    _ = ENNReal.ofReal (cK * Λ) * sa16z_S p φ (m + 2) := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => by
          exact mul_nonneg (by positivity) (mul_nonneg (hKj0 j) hΛ)), hcK, Finset.sum_mul]
        congr 2
        refine Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ENNReal.ofReal (cK * Λ) * (ENNReal.ofReal cS * eLpNorm (wJet (m + 2) φ) (ENNReal.ofReal p) volume) := by
        gcongr
        exact sa16y3_S_le_jet hφ.1 (m + 2)
    _ = ENNReal.ofReal (cK * cS * Λ) * eLpNorm (wJet (m + 2) φ) (ENNReal.ofReal p) volume := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg hcK0 hΛ)]
        congr 2; ring

end Mem1

end HRS.Whole.AppendixA.Phase2SA16R
